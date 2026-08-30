#!/usr/bin/env python3
# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Reject Lean sources hidden from Git by ignore rules.

An ignored proof source can leave a stale ``.olean`` available locally while the
source itself is absent from the commit.  Builds may then appear to validate code
that a clean checkout cannot even inspect.  This gate derives authoritative roots
from Lake, walks them from the filesystem (not ``git ls-files``), checks native and
case-insensitive ignore semantics, and rejects project ``.olean`` files whose source
has disappeared.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import tomllib
from io import BytesIO
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = REPO_ROOT / "lakefile.toml"


def safe_git_environment() -> dict[str, str]:
    environment = os.environ.copy()
    authority_overrides = {
        "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_COMMON_DIR", "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE", "GIT_CONFIG_PARAMETERS", "GIT_QUARANTINE_PATH",
        "GIT_SHALLOW_FILE",
    }
    for key in list(environment):
        if key in authority_overrides or key.startswith("GIT_CONFIG_KEY_") \
                or key.startswith("GIT_CONFIG_VALUE_"):
            environment.pop(key, None)
    environment.pop("GIT_CONFIG_COUNT", None)
    environment["GIT_NO_REPLACE_OBJECTS"] = "1"
    return environment


def configured_modules() -> list[str]:
    data = tomllib.loads(LAKEFILE.read_text(encoding="utf-8"))
    modules: list[str] = []
    for library in data.get("lean_lib", []):
        modules.extend(library.get("roots", []))
    for executable in data.get("lean_exe", []):
        root = executable.get("root")
        if root:
            modules.append(root)
    if not modules:
        raise RuntimeError("lakefile.toml declares no Lean roots")
    return sorted(set(modules))


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def lean_sources(modules: list[str], repo_root: Path = REPO_ROOT) -> tuple[list[str], list[str]]:
    configured_paths = [module_path(module) for module in modules]
    errors = [
        f"configured root source absent: {path.as_posix()}"
        for path in configured_paths
        if not (repo_root / path).is_file()
    ]
    paths: set[str] = set()
    # Git/Lake metadata is not source. No dependency source exemption exists yet:
    # a future package policy must verify its manifest pin and checkout before any
    # Lean file under .lake can become authoritative.
    pruned = {".git", ".lake"}

    infrastructure_roots = [repo_root / ".git", repo_root / ".lake"]
    for infrastructure in infrastructure_roots:
        infrastructure_relative = infrastructure.relative_to(repo_root).as_posix()
        if infrastructure.is_symlink() or bool(
            getattr(infrastructure, "is_junction", lambda: False)()
        ):
            errors.append(
                f"repository infrastructure symlink/junction is forbidden: {infrastructure_relative}"
            )
            continue
        if not infrastructure.is_dir():
            continue
        for current, directories, files in os.walk(infrastructure, followlinks=False):
            current_path = Path(current)
            traversable: list[str] = []
            for directory in directories:
                child = current_path / directory
                relative = child.relative_to(repo_root).as_posix()
                is_junction = bool(getattr(child, "is_junction", lambda: False)())
                if child.is_symlink() or is_junction:
                    errors.append(
                        f"infrastructure symlink/junction directory is forbidden: {relative}"
                    )
                    continue
                if (child / ".git").exists():
                    errors.append(f"nested repository in infrastructure is forbidden: {relative}")
                    continue
                traversable.append(directory)
            directories[:] = traversable
            for filename in files:
                if filename.casefold().endswith(".lean"):
                    relative = (current_path / filename).relative_to(repo_root).as_posix()
                    errors.append(f"Lean source in non-source infrastructure is forbidden: {relative}")
    for current, directories, files in os.walk(repo_root, followlinks=False):
        current_path = Path(current)
        traversable: list[str] = []
        for directory in directories:
            child = current_path / directory
            relative = child.relative_to(repo_root).as_posix()
            if current_path == repo_root and directory in pruned:
                continue
            is_junction = bool(getattr(child, "is_junction", lambda: False)())
            if child.is_symlink() or is_junction:
                errors.append(f"importable symlink/junction directory is forbidden: {relative}")
                continue
            if (child / ".git").exists():
                errors.append(f"nested repository/worktree is forbidden: {relative}")
                continue
            traversable.append(directory)
        directories[:] = traversable
        for filename in files:
            if filename.casefold().endswith(".lean"):
                path = current_path / filename
                relative = path.relative_to(repo_root).as_posix()
                if not filename.endswith(".lean"):
                    errors.append(f"noncanonical Lean source extension casing: {relative}")
                    continue
                if path.is_symlink():
                    errors.append(f"symlinked Lean source is forbidden: {relative}")
                else:
                    paths.add(relative)
    return sorted(paths), sorted(set(errors))


def parse_index_stage_output(output: str) -> tuple[dict[str, str], dict[str, str], list[str]]:
    indexed: dict[str, str] = {}
    object_ids: dict[str, str] = {}
    errors: list[str] = []
    for record in output.split("\0"):
        if not record or "\t" not in record:
            continue
        metadata, path = record.split("\t", 1)
        fields = metadata.split(" ")
        if len(fields) != 3:
            errors.append(f"malformed Git index record for Lean source: {path}")
            continue
        mode, object_id, stage = fields
        if not path.casefold().endswith(".lean"):
            continue
        if not path.endswith(".lean"):
            errors.append(f"noncanonical indexed Lean extension casing: {path}")
        if path in indexed:
            errors.append(f"duplicate/unmerged Lean index entries are forbidden: {path}")
        if stage != "0":
            errors.append(f"non-stage-0 Lean index entry is forbidden: {path} (stage {stage})")
        if mode != "100644":
            errors.append(f"unsupported Lean index mode is forbidden: {path} ({mode})")
        indexed[path] = mode
        object_ids[path] = object_id
    return indexed, object_ids, errors


def committed_lean_sources(repo_root: Path = REPO_ROOT) -> tuple[dict[str, str], dict[str, str]]:
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "-z", "HEAD"],
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
        errors="replace",
        check=False,
        env=safe_git_environment(),
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "HEAD does not name a committed tree")
    modes: dict[str, str] = {}
    object_ids: dict[str, str] = {}
    for record in proc.stdout.split("\0"):
        if not record or "\t" not in record:
            continue
        metadata, path = record.split("\t", 1)
        fields = metadata.split(" ")
        if len(fields) != 3 or not path.casefold().endswith(".lean"):
            continue
        mode, object_type, object_id = fields
        if object_type != "blob":
            raise RuntimeError(f"committed Lean authority is not a blob: {path}")
        modes[path] = mode
        object_ids[path] = object_id
    return modes, object_ids


def batch_blob_contents(object_ids: list[str], repo_root: Path) -> list[bytes]:
    proc = subprocess.run(
        ["git", "cat-file", "--batch"],
        cwd=repo_root,
        input=("\n".join(object_ids) + "\n").encode("ascii"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        env=safe_git_environment(),
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.decode("utf-8", "replace").strip() or "git cat-file failed")
    stream = BytesIO(proc.stdout)
    blobs: list[bytes] = []
    for expected in object_ids:
        header = stream.readline().decode("ascii", "replace").strip().split(" ")
        if len(header) != 3 or header[0] != expected or header[1] != "blob":
            raise RuntimeError(f"unexpected git cat-file response for {expected}: {' '.join(header)}")
        size = int(header[2])
        blobs.append(stream.read(size))
        if stream.read(1) != b"\n":
            raise RuntimeError(f"malformed git cat-file framing for {expected}")
    return blobs


def normalized_lean_bytes(data: bytes, path: str) -> bytes:
    normalized = data.replace(b"\r\n", b"\n")
    if b"\r" in normalized:
        raise RuntimeError(f"unsupported lone-CR line ending in Lean source: {path}")
    return normalized


def indexed_lean_sources(repo_root: Path = REPO_ROOT) -> tuple[dict[str, str], list[str]]:
    proc = subprocess.run(
        ["git", "ls-files", "--stage", "-z"],
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
        errors="replace",
        check=False,
        env=safe_git_environment(),
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "git ls-files --stage failed")
    indexed, object_ids, errors = parse_index_stage_output(proc.stdout)
    committed_modes, committed_ids = committed_lean_sources(repo_root)
    for path in sorted(set(indexed) - set(committed_modes)):
        errors.append(f"Lean source is staged but absent from HEAD: {path}")
    for path in sorted(set(committed_modes) - set(indexed)):
        errors.append(f"committed Lean source is absent from the index: {path}")
    for path in sorted(set(indexed) & set(committed_modes)):
        if indexed[path] != committed_modes[path] or object_ids[path] != committed_ids[path]:
            errors.append(f"Lean index entry differs from committed HEAD authority: {path}")

    flags_proc = subprocess.run(
        ["git", "ls-files", "-v", "-z"],
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
        errors="replace",
        check=False,
        env=safe_git_environment(),
    )
    if flags_proc.returncode != 0:
        raise RuntimeError(flags_proc.stderr.strip() or "git ls-files -v failed")
    for record in flags_proc.stdout.split("\0"):
        if len(record) < 3 or record[1] != " ":
            continue
        tag, path = record[0], record[2:]
        if path.casefold().endswith(".lean") and tag != "H":
            errors.append(f"special Lean index flag is forbidden: {path} ({tag})")

    diff_proc = subprocess.run(
        ["git", "diff-files", "--name-only", "-z", "--", "*.lean"],
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
        errors="replace",
        check=False,
        env=safe_git_environment(),
    )
    if diff_proc.returncode != 0:
        raise RuntimeError(diff_proc.stderr.strip() or "git diff-files failed")
    for path in diff_proc.stdout.split("\0"):
        if path:
            errors.append(f"Lean worktree content differs from its stage-0 index blob: {path}")

    committed_paths = sorted(committed_ids)
    blobs = batch_blob_contents([committed_ids[path] for path in committed_paths], repo_root)
    for path, committed_blob in zip(committed_paths, blobs):
        worktree_path = repo_root / path
        if not worktree_path.is_file():
            continue  # The source/index census reports the missing path above.
        try:
            worktree_blob = worktree_path.read_bytes()
            if normalized_lean_bytes(worktree_blob, path) != normalized_lean_bytes(committed_blob, path):
                errors.append(f"raw Lean worktree bytes differ from committed HEAD authority: {path}")
        except OSError as error:
            errors.append(f"cannot read committed Lean worktree source: {path}: {error}")
    return indexed, sorted(set(errors))


def ignored_sources(
    paths: list[str], *, case_insensitive: bool, repo_root: Path = REPO_ROOT
) -> list[str]:
    if not paths:
        return []
    command = ["git"]
    command.extend(["-c", f"core.ignoreCase={'true' if case_insensitive else 'false'}"])
    command.extend(["check-ignore", "--no-index", "-z", "--stdin"])
    proc = subprocess.run(
        command,
        cwd=repo_root,
        input="\0".join(paths) + "\0",
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        encoding="utf-8",
        errors="replace",
        check=False,
        env=safe_git_environment(),
    )
    # git check-ignore returns 0 when it found a match and 1 when it found none.
    if proc.returncode not in (0, 1):
        print(proc.stderr.strip() or "git check-ignore failed", file=sys.stderr)
        raise SystemExit(2)
    return sorted(item for item in proc.stdout.split("\0") if item)


def stale_project_oleans(checked_sources: set[str], repo_root: Path = REPO_ROOT) -> list[str]:
    olean_root = repo_root / ".lake" / "build" / "lib" / "lean"
    if not olean_root.is_dir():
        return []
    stale: list[str] = []
    for olean in olean_root.rglob("*.olean"):
        relative = olean.relative_to(olean_root).with_suffix(".lean")
        if relative.as_posix() not in checked_sources:
            stale.append(olean.relative_to(repo_root).as_posix())
    return sorted(stale)


def self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="gasm-ignore-gate-") as temp:
        repo = Path(temp)
        git_env = safe_git_environment()
        subprocess.run(["git", "init", "--quiet"], cwd=repo, check=True, env=git_env)
        (repo / ".gitignore").write_text("gasm.lean\nspike*\n", encoding="utf-8")
        (repo / "Gasm.lean").write_text("import Gasm.Core.Visible\n", encoding="utf-8")
        (repo / "Gasm" / "Core").mkdir(parents=True)
        (repo / "Gasm" / "Core" / "Visible.lean").write_text("def visible := True\n", encoding="utf-8")
        (repo / "Spikes").mkdir()
        (repo / "Spikes" / "Proof.lean").write_text("def proof := True\n", encoding="utf-8")

        sources, errors = lean_sources(["Gasm", "Spikes.Proof"], repo)
        if errors or "Gasm.lean" not in sources or "Spikes/Proof.lean" not in sources:
            raise RuntimeError("root/module source enumeration negative control failed")
        ignored = ignored_sources(sources, case_insensitive=True, repo_root=repo)
        if "Gasm.lean" not in ignored or "Spikes/Proof.lean" not in ignored:
            raise RuntimeError("case-insensitive broad-ignore negative control failed")

        subprocess.run(
            ["git", "add", "-f", "Gasm.lean", "Gasm/Core/Visible.lean", "Spikes/Proof.lean"],
            cwd=repo,
            check=True,
            stdout=subprocess.DEVNULL,
            env=git_env,
        )
        subprocess.run(["git", "add", ".gitignore"], cwd=repo, check=True, env=git_env)
        subprocess.run(["git", "config", "user.name", "Gate Self Test"], cwd=repo,
                       check=True, env=git_env)
        subprocess.run(["git", "config", "user.email", "gate-self-test@example.invalid"],
                       cwd=repo, check=True, env=git_env)
        subprocess.run(["git", "commit", "--quiet", "-m", "fixture"], cwd=repo,
                       check=True, env=git_env)

        original_id = subprocess.run(
            ["git", "rev-parse", "HEAD:Gasm.lean"], cwd=repo, check=True, env=git_env,
            stdout=subprocess.PIPE, text=True, encoding="utf-8",
        ).stdout.strip()
        original_blob = batch_blob_contents([original_id], repo)[0]
        replacement_id = subprocess.run(
            ["git", "hash-object", "-w", "--stdin"], cwd=repo, check=True, env=git_env,
            input="def replacementForgery := True\n", stdout=subprocess.PIPE,
            text=True, encoding="utf-8",
        ).stdout.strip()
        subprocess.run(["git", "replace", original_id, replacement_id], cwd=repo,
                       check=True, env=git_env)
        if batch_blob_contents([original_id], repo)[0] != original_blob:
            raise RuntimeError("Git replacement-object isolation negative control failed")
        subprocess.run(["git", "replace", "-d", original_id], cwd=repo, check=True,
                       env=git_env, stdout=subprocess.DEVNULL)
        indexed, index_errors = indexed_lean_sources(repo)
        if index_errors or set(sources) - set(indexed):
            raise RuntimeError("outer-index source identity positive control failed")
        untracked = repo / "Spikes" / "Untracked.lean"
        untracked.write_text("def untracked := True\n", encoding="utf-8")
        untracked_sources, _ = lean_sources(["Gasm", "Spikes.Proof"], repo)
        if "Spikes/Untracked.lean" not in set(untracked_sources) - set(indexed):
            raise RuntimeError("untracked Lean source negative control failed")

        subprocess.run(["git", "add", "-N", "-f", "Spikes/Untracked.lean"], cwd=repo,
                       check=True, env=git_env)
        _, intent_errors = indexed_lean_sources(repo)
        if not any("Spikes/Untracked.lean" in error for error in intent_errors):
            raise RuntimeError("intent-to-add Lean source negative control failed")
        subprocess.run(["git", "reset", "--", "Spikes/Untracked.lean"], cwd=repo, check=True,
                       stdout=subprocess.DEVNULL, env=git_env)

        subprocess.run(["git", "update-index", "--assume-unchanged", "Gasm.lean"],
                       cwd=repo, check=True, env=git_env)
        _, assume_errors = indexed_lean_sources(repo)
        if not any("special Lean index flag" in error for error in assume_errors):
            raise RuntimeError("assume-unchanged Lean source negative control failed")
        subprocess.run(["git", "update-index", "--no-assume-unchanged", "Gasm.lean"],
                       cwd=repo, check=True, env=git_env)

        subprocess.run(["git", "update-index", "--skip-worktree", "Gasm.lean"],
                       cwd=repo, check=True, env=git_env)
        _, skip_errors = indexed_lean_sources(repo)
        if not any("special Lean index flag" in error for error in skip_errors):
            raise RuntimeError("skip-worktree Lean source negative control failed")
        subprocess.run(["git", "update-index", "--no-skip-worktree", "Gasm.lean"],
                       cwd=repo, check=True, env=git_env)

        with (repo / "Gasm.lean").open("a", encoding="utf-8") as source:
            source.write("\ndef stagedMutation := True\n")
        subprocess.run(["git", "add", "-f", "Gasm.lean"], cwd=repo, check=True,
                       env=git_env)
        _, staged_errors = indexed_lean_sources(repo)
        if not any("differs from committed HEAD authority" in error for error in staged_errors):
            raise RuntimeError("staged Lean mutation negative control failed")
        subprocess.run(
            ["git", "restore", "--source=HEAD", "--staged", "--worktree", "Gasm.lean"],
            cwd=repo, check=True, env=git_env,
        )

        conflict_hash = "1" * 40
        _, _, unmerged_errors = parse_index_stage_output(
            f"100644 {conflict_hash} 1\tGasm/Core/Conflict.lean\0"
            f"100644 {conflict_hash} 2\tGasm/Core/Conflict.lean\0"
        )
        if not any("non-stage-0" in error for error in unmerged_errors):
            raise RuntimeError("unmerged Lean index negative control failed")

        (repo / ".gitignore").write_text(
            "gasm.lean\nSpikes/*\n!spikes/Proof.lean\n.cache/\n", encoding="utf-8"
        )
        sensitive = ignored_sources(sources, case_insensitive=False, repo_root=repo)
        insensitive = ignored_sources(sources, case_insensitive=True, repo_root=repo)
        if "Spikes/Proof.lean" not in sensitive or "Spikes/Proof.lean" in insensitive:
            raise RuntimeError("explicit true/false ignore negation control failed")

        stale = repo / ".lake" / "build" / "lib" / "lean" / "Gasm" / "Ghost.olean"
        stale.parent.mkdir(parents=True)
        stale.write_bytes(b"stale")
        if stale_project_oleans(set(sources), repo) != [
            ".lake/build/lib/lean/Gasm/Ghost.olean"
        ]:
            raise RuntimeError("source-less stale .olean negative control failed")

        package_source = repo / ".lake" / "packages" / "Injected" / "Proof.lean"
        package_source.parent.mkdir(parents=True)
        package_source.write_text("def injected := True\n", encoding="utf-8")
        _, package_errors = lean_sources(["Gasm", "Spikes.Proof"], repo)
        if (
            "Lean source in non-source infrastructure is forbidden: "
            ".lake/packages/Injected/Proof.lean"
        ) not in package_errors:
            raise RuntimeError("unverified Lake package source negative control failed")

        nested_lake = repo / "Gasm" / ".lake" / "Ghost.lean"
        nested_lake.parent.mkdir(parents=True)
        nested_lake.write_text("def ghost := True\n", encoding="utf-8")
        nested_sources, _ = lean_sources(["Gasm", "Spikes.Proof"], repo)
        if "Gasm/.lake/Ghost.lean" not in nested_sources:
            raise RuntimeError("nested .lake namespace enumeration negative control failed")

        external = repo.parent / f"{repo.name}-external-infrastructure"
        external.mkdir()
        (external / "Proof.lean").write_text("def external := True\n", encoding="utf-8")
        link = repo / ".lake" / "InjectedLink"
        try:
            os.symlink(external, link, target_is_directory=True)
        except OSError:
            pass  # Windows may deny unprivileged symlink creation; Ubuntu CI exercises this control.
        else:
            _, link_errors = lean_sources(["Gasm", "Spikes.Proof"], repo)
            if (
                "infrastructure symlink/junction directory is forbidden: .lake/InjectedLink"
                not in link_errors
            ):
                raise RuntimeError("infrastructure symlink negative control failed")
        finally:
            if link.is_symlink():
                link.unlink()
            for child in external.iterdir():
                child.unlink()
            external.rmdir()

        nested = repo / "Vendor"
        (nested / ".git").mkdir(parents=True)
        (nested / "Ghost.lean").write_text("def ghost := True\n", encoding="utf-8")
        _, boundary_errors = lean_sources(["Gasm", "Spikes.Proof"], repo)
        if "nested repository/worktree is forbidden: Vendor" not in boundary_errors:
            raise RuntimeError("nested importable repository negative control failed")

        cache_source = repo / ".cache" / "Ghost.lean"
        cache_source.parent.mkdir()
        cache_source.write_text("def ghost := True\n", encoding="utf-8")
        dot_sources, _ = lean_sources(["Gasm", "Spikes.Proof"], repo)
        if ".cache/Ghost.lean" not in dot_sources:
            raise RuntimeError("escaped dot-namespace source enumeration control failed")
        if ".cache/Ghost.lean" not in ignored_sources(
            dot_sources, case_insensitive=False, repo_root=repo
        ):
            raise RuntimeError("escaped dot-namespace ignored-source control failed")


def main() -> int:
    try:
        self_test()
        modules = configured_modules()
        sources, source_errors = lean_sources(modules)
        indexed, index_errors = indexed_lean_sources()
    except (OSError, RuntimeError, tomllib.TOMLDecodeError) as error:
        print(f"FAIL: cannot derive authoritative Lean roots: {error}")
        return 2
    source_errors.extend(index_errors)
    source_set = set(sources)
    indexed_set = set(indexed)
    for path in sorted(source_set - indexed_set):
        source_errors.append(f"Lean source is not tracked in the outer Git index: {path}")
    for path in sorted(indexed_set - source_set):
        source_errors.append(f"indexed Lean source is absent or outside the checked closure: {path}")
    if source_errors:
        print("FAIL: authoritative Lean source closure is incomplete or crosses a forbidden boundary:")
        for error in source_errors:
            print(f"  {error}")
        return 1

    ignored = sorted(set(
        ignored_sources(sources, case_insensitive=False)
        + ignored_sources(sources, case_insensitive=True)
    ))
    if ignored:
        print("FAIL: Lean proof sources are hidden by Git ignore rules:")
        for path in ignored:
            print(f"  {path}")
        print("Remove the matching ignore rule; proof sources must be reviewable in a clean checkout.")
        return 1

    stale = stale_project_oleans(source_set)
    if stale:
        print("FAIL: compiled project modules have no corresponding Lean source:")
        for path in stale:
            print(f"  {path}")
        print("Remove stale build products and restore/track every authoritative proof source.")
        return 1

    print("PASS: authoritative Lean roots are present, non-ignored under native and "
          "case-insensitive matching, and have no source-less stale .olean")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

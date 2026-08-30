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

"""Explicit launcher for the full-repository Lean declaration-coverage gate."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import sys

from lean_process_lease import inherited_lease_environment, lean_process_lease


REPO_ROOT = Path(__file__).resolve().parent.parent
OPT_IN_ENV = "GASM_RUN_FULL_REFS_COVERAGE"
TRUE_VALUES = {"1", "true", "yes"}
AUTHORITY_ENV = "GASM_FULL_REFS_BUILD_AUTHORITY"
AUTHORITY_DIR = REPO_ROOT / ".lake" / "build" / "full_refs_authority"
OLEAN_ROOT = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
AUTHORITY_INPUTS = [
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "scripts/run_full_refs_coverage.py",
    "Tools/CheckRefsCoverage.lean",
    "Tools/GateSubprocess.lean",
]


def fnv1a64(path: Path) -> str:
    value = 14695981039346656037
    for byte in path.read_bytes():
        value ^= byte
        value = (value * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return str(value)


def file_fingerprint(path: Path) -> dict[str, int | str]:
    stat = path.stat()
    return {
        "size": stat.st_size,
        "mtimeSec": stat.st_mtime_ns // 1_000_000_000,
        "mtimeNsec": stat.st_mtime_ns % 1_000_000_000,
    }


def content_entry(path: Path) -> dict[str, object]:
    return {
        "path": path.relative_to(REPO_ROOT).as_posix(),
        "hash": fnv1a64(path),
        "stat": file_fingerprint(path),
    }


def authority_sources() -> list[Path]:
    suffix = ".exe" if os.name == "nt" else ""
    gate_executable = REPO_ROOT / ".lake" / "build" / "bin" / f"check_refs_coverage_full{suffix}"
    output = subprocess.check_output(
        [str(gate_executable), "--list-authority-modules"], cwd=REPO_ROOT, text=True
    ).strip()
    marker = "GASM_AUTHORITY_MODULES "
    if not output.startswith(marker):
        raise ValueError("declaration-coverage executable returned no authority module census")
    paths = json.loads(output[len(marker) :])
    if not isinstance(paths, list) or not all(isinstance(path, str) for path in paths):
        raise ValueError("declaration-coverage authority module census is malformed")
    return [REPO_ROOT / path for path in paths]


def gate_executable_path() -> Path:
    suffix = ".exe" if os.name == "nt" else ""
    return REPO_ROOT / ".lake" / "build" / "bin" / f"check_refs_coverage_full{suffix}"


def built_artifact(path: Path) -> dict[str, object]:
    hash_path = Path(f"{path}.hash")
    return {
        "path": path.resolve().as_posix(),
        "lakeHash": hash_path.read_text(encoding="utf-8").strip(),
        "stat": file_fingerprint(path),
    }


def write_build_authority(authority_file: Path, nonce: str) -> None:
    entries = []
    for source in authority_sources():
        if source.suffix != ".lean":
            continue
        relative_source = source.relative_to(REPO_ROOT)
        olean = OLEAN_ROOT / relative_source.with_suffix(".olean")
        olean_hash = Path(f"{olean}.hash")
        if not olean.is_file() or not olean_hash.is_file():
            continue
        entries.append(
            {
                "path": relative_source.as_posix(),
                "sourceHash": fnv1a64(source),
                "source": file_fingerprint(source),
                "oleanPath": olean.relative_to(REPO_ROOT).as_posix(),
                "oleanHash": olean_hash.read_text(encoding="utf-8").strip(),
                "olean": file_fingerprint(olean),
            }
        )
    lake = shutil.which("lake") or "lake"
    lean_header = subprocess.check_output(
        [lake, "env", "lean", "--version"], cwd=REPO_ROOT, text=True
    ).strip()
    version_match = re.search(r"\bversion\s+([^, )]+)", lean_header)
    if version_match is None:
        raise ValueError(f"could not parse Lean version from: {lean_header}")
    lean_version = version_match.group(1)
    inputs = [content_entry(REPO_ROOT / relative) for relative in AUTHORITY_INPUTS]
    authority_file.write_text(
        json.dumps(
            {
                "version": 1,
                "nonce": nonce,
                "leanVersion": lean_version,
                "gate": built_artifact(gate_executable_path()),
                "inputs": inputs,
                "entries": entries,
            },
            separators=(",", ":"),
        ),
        encoding="utf-8",
    )


def opted_in(flag: bool) -> bool:
    return flag or os.environ.get(OPT_IN_ENV, "").strip().lower() in TRUE_VALUES


def lake_commands(forwarded: list[str]) -> list[list[str]]:
    lake = shutil.which("lake") or "lake"
    return [
        [lake, "build"],
        [lake, "exe", "check_refs_coverage_full", "--", *forwarded],
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run the full-repository compiled declaration-coverage gate.",
        epilog=(
            "Arguments after `--` are forwarded to the underlying Lean executable. "
            f"CI may set {OPT_IN_ENV}=1 instead of passing --full-repository."
        ),
    )
    parser.add_argument(
        "--full-repository",
        action="store_true",
        help="acknowledge and run the complete Gasm/Stdlib/Spikes gate",
    )
    parser.add_argument(
        "--print-command",
        action="store_true",
        help="print the opted-in Lake command without executing it",
    )
    parser.add_argument("forwarded", nargs=argparse.REMAINDER, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)

    forwarded = args.forwarded
    if forwarded[:1] == ["--"]:
        forwarded = forwarded[1:]

    if not opted_in(args.full_repository):
        print(
            "REFUSED: declaration coverage is a FULL-REPOSITORY gate, not an edit-local check.",
            file=sys.stderr,
        )
        print(
            "It can schedule hundreds of Lean modules. One partially warm incident scheduled "
            "616 targets, ran for more than 23 minutes before cancellation, and was observed "
            "near 28 GiB aggregate memory (including one Lean process near 17 GiB); actual "
            "cost varies with the tree, cache, machine, and concurrency.",
            file=sys.stderr,
        )
        print(
            "For fast local feedback, build the edited modules directly. Examples:\n"
            "  python scripts/build_x86_family.py Add\n"
            "  lake exe test_graphics_foundation\n"
            "These focused checks do not replace the final full-repository gate.",
            file=sys.stderr,
        )
        print(
            "To run the authoritative gate intentionally:\n"
            "  python scripts/run_full_refs_coverage.py --full-repository\n"
            f"or set {OPT_IN_ENV}=1 for noninteractive CI.",
            file=sys.stderr,
        )
        return 2

    commands = lake_commands(forwarded)
    if args.print_command:
        for command in commands:
            print(subprocess.list2cmdline(command))
        return 0
    try:
        with lean_process_lease():
            environment = inherited_lease_environment()
            build_result = subprocess.run(
                commands[0], cwd=REPO_ROOT, check=False, env=environment
            )
            if build_result.returncode != 0:
                return build_result.returncode

            nonce = secrets.token_urlsafe(32)
            AUTHORITY_DIR.mkdir(parents=True, exist_ok=True)
            authority_file = AUTHORITY_DIR / f"{nonce}.token"
            write_build_authority(authority_file, nonce)
            gate_environment = environment.copy()
            gate_environment[AUTHORITY_ENV] = nonce
            try:
                return subprocess.run(
                    commands[1], cwd=REPO_ROOT, check=False, env=gate_environment
                ).returncode
            finally:
                authority_file.unlink(missing_ok=True)
    except (OSError, TimeoutError, ValueError) as error:
        print(f"full declaration-coverage lease failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

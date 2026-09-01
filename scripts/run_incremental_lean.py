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

"""Elaborate one edited Lean source through a sound, reusable incremental snapshot.

This is an edit-local frontend.  It invokes Lean's own experimental incremental serialization;
it does not replace Lake dependency builds or repository validation gates.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import threading
import time
from typing import Callable, Iterator
import uuid

if os.name == "nt":
    import msvcrt
else:
    import fcntl


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CACHE_DIR = REPO_ROOT / ".lake" / "build" / "incremental-lean-snapshots"
CACHE_PROTOCOL = b"gasm-incremental-lean-full-v3\0"
IMPORT_RE = re.compile(rb"(?m)^[ \t]*(?:(?:public|meta)[ \t]+)*import(?:[ \t]|$)")
VALUE_ARGUMENTS = {
    "-M": "memory limit",
    "--memory": "memory limit",
    "-T": "allocation timeout",
    "--timeout": "allocation timeout",
    "-j": "thread count",
    "--threads": "thread count",
    "-s": "thread stack size",
    "--tstack": "thread stack size",
    "-E": "error-kind selection",
    "--error": "error-kind selection",
}
FLAG_ARGUMENTS = {
    "-q",
    "--quiet",
    "--json",
    "--profile",
    "--stats",
}
MUTABLE_OR_CONTROL_ARGUMENTS = (
    "--setup",
    "--plugin",
    "--load-dynlib",
    "-R",
    "--root",
    "-D",
    "-o",
    "--o",
    "-i",
    "--i",
    "-c",
    "--c",
    "-b",
    "--bc",
    "--stdin",
    "--run",
    "--server",
    "--worker",
    "--deps",
    "--src-deps",
    "--incr-load",
    "--incr-save",
    "--incr-header-save",
)
LOCK_TIMEOUT_SECONDS = 120.0
_THREAD_LOCKS_GUARD = threading.Lock()
_THREAD_LOCKS: dict[Path, threading.Lock] = {}


class PreparationError(RuntimeError):
    """The snapshot fingerprint could not be constructed safely."""


def command_text(command: list[str]) -> str:
    if os.name == "nt":
        return subprocess.list2cmdline(command)
    return shlex.join(command)


def source_import_prefix(source_bytes: bytes) -> bytes:
    """Return the exact source prefix through the final import command line.

    The prefix deliberately includes comments and whitespace before imports.  Invalidating for a
    harmless header edit is preferable to reusing a snapshot across a header distinction that a
    textual approximation failed to model.
    """

    matches = list(IMPORT_RE.finditer(source_bytes))
    if not matches:
        return b""
    line_end = source_bytes.find(b"\n", matches[-1].end())
    return source_bytes if line_end < 0 else source_bytes[: line_end + 1]


def hash_file(hasher: "hashlib._Hash", path: Path) -> None:
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            hasher.update(chunk)


def run_capture(command: list[str]) -> str:
    result = subprocess.run(
        command,
        cwd=REPO_ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or f"exit {result.returncode}"
        raise PreparationError(f"{command_text(command)} failed: {detail}")
    return result.stdout


def dependency_paths(source_argument: str, lean_arguments: list[str]) -> tuple[str, list[Path]]:
    output = run_capture(
        ["lake", "env", "lean", *lean_arguments, "--deps", source_argument]
    )
    dependencies: list[Path] = []
    seen: set[Path] = set()
    for raw_line in output.splitlines():
        if not raw_line.strip():
            continue
        path = Path(raw_line.strip())
        if not path.is_absolute():
            path = REPO_ROOT / path
        path = path.resolve()
        if path in seen:
            continue
        if not path.is_file():
            raise PreparationError(
                f"Lean dependency is missing: {path}\n"
                "Build the edited module's focused Lake target once, then retry."
            )
        seen.add(path)
        dependencies.append(path)
    return output, dependencies


def snapshot_fingerprint(
    source: Path,
    source_argument: str,
    lean_arguments: list[str],
) -> str:
    source_bytes = source.read_bytes()
    dependency_output, dependencies = dependency_paths(source_argument, lean_arguments)
    version = run_capture(["lake", "env", "lean", "--version"])

    hasher = hashlib.sha256()
    hasher.update(CACHE_PROTOCOL)
    hasher.update(str(source.resolve()).encode("utf-8"))
    hasher.update(b"\0toolchain\0")
    hasher.update(version.encode("utf-8"))
    hasher.update(b"\0arguments\0")
    for argument in lean_arguments:
        hasher.update(argument.encode("utf-8"))
        hasher.update(b"\0")
    hasher.update(b"header\0")
    hasher.update(source_import_prefix(source_bytes))
    hasher.update(b"\0dependency-list\0")
    hasher.update(dependency_output.encode("utf-8"))
    for dependency in dependencies:
        hasher.update(b"\0dependency\0")
        hasher.update(str(dependency).encode("utf-8"))
        hasher.update(b"\0")
        hash_file(hasher, dependency)
    return hasher.hexdigest()


def validate_lean_arguments(arguments: list[str]) -> None:
    """Accept only resource and diagnostic options with no mutable file-backed input."""

    index = 0
    while index < len(arguments):
        argument = arguments[index]
        if argument in FLAG_ARGUMENTS:
            index += 1
            continue
        if argument in VALUE_ARGUMENTS:
            if index + 1 >= len(arguments) or arguments[index + 1].startswith("-"):
                raise PreparationError(
                    f"argument {argument!r} requires its {VALUE_ARGUMENTS[argument]} value"
                )
            index += 2
            continue
        matched_equals = False
        for option, description in VALUE_ARGUMENTS.items():
            if option.startswith("--") and argument.startswith(f"{option}="):
                if not argument.partition("=")[2]:
                    raise PreparationError(
                        f"argument {argument!r} requires its {description} value"
                    )
                matched_equals = True
                break
        if matched_equals:
            index += 1
            continue
        if any(
            argument == option or argument.startswith(f"{option}=")
            for option in MUTABLE_OR_CONTROL_ARGUMENTS
        ):
            raise PreparationError(
                f"argument {argument!r} is mutable, semantic, or launcher-owned; "
                "the incremental launcher accepts only resource and diagnostic options"
            )
        raise PreparationError(
            f"unsupported Lean argument {argument!r}; the incremental launcher accepts only "
            "resource and diagnostic options"
        )


def _thread_lock_for(path: Path) -> threading.Lock:
    with _THREAD_LOCKS_GUARD:
        return _THREAD_LOCKS.setdefault(path, threading.Lock())


@contextmanager
def cache_lock(path: Path, timeout: float = LOCK_TIMEOUT_SECONDS) -> Iterator[None]:
    """Hold one per-key lock across selection, Lean access, and snapshot publication."""

    path.parent.mkdir(parents=True, exist_ok=True)
    local_lock = _thread_lock_for(path)
    started = time.monotonic()
    if not local_lock.acquire(timeout=timeout):
        raise PreparationError(f"timed out waiting for incremental cache lock: {path}")
    stream = None
    locked = False
    try:
        stream = path.open("a+b")
        stream.seek(0, os.SEEK_END)
        if stream.tell() == 0:
            stream.write(b"\0")
            stream.flush()
        while not locked:
            try:
                stream.seek(0)
                if os.name == "nt":
                    msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                locked = True
            except OSError as error:
                if time.monotonic() - started >= timeout:
                    raise PreparationError(
                        f"timed out waiting for incremental cache lock: {path}"
                    ) from error
                time.sleep(0.05)
        yield
    finally:
        if stream is not None:
            if locked:
                stream.seek(0)
                if os.name == "nt":
                    msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(stream.fileno(), fcntl.LOCK_UN)
            stream.close()
        local_lock.release()


def dependency_companion(snapshot: Path) -> Path:
    """Return Lean's required dependency companion for an incremental snapshot."""

    return Path(f"{snapshot}.deps")


def manifest_companion(snapshot: Path) -> Path:
    """Return the atomic commit marker authenticating both snapshot files."""

    return Path(f"{snapshot}.json")


def file_digest(path: Path) -> str:
    hasher = hashlib.sha256()
    hash_file(hasher, path)
    return hasher.hexdigest()


def pair_manifest(snapshot: Path, dependencies: Path) -> dict[str, object]:
    return {
        "protocol": CACHE_PROTOCOL.decode("ascii", errors="strict").rstrip("\0"),
        "snapshot_size": snapshot.stat().st_size,
        "snapshot_sha256": file_digest(snapshot),
        "dependencies_size": dependencies.stat().st_size,
        "dependencies_sha256": file_digest(dependencies),
    }


def write_manifest(path: Path, manifest: dict[str, object]) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    try:
        temporary.write_text(json.dumps(manifest, sort_keys=True) + "\n", encoding="utf-8")
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def validate_snapshot_pair(snapshot: Path) -> bool:
    """Return false for absence and fail closed for a partial, mixed, or damaged pair."""

    dependencies = dependency_companion(snapshot)
    manifest_path = manifest_companion(snapshot)
    present = [path.is_file() for path in (snapshot, dependencies, manifest_path)]
    if not any(present):
        return False
    if not all(present):
        raise PreparationError(
            f"incremental cache is incomplete: {snapshot}; rerun with --refresh"
        )
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        expected = pair_manifest(snapshot, dependencies)
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as error:
        raise PreparationError(
            f"incremental cache metadata is unreadable: {manifest_path}; rerun with --refresh"
        ) from error
    if manifest != expected:
        raise PreparationError(
            f"incremental cache pair failed integrity validation: {snapshot}; "
            "rerun with --refresh"
        )
    return True


def publish_snapshot_pair(
    temporary: Path,
    temporary_dependencies: Path,
    snapshot: Path,
    between_replaces: Callable[[], None] | None = None,
) -> None:
    """Commit one pair; the manifest is replaced last and authenticates both files."""

    manifest = pair_manifest(temporary, temporary_dependencies)
    os.replace(temporary_dependencies, dependency_companion(snapshot))
    if between_replaces is not None:
        between_replaces()
    os.replace(temporary, snapshot)
    write_manifest(manifest_companion(snapshot), manifest)


def source_cache_key(source: Path) -> str:
    return hashlib.sha256(str(source.resolve()).encode("utf-8")).hexdigest()[:16]


def prune_obsolete_snapshots(cache_dir: Path, source_key: str, keep: Path) -> None:
    """Keep one committed fingerprint per source so large serialized environments do not pile up."""

    for obsolete in cache_dir.glob(f"{source_key}-*.snapshot"):
        if obsolete == keep:
            continue
        try:
            obsolete.unlink(missing_ok=True)
            dependency_companion(obsolete).unlink(missing_ok=True)
            manifest_companion(obsolete).unlink(missing_ok=True)
        except OSError:
            # A concurrent reader may hold the old snapshot on Windows.  It is still correctly
            # keyed and can be removed by a later refresh or ordinary `.lake` cleanup.
            pass


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true", help="regenerate the snapshot")
    parser.add_argument("--print-command", action="store_true", help="render without elaborating")
    parser.add_argument(
        "--cache-dir", type=Path, default=DEFAULT_CACHE_DIR, help=argparse.SUPPRESS
    )
    parser.add_argument("source", type=Path, help="edited .lean source file")
    parser.add_argument("lean_arguments", nargs=argparse.REMAINDER, help="arguments after --")
    args = parser.parse_args(argv)

    lean_arguments = args.lean_arguments[1:] if args.lean_arguments[:1] == ["--"] else args.lean_arguments
    try:
        validate_lean_arguments(lean_arguments)
        source = args.source if args.source.is_absolute() else REPO_ROOT / args.source
        source = source.resolve()
        if source.suffix != ".lean" or not source.is_file():
            raise PreparationError(f"Lean source does not exist: {source}")
        try:
            source_argument = str(source.relative_to(REPO_ROOT))
        except ValueError:
            source_argument = str(source)
        cache_dir = args.cache_dir.resolve()
        cache_dir.mkdir(parents=True, exist_ok=True)
        source_key = source_cache_key(source)

        # Compute the complete fingerprint only after taking the source lock. A waiter therefore
        # cannot select a pair using imports or dependencies observed before lock acquisition.
        # One source-level lock also makes pruning obsolete fingerprints safe when another run uses
        # different resource or diagnostic arguments.
        lock_path = cache_dir / f".{source_key}.lock"
        with cache_lock(lock_path):
            fingerprint = snapshot_fingerprint(source, source_argument, lean_arguments)
            snapshot = cache_dir / f"{source_key}-{fingerprint}.snapshot"
            pair_exists = validate_snapshot_pair(snapshot) if not args.refresh else False
            if pair_exists:
                command = [
                    "lake", "env", "lean", *lean_arguments,
                    f"--incr-load={snapshot}", source_argument,
                ]
                mode = "load"
                temporary = None
                temporary_dependencies = None
            else:
                temporary = cache_dir / (
                    f".{fingerprint}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
                )
                temporary_dependencies = dependency_companion(temporary)
                command = [
                    "lake", "env", "lean", *lean_arguments,
                    f"--incr-save={temporary}", source_argument,
                ]
                mode = "refresh" if args.refresh else "save"

            print(f"INCREMENTAL_LEAN mode={mode} cache={snapshot}", file=sys.stderr)
            if args.print_command:
                print(command_text(command))
                return 0

            try:
                result = subprocess.run(command, cwd=REPO_ROOT, check=False)
                if (
                    temporary is not None
                    and temporary_dependencies is not None
                    and temporary.is_file()
                    and temporary.stat().st_size > 0
                    and temporary_dependencies.is_file()
                    and temporary_dependencies.stat().st_size > 0
                ):
                    # Body edits deliberately retain the key: Lean's loader reconciles them
                    # against the serialized command stream. Imports and dependencies do not.
                    after = snapshot_fingerprint(source, source_argument, lean_arguments)
                    if after == fingerprint:
                        publish_snapshot_pair(temporary, temporary_dependencies, snapshot)
                        prune_obsolete_snapshots(cache_dir, source_key, snapshot)
                    else:
                        print(
                            "incremental Lean cache not published: inputs changed during run",
                            file=sys.stderr,
                        )
                return result.returncode
            finally:
                if temporary is not None:
                    temporary.unlink(missing_ok=True)
                if temporary_dependencies is not None:
                    temporary_dependencies.unlink(missing_ok=True)
    except KeyboardInterrupt:
        return 130
    except (OSError, PreparationError) as error:
        print(f"incremental Lean preparation failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

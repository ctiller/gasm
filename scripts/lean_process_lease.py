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

"""Host-global lease and commit-reserve check for Lean/Lake process trees.

The lock lives in the host temporary directory, not a worktree, so independent gasm worktrees and
clones serialize their canonical Lean commands. OS file locks are released automatically if a
holder crashes. The environment marker makes nested canonical launchers reentrant: the outer
holder remains responsible for the whole child process tree.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import ctypes
from dataclasses import dataclass
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from typing import Iterator


LEASE_HELD_ENV = "GASM_LEAN_LEASE_HELD"
RESERVE_GIB_ENV = "GASM_LEAN_COMMIT_RESERVE_GIB"
PHYSICAL_RESERVE_GIB_ENV = "GASM_LEAN_PHYSICAL_RESERVE_GIB"
TIMEOUT_SECONDS_ENV = "GASM_LEAN_LEASE_TIMEOUT_SECONDS"
DEFAULT_RESERVE_GIB = 32.0
DEFAULT_PHYSICAL_RESERVE_GIB = 12.0
DEFAULT_TIMEOUT_SECONDS = 1800.0
LOCK_PATH = Path(tempfile.gettempdir()) / "gasm-lean-process-tree-v1.lock"


@dataclass(frozen=True)
class CommitStatus:
    total_bytes: int
    available_bytes: int
    total_physical_bytes: int
    available_physical_bytes: int


def windows_commit_status() -> CommitStatus | None:
    if os.name != "nt":
        return None

    class MEMORYSTATUSEX(ctypes.Structure):
        _fields_ = [
            ("dwLength", ctypes.c_ulong),
            ("dwMemoryLoad", ctypes.c_ulong),
            ("ullTotalPhys", ctypes.c_ulonglong),
            ("ullAvailPhys", ctypes.c_ulonglong),
            ("ullTotalPageFile", ctypes.c_ulonglong),
            ("ullAvailPageFile", ctypes.c_ulonglong),
            ("ullTotalVirtual", ctypes.c_ulonglong),
            ("ullAvailVirtual", ctypes.c_ulonglong),
            ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
        ]

    status = MEMORYSTATUSEX()
    status.dwLength = ctypes.sizeof(status)
    if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):
        raise ctypes.WinError()
    return CommitStatus(
        int(status.ullTotalPageFile),
        int(status.ullAvailPageFile),
        int(status.ullTotalPhys),
        int(status.ullAvailPhys),
    )


def _try_lock(file_obj) -> bool:
    file_obj.seek(0)
    if os.name == "nt":
        import msvcrt

        try:
            msvcrt.locking(file_obj.fileno(), msvcrt.LK_NBLCK, 1)
            return True
        except OSError:
            return False
    else:
        import fcntl

        try:
            fcntl.flock(file_obj.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            return True
        except BlockingIOError:
            return False


def _unlock(file_obj) -> None:
    file_obj.seek(0)
    if os.name == "nt":
        import msvcrt

        msvcrt.locking(file_obj.fileno(), msvcrt.LK_UNLCK, 1)
    else:
        import fcntl

        fcntl.flock(file_obj.fileno(), fcntl.LOCK_UN)


def _configured_float(name: str, default: float, minimum: float) -> float:
    raw = os.environ.get(name)
    if raw is None:
        return default
    try:
        value = float(raw)
    except ValueError as error:
        raise ValueError(f"{name} must be numeric, got {raw!r}") from error
    if value < minimum:
        raise ValueError(f"{name} must be >= {minimum}, got {value}")
    return value


def _configured_optional_float(name: str, minimum: float) -> float | None:
    if name not in os.environ:
        return None
    return _configured_float(name, 0.0, minimum)


@contextmanager
def lean_process_lease() -> Iterator[None]:
    if os.environ.get(LEASE_HELD_ENV) == "1":
        yield
        return

    reserve_override_gib = _configured_optional_float(RESERVE_GIB_ENV, 0.0)
    physical_reserve_override_gib = _configured_optional_float(
        PHYSICAL_RESERVE_GIB_ENV, 0.0
    )
    timeout_seconds = _configured_float(TIMEOUT_SECONDS_ENV, DEFAULT_TIMEOUT_SECONDS, 1.0)
    deadline = time.monotonic() + timeout_seconds
    reported_wait = False
    required_commit_gib = reserve_override_gib or DEFAULT_RESERVE_GIB
    required_physical_gib = physical_reserve_override_gib or DEFAULT_PHYSICAL_RESERVE_GIB

    LOCK_PATH.parent.mkdir(parents=True, exist_ok=True)
    with LOCK_PATH.open("a+b") as lock_file:
        if lock_file.seek(0, os.SEEK_END) == 0:
            lock_file.write(b"0")
            lock_file.flush()

        while True:
            locked = _try_lock(lock_file)
            if locked:
                try:
                    commit = windows_commit_status()
                    if commit is not None:
                        # Defaults adapt downward on smaller CI hosts so the guard cannot demand
                        # more memory than the machine owns. Explicit environment overrides remain
                        # exact. This host retains a large desktop/app reserve.
                        required_commit_gib = reserve_override_gib if reserve_override_gib is not None else min(
                            DEFAULT_RESERVE_GIB,
                            max(4.0, (commit.total_bytes / 1024**3) * 0.30),
                        )
                        required_physical_gib = (
                            physical_reserve_override_gib
                            if physical_reserve_override_gib is not None
                            else min(
                                DEFAULT_PHYSICAL_RESERVE_GIB,
                                max(2.0, (commit.total_physical_bytes / 1024**3) * 0.25),
                            )
                        )
                    reserve_bytes = int(required_commit_gib * 1024**3)
                    physical_reserve_bytes = int(required_physical_gib * 1024**3)
                    if commit is None or (
                        commit.available_bytes >= reserve_bytes
                        and commit.available_physical_bytes >= physical_reserve_bytes
                    ):
                        # Do not mutate os.environ here. run_gates can have multiple worker
                        # threads in this process; a process-global marker would let a sibling
                        # thread mistake another thread's lease for its own. Only child process
                        # environments receive LEASE_HELD_ENV via inherited_lease_environment().
                        yield
                        return
                    available_gib = commit.available_bytes / 1024**3
                    available_physical_gib = commit.available_physical_bytes / 1024**3
                    if not reported_wait:
                        print(
                            "Waiting for Lean memory reserve: "
                            f"commit {available_gib:.1f}/{required_commit_gib:.1f} GiB required, "
                            f"physical {available_physical_gib:.1f}/"
                            f"{required_physical_gib:.1f} GiB required.",
                            file=sys.stderr,
                            flush=True,
                        )
                        reported_wait = True
                finally:
                    _unlock(lock_file)
            elif not reported_wait:
                print("Waiting for the host-global Lean/Lake process-tree lease.",
                      file=sys.stderr, flush=True)
                reported_wait = True

            if time.monotonic() >= deadline:
                raise TimeoutError(
                    f"timed out after {timeout_seconds:.0f}s waiting for the global Lean lease "
                    f"and reserves (commit {required_commit_gib:.1f} GiB, "
                    f"physical {required_physical_gib:.1f} GiB)"
                )
            time.sleep(1.0)


def inherited_lease_environment() -> dict[str, str]:
    env = os.environ.copy()
    env[LEASE_HELD_ENV] = "1"
    return env


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run one command under the host-global Lean/Lake process-tree lease."
    )
    parser.add_argument("--status", action="store_true", help="print current commit headroom")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)

    if args.status:
        status = windows_commit_status()
        if status is None:
            print("commit headroom: unavailable on this platform; lease serialization still applies")
        else:
            print(
                f"commit_total_gib={status.total_bytes / 1024**3:.1f} "
                f"commit_available_gib={status.available_bytes / 1024**3:.1f} "
                f"physical_total_gib={status.total_physical_bytes / 1024**3:.1f} "
                f"physical_available_gib={status.available_physical_bytes / 1024**3:.1f}"
            )
        if not args.command:
            return 0

    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required unless --status is used alone")
    try:
        with lean_process_lease():
            return subprocess.run(
                command,
                check=False,
                env=inherited_lease_environment(),
            ).returncode
    except (OSError, TimeoutError, ValueError) as error:
        print(f"Lean process-tree lease failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

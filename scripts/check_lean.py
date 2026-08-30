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

"""Incrementally check Lean source files through Lake's cached OLean targets.

Unlike ``lake env lean FILE``, this command records the resulting OLean in Lake's build graph, so
an unchanged repeat is a trace check rather than another full elaboration. Files are built one at
a time under the host-global Lean lease to avoid duplicate multi-GiB direct compiler processes.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import sys

from lean_process_lease import inherited_lease_environment, lean_process_lease


REPO_ROOT = Path(__file__).resolve().parent.parent


def module_for_source(raw_path: str) -> str:
    source = Path(raw_path)
    if not source.is_absolute():
        source = REPO_ROOT / source
    source = source.resolve()
    try:
        relative = source.relative_to(REPO_ROOT)
    except ValueError as error:
        raise ValueError(f"Lean source is outside the repository: {source}") from error
    if source.suffix != ".lean" or not source.is_file():
        raise ValueError(f"Lean source does not exist: {relative}")
    return ".".join(relative.with_suffix("").parts)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", help="repository-relative .lean source file(s)")
    parser.add_argument(
        "--print-only", action="store_true", help="print cached Lake commands without running them"
    )
    args = parser.parse_args(argv)

    try:
        modules = [module_for_source(path) for path in args.files]
    except ValueError as error:
        parser.error(str(error))
    lake = shutil.which("lake") or "lake"
    commands = [[lake, "build", f"+{module}:olean"] for module in modules]
    print("Cached focused Lean check (not a substitute for the full repository build):")
    for command in commands:
        print(subprocess.list2cmdline(command), flush=True)
    if args.print_only:
        return 0

    try:
        with lean_process_lease():
            child_env = inherited_lease_environment()
            for command in commands:
                result = subprocess.run(
                    command, cwd=REPO_ROOT, check=False, env=child_env
                )
                if result.returncode != 0:
                    return result.returncode
    except (OSError, TimeoutError, ValueError) as error:
        print(f"focused Lean check failed before launch: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

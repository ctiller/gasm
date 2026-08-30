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
import os
from pathlib import Path
import shutil
import subprocess
import sys


REPO_ROOT = Path(__file__).resolve().parent.parent
OPT_IN_ENV = "GASM_RUN_FULL_REFS_COVERAGE"
TRUE_VALUES = {"1", "true", "yes"}


def opted_in(flag: bool) -> bool:
    return flag or os.environ.get(OPT_IN_ENV, "").strip().lower() in TRUE_VALUES


def lake_command(forwarded: list[str]) -> list[str]:
    lake = shutil.which("lake") or "lake"
    return [lake, "exe", "check_refs_coverage_full", "--", *forwarded]


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

    command = lake_command(forwarded)
    if args.print_command:
        print(subprocess.list2cmdline(command))
        return 0
    return subprocess.run(command, cwd=REPO_ROOT, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())

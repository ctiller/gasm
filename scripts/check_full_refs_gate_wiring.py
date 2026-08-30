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

"""Reject active command shapes that bypass the guarded full-refs launcher."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys


REPO_ROOT = Path(__file__).resolve().parent.parent
AUTHORIZED_RAW_LAUNCHER = "scripts/run_full_refs_coverage.py"
SCANNED_PREFIXES = (".github/", "scripts/", "tests/")
SCANNED_SUFFIXES = {".py", ".ps1", ".sh", ".yml", ".yaml", ".toml"}

# These patterns describe invocations, not prose or internal gate keys: an E2E helper call,
# an argv fragment, or a shell/workflow command line. The one file authorized to construct the
# raw command is excluded from the repository scan below.
COMMAND_PATTERNS = (
    re.compile(
        r"run_lean_target\s*\(\s*['\"]check_refs_coverage(?:_full)?['\"]",
        re.MULTILINE,
    ),
    re.compile(
        r"['\"]exe['\"]\s*,\s*['\"]check_refs_coverage(?:_full)?['\"]",
        re.MULTILINE,
    ),
    re.compile(
        r"^\s*(?:run:\s*)?(?:[&.]\s*)?(?:lake|lake\.exe)\s+exe\s+"
        r"check_refs_coverage(?:_full)?(?:\s|$)",
        re.IGNORECASE | re.MULTILINE,
    ),
)


def command_shape_hits(text: str) -> list[str]:
    hits: list[str] = []
    for pattern in COMMAND_PATTERNS:
        hits.extend(match.group(0).strip() for match in pattern.finditer(text))
    return hits


def tracked_candidate_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "--", ".github", "scripts", "tests"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return [
        path
        for path in result.stdout.splitlines()
        if path.startswith(SCANNED_PREFIXES)
        and Path(path).suffix.lower() in SCANNED_SUFFIXES
        and path != AUTHORIZED_RAW_LAUNCHER
    ]


def check_repository() -> list[str]:
    findings: list[str] = []
    for relative in tracked_candidate_files():
        text = (REPO_ROOT / relative).read_text(encoding="utf-8")
        for hit in command_shape_hits(text):
            findings.append(f"{relative}: raw full-gate invocation: {hit}")
    return findings


def self_test() -> int:
    old_target = "check_refs_" + "coverage"
    raw_target = old_target + "_full"
    bad = (
        f'ctx.run_lean_target("{old_target}")',
        f'[lake, "exe", "{raw_target}"]',
        f'lake exe {old_target}\n',
        f'run: lake exe {raw_target} --scan-module Foo Foo.lean\n',
    )
    good = (
        'key = "check_refs_coverage"',
        'The historical executable was check_refs_coverage.',
        '[python, "scripts/run_full_refs_coverage.py", "--full-repository"]',
    )
    if any(not command_shape_hits(sample) for sample in bad):
        print("self-test failed: a raw invocation shape was not detected", file=sys.stderr)
        return 1
    if any(command_shape_hits(sample) for sample in good):
        print("self-test failed: prose or the canonical launcher was rejected", file=sys.stderr)
        return 1
    print("full-refs wiring checker self-test passed")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Ensure runners/tests/workflows use the guarded full-refs launcher."
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    findings = check_repository()
    if findings:
        print("Full declaration-coverage gate wiring check failed:", file=sys.stderr)
        for finding in findings:
            print(f"  {finding}", file=sys.stderr)
        print(
            "Use: python scripts/run_full_refs_coverage.py --full-repository",
            file=sys.stderr,
        )
        return 1
    print("Full declaration-coverage gate wiring is protected.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

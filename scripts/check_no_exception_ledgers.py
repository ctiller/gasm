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

"""Reject every gate-exception ledger and every parser that could honor one."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_PATH = Path(__file__).relative_to(REPO_ROOT).as_posix()
FORBIDDEN_PATH_PARTS = (
    "allowlist", "allow_list", "whitelist", "waiver", "exemption",
    "gate_exception", "gate-exception", "bypass_ledger", "suppression_ledger",
    "optout_ledger", "opt_out_ledger",
)
PARSER_MARKERS = (
    "ALLOWLIST_PATH", "load_allowlist", "parseAllowlist", "AllowlistEntry",
    "load_waivers", "parseWaiver", "load_exceptions", "parseExceptionLedger",
    "suppress_finding", "is_exempt",
)
RETIRED_LEDGER_REFERENCES = (
    "scripts/gate_allowlist.txt",
    "temporary law-10 ledger",
    "authoritative live ledger",
    "sole temporary exception",
    "law-10 debt ledger",
    "current ledger:",
    "checked-in allowlist",
    "pre-authorize declarations",
    "debt ledger was not widened",
)


def tracked_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"], cwd=REPO_ROOT, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise RuntimeError(f"git ls-files failed: {result.stderr.strip()}")
    return [line.strip().replace("\\", "/") for line in result.stdout.splitlines() if line.strip()]


def forbidden_ledger_paths(paths: Iterable[str]) -> list[str]:
    return sorted(
        path for path in paths
        if path != RATCHET_PATH and any(part in path.lower() for part in FORBIDDEN_PATH_PARTS)
    )


def parser_leaks(paths: Iterable[str]) -> list[str]:
    leaks = []
    for rel in paths:
        if rel == RATCHET_PATH:
            continue
        path = REPO_ROOT / rel
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        hits = [marker for marker in PARSER_MARKERS if marker in text]
        if hits:
            leaks.append(f"{rel}: {', '.join(hits)}")
    return sorted(leaks)


def retired_reference_leaks(paths: Iterable[str]) -> list[str]:
    leaks = []
    for rel in paths:
        if rel == RATCHET_PATH:
            continue
        path = REPO_ROOT / rel
        try:
            source = path.read_text(encoding="utf-8").lower()
        except (OSError, UnicodeDecodeError):
            continue
        hits = [marker for marker in RETIRED_LEDGER_REFERENCES if marker in source]
        if hits:
            leaks.append(f"{rel}: {', '.join(hits)}")
    return sorted(leaks)


def run_check(paths: Iterable[str] | None = None) -> tuple[list[str], list[str], list[str]]:
    selected = list(paths) if paths is not None else tracked_files()
    return (
        forbidden_ledger_paths(selected),
        parser_leaks(selected),
        retired_reference_leaks(selected),
    )


def self_test() -> int:
    empty_ledger = "scripts/gate_allowlist.txt"
    comment_only_ledger = "scripts/comment_only_allowlist.txt"
    bad_paths = forbidden_ledger_paths([empty_ledger, comment_only_ledger, RATCHET_PATH])

    probes = {
        "scripts/_exception_parser_probe.py": "def load_exceptions(): pass\n",
        "scripts/_retired_path_probe.py": "# scripts/gate_allowlist.txt\n",
        "scripts/_sole_exception_probe.py": "# sole temporary exception\n",
        "scripts/_current_ledger_probe.py": "# current ledger: 1\n",
        "scripts/_checked_in_probe.py": "# checked-in allowlist\n",
        "scripts/_preauthorize_probe.py": "# pre-authorize declarations\n",
        "scripts/_widened_debt_probe.py": "# debt ledger was not widened\n",
    }
    for rel, contents in probes.items():
        (REPO_ROOT / rel).write_text(contents, encoding="utf-8")
    try:
        bad_parsers = parser_leaks(probes)
        bad_references = retired_reference_leaks(probes)
    finally:
        for rel in probes:
            (REPO_ROOT / rel).unlink(missing_ok=True)

    passed = (
        bad_paths == [comment_only_ledger, empty_ledger]
        and bad_parsers == ["scripts/_exception_parser_probe.py: load_exceptions"]
        and bad_references == [
            "scripts/_checked_in_probe.py: checked-in allowlist",
            "scripts/_current_ledger_probe.py: current ledger:",
            "scripts/_preauthorize_probe.py: pre-authorize declarations",
            "scripts/_retired_path_probe.py: scripts/gate_allowlist.txt",
            "scripts/_sole_exception_probe.py: sole temporary exception",
            "scripts/_widened_debt_probe.py: debt ledger was not widened",
        ]
    )
    print(
        "synthetic empty-ledger/comment-ledger/parser/retired-reference rejection: "
        f"{'PASS' if passed else 'FAIL'}"
    )
    return 0 if passed else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Reject gate exception ledgers and parser wiring")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()

    bad_paths, leaks, retired_references = run_check()
    print("=" * 72)
    print(" Exception-ledger removal ratchet")
    print("=" * 72)
    for path in bad_paths:
        print(f"[!] forbidden exception-ledger path: {path}")
    for leak in leaks:
        print(f"[!] exception parser authority remains: {leak}")
    for leak in retired_references:
        print(f"[!] retired exception-ledger guidance remains: {leak}")
    if not bad_paths and not leaks and not retired_references:
        print("[+] no exception ledger, parser authority, or retired-ledger guidance exists")
    return 1 if bad_paths or leaks or retired_references else 0


if __name__ == "__main__":
    sys.exit(main())

# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Ratchet against reintroducing gate exception ledgers.

All already-empty exception mechanisms have been deleted.  The Law-10 gate
ledger is the sole temporary debt file; its live-entry ceiling only moves
downward and the parser is confined to the two tools that consume it.  Once
that debt reaches zero, remove the final entries, parser, file, and temporary
allowances below.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_PATH = Path(__file__).relative_to(REPO_ROOT).as_posix()
TEMPORARY_LEDGER = "scripts/gate_allowlist.txt"
MAX_TEMPORARY_GATE_ENTRIES = 17
PINNED_GATE_KEYS = {
    "Spikes/Spike3SortLines/Windows/Equivalence.lean::spike3_canonical_effect_trace_equivalence_inst::Spikes.Spike3SortLines.Windows.spike3_canonical_effect_trace_equivalence_inst",
    "Spikes/Spike2Fibonacci/Windows/Equivalence.lean::spike2VerifiedProgram::Spikes.Spike2Fibonacci.Windows.spike2VerifiedProgram",
    "Spikes/Spike3SortLines/Windows/Equivalence.lean::spike3VerifiedProgram::Spikes.Spike3SortLines.Windows.spike3VerifiedProgram",
    "Spikes/Spike3SortLines/Windows/Equivalence.lean::spike3_effect_trace_equivalence_for_canonical_stdin::Spikes.Spike3SortLines.Windows.spike3_effect_trace_equivalence_for_canonical_stdin",
    "Spikes/Spike2Fibonacci/Windows/Emit.lean::main::main",
    "Spikes/Spike3SortLines/Windows/Emit.lean::main::main",
    "Spikes/Spike3SortLines/Windows/Test.lean::runTests::Spikes.Spike3SortLines.Windows.runTests",
    "Spikes/Spike3SortLines/Windows/Test.lean::main::main",
    "Spikes/Spike2Fibonacci/Linux/Emit.lean::main::main",
    "Spikes/Spike2Fibonacci/Linux/Equivalence.lean::spike2VerifiedProgram::Spikes.Spike2Fibonacci.Linux.spike2VerifiedProgram",
    "Spikes/Spike3SortLines/Linux/Emit.lean::main::main",
    "Spikes/Spike3SortLines/Linux/Equivalence.lean::spike3VerifiedProgram::Spikes.Spike3SortLines.Linux.spike3VerifiedProgram",
    "Spikes/Spike3SortLines/Linux/Equivalence.lean::spike3_canonical_effect_trace_equivalence_inst::Spikes.Spike3SortLines.Linux.spike3_canonical_effect_trace_equivalence_inst",
    "Spikes/Spike3SortLines/Linux/Equivalence.lean::spike3_empty_effect_trace_equivalence_inst::Spikes.Spike3SortLines.Linux.spike3_empty_effect_trace_equivalence_inst",
    "Spikes/Spike3SortLines/Linux/Test.lean::main::main",
    "Spikes/Spike3SortLines/Linux/Test.lean::runTests::Spikes.Spike3SortLines.Linux.runTests",
    "Spikes/Spike2Fibonacci/Linux/Test.lean::main::main",
}
PINNED_GATE_ROWS = {
    key: (
        "grandfathered"
        if "spike3_canonical_effect_trace_equivalence_inst" in key
        or "spike3_empty_effect_trace_equivalence_inst" in key
        else "axiom-only"
    )
    for key in PINNED_GATE_KEYS
}
PINNED_DIRECT_MECHANISMS = {
    key: ({"native_decide": 1} if "spike3_canonical_effect_trace_equivalence_inst" in key
          or "spike3_empty_effect_trace_equivalence_inst" in key else {})
    for key in PINNED_GATE_ROWS
}
TEMPORARY_PARSER_FILES = {
    "scripts/check_gates.py",
    "Tools/CheckGatesAxioms.lean",
}
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
LEDGER_REFERENCE_RE = re.compile(
    r"scripts/[A-Za-z0-9_.-]*(?:allowlist|allow_list|whitelist|waiver|exemption|"
    r"gate[_-]exceptions?|bypass[_-]ledger|suppression[_-]ledger|opt[_-]?out[_-]ledger)"
    r"[A-Za-z0-9_.-]*",
    re.IGNORECASE,
)


def tracked_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"], cwd=REPO_ROOT, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise RuntimeError(f"git ls-files failed: {result.stderr.strip()}")
    return [line.strip().replace("\\", "/") for line in result.stdout.splitlines() if line.strip()]


def forbidden_ledger_paths(paths: Iterable[str]) -> list[str]:
    bad = []
    for path in paths:
        lowered = path.lower()
        if path in {TEMPORARY_LEDGER, RATCHET_PATH}:
            continue
        if any(part in lowered for part in FORBIDDEN_PATH_PARTS):
            bad.append(path)
    return sorted(bad)


def parser_leaks(paths: Iterable[str]) -> list[str]:
    leaks = []
    for rel in paths:
        if rel in TEMPORARY_PARSER_FILES or rel == RATCHET_PATH:
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


def forbidden_ledger_references(paths: Iterable[str]) -> list[str]:
    """Reject documentation or code that advertises a retired exception path."""
    leaks = []
    for rel in paths:
        if rel == RATCHET_PATH:
            continue
        path = REPO_ROOT / rel
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        references = sorted(set(LEDGER_REFERENCE_RE.findall(text)))
        retired = [
            ref for ref in references
            if ref.rstrip(".") not in {TEMPORARY_LEDGER, RATCHET_PATH}
        ]
        if retired:
            leaks.append(f"{rel}: {', '.join(retired)}")
    return sorted(leaks)


def count_live_entries(text: str) -> int:
    return sum(
        1 for line in text.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    )


def live_temporary_entries() -> int:
    path = REPO_ROOT / TEMPORARY_LEDGER
    if not path.is_file():
        return 0
    return count_live_entries(path.read_text(encoding="utf-8"))


def temporary_rows(text: str) -> list[tuple[str, str]]:
    rows = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        parts = stripped.split("::")
        if len(parts) >= 4:
            rows.append(("::".join(part.strip() for part in parts[:3]), parts[3].strip()))
    return rows


def row_identity_failures(
    rows: list[tuple[str, str]], pinned: dict[str, str] = PINNED_GATE_ROWS
) -> list[str]:
    """Require the live debt inventory to equal this revision's exact pin."""
    expected = Counter((key, category) for key, category in pinned.items())
    actual = Counter(rows)
    failures = []
    for row, count in sorted((actual - expected).items()):
        failures.append(f"unexpected row ({count}x): {row[0]}::{row[1]}")
    for row, count in sorted((expected - actual).items()):
        failures.append(f"pinned row missing ({count}x): {row[0]}::{row[1]}")
    return failures


def live_row_identity_failures() -> list[str]:
    path = REPO_ROOT / TEMPORARY_LEDGER
    if not path.is_file():
        return []
    return row_identity_failures(temporary_rows(path.read_text(encoding="utf-8")))


def direct_mechanism_failures(actual: dict[str, Counter[str]]) -> list[str]:
    """Pin tactic kind and occurrence count inside every debt declaration."""
    failures = []
    for key, expected_dict in sorted(PINNED_DIRECT_MECHANISMS.items()):
        expected = Counter(expected_dict)
        observed = actual.get(key, Counter())
        if observed != expected:
            failures.append(
                f"{key}: expected {dict(expected)}, observed {dict(observed)}"
            )
    return failures


def live_direct_mechanism_failures() -> list[str]:
    # Reuse the gate's comment-aware declaration attribution instead of
    # maintaining a second, weaker Lean source parser here.
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    from check_gates import collect_occurrences  # type: ignore

    occurrences, _, _ = collect_occurrences()
    by_source = {
        "::".join(key.split("::")[:2]): key for key in PINNED_GATE_ROWS
    }
    actual: dict[str, Counter[str]] = defaultdict(Counter)
    for occurrence in occurrences:
        if occurrence.decl is None:
            continue
        source_key = f"{occurrence.file}::{occurrence.decl.name}"
        pinned_key = by_source.get(source_key)
        if pinned_key is not None:
            actual[pinned_key][occurrence.kind] += 1
    return direct_mechanism_failures(actual)


def temporary_debt_exceeded(count: int) -> bool:
    return count > MAX_TEMPORARY_GATE_ENTRIES


def ratchet_configuration_failures() -> list[str]:
    if MAX_TEMPORARY_GATE_ENTRIES != len(PINNED_GATE_ROWS):
        return [
            "MAX_TEMPORARY_GATE_ENTRIES must equal the exact pinned inventory "
            f"({MAX_TEMPORARY_GATE_ENTRIES} != {len(PINNED_GATE_ROWS)})"
        ]
    return []


def has_failures(
    bad_paths: list[str], parser_leak_list: list[str], bad_references: list[str],
    row_failures: list[str], mechanism_failures: list[str],
    configuration_failures: list[str], live_entries: int
) -> bool:
    return bool(
        bad_paths
        or parser_leak_list
        or bad_references
        or row_failures
        or mechanism_failures
        or configuration_failures
        or temporary_debt_exceeded(live_entries)
    )


def run_check(paths: Iterable[str] | None = None) -> tuple[list[str], list[str], list[str], list[str], list[str], list[str], int]:
    selected = list(paths) if paths is not None else tracked_files()
    return (
        forbidden_ledger_paths(selected),
        parser_leaks(selected),
        forbidden_ledger_references(selected),
        live_row_identity_failures(),
        live_direct_mechanism_failures(),
        ratchet_configuration_failures(),
        live_temporary_entries(),
    )


def self_test() -> int:
    bad_paths = forbidden_ledger_paths([
        "scripts/new_allowlist.txt",
        "scripts/waiver_ledger.toml",
        TEMPORARY_LEDGER,
    ])
    reference_probe = "_exception_ledger_reference_probe.txt"
    parser_probe = "scripts/_exception_parser_probe.py"
    probe_path = REPO_ROOT / reference_probe
    probe_path.write_text("use scripts/new_allowlist.txt\n", encoding="utf-8")
    try:
        parser_path = REPO_ROOT / parser_probe
        parser_path.write_text("def load_exceptions(): pass\n", encoding="utf-8")
        bad_references = forbidden_ledger_references([reference_probe])
        bad_parsers = parser_leaks([parser_probe])
    finally:
        probe_path.unlink(missing_ok=True)
        (REPO_ROOT / parser_probe).unlink(missing_ok=True)
    boundary_is_accepted = not temporary_debt_exceeded(MAX_TEMPORARY_GATE_ENTRIES)
    ceiling_rejects_growth = temporary_debt_exceeded(MAX_TEMPORARY_GATE_ENTRIES + 1)
    aggregate_rejects_each_kind = all([
        has_failures(["path"], [], [], [], [], [], 0),
        has_failures([], ["parser"], [], [], [], [], 0),
        has_failures([], [], ["reference"], [], [], [], 0),
        has_failures([], [], [], ["row"], [], [], 0),
        has_failures([], [], [], [], ["mechanism"], [], 0),
        has_failures([], [], [], [], [], ["configuration"], 0),
        has_failures([], [], [], [], [], [], MAX_TEMPORARY_GATE_ENTRIES + 1),
    ])
    aggregate_accepts_clean_boundary = not has_failures(
        [], [], [], [], [], [], MAX_TEMPORARY_GATE_ENTRIES
    )
    exact_rows = list(PINNED_GATE_ROWS.items())
    identity_accepts_exact = row_identity_failures(exact_rows) == []
    removal_without_update_rejected = bool(row_identity_failures(exact_rows[:-1]))
    reduced_pin = dict(exact_rows[:-1])
    retired_resurrection_rejected = bool(row_identity_failures(exact_rows, reduced_pin))
    ceiling_must_follow_pin = MAX_TEMPORARY_GATE_ENTRIES == len(PINNED_GATE_ROWS)
    sample_key = next(key for key, expected in PINNED_DIRECT_MECHANISMS.items() if expected)
    expected_actual = {key: Counter(value) for key, value in PINNED_DIRECT_MECHANISMS.items()}
    mechanism_accepts_exact = direct_mechanism_failures(expected_actual) == []
    expected_actual[sample_key]["native_decide"] += 1
    extra_occurrence_rejected = bool(direct_mechanism_failures(expected_actual))
    passed = (
        bad_paths == ["scripts/new_allowlist.txt", "scripts/waiver_ledger.toml"]
        and bad_references == [f"{reference_probe}: scripts/new_allowlist.txt"]
        and bad_parsers == [f"{parser_probe}: load_exceptions"]
        and boundary_is_accepted
        and ceiling_rejects_growth
        and aggregate_rejects_each_kind
        and aggregate_accepts_clean_boundary
        and identity_accepts_exact
        and removal_without_update_rejected
        and retired_resurrection_rejected
        and ceiling_must_follow_pin
        and mechanism_accepts_exact
        and extra_occurrence_rejected
    )
    print(f"synthetic path/reference/parser/identity/ceiling rejection: {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Reject gate exception ledgers and parser wiring")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()

    (bad_paths, leaks, bad_references, row_failures, mechanism_failures,
     configuration_failures, live_entries) = run_check()
    failed = has_failures(
        bad_paths, leaks, bad_references, row_failures, mechanism_failures,
        configuration_failures, live_entries
    )
    print("=" * 72)
    print(" Exception-ledger removal ratchet")
    print("=" * 72)
    for path in bad_paths:
        print(f"[!] forbidden exception-ledger path: {path}")
    for leak in leaks:
        print(f"[!] exception parser outside temporary Law-10 tools: {leak}")
    for leak in bad_references:
        print(f"[!] retired exception ledger is still advertised: {leak}")
    for failure in row_failures:
        print(f"[!] Law-10 debt inventory differs from the exact pin: {failure}")
    for failure in mechanism_failures:
        print(f"[!] Law-10 debt mechanism changed: {failure}")
    for failure in configuration_failures:
        print(f"[!] Law-10 ratchet configuration drifted: {failure}")
    if temporary_debt_exceeded(live_entries):
        print(f"[!] temporary Law-10 debt grew: {live_entries} > {MAX_TEMPORARY_GATE_ENTRIES}")
    else:
        print(f"[*] temporary Law-10 debt: {live_entries}/{MAX_TEMPORARY_GATE_ENTRIES}")
    if not failed:
        print("[+] no retired exception ledger or parser has been reintroduced")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

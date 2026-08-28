#!/usr/bin/env python3
# Copyright 2026 Google LLC
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

"""
tests/e2e/runner.py - Main Test Runner for AArch64 QEMU Support in gasm.

Executes opaque-box, requirement-driven tests across Tiers 1–4.
Exit Code Conventions:
  - Exit 0: All executed tests PASSED.
  - Exit 1: One or more tests FAILED or ERROR.
  - Exit 2: One or more tests SKIPPED (missing external host runner / oracle) and no failures.

Usage:
  python tests/e2e/runner.py                     # Run all Tiers 1-4 tests
  python tests/e2e/runner.py --tier 1             # Run only Tier 1 tests
  python tests/e2e/runner.py --milestone M1       # Run only M1 tests
  python tests/e2e/runner.py --feature 1          # Run tests for Feature 1
  python tests/e2e/runner.py --feature 1,2        # Run tests for Features 1 and 2
  python tests/e2e/runner.py --test T1.01.01      # Run a single test case
  python tests/e2e/runner.py --list               # List all test cases
  python tests/e2e/runner.py --json               # Output results as JSON
"""

import argparse
import json
import sys
import time
from pathlib import Path
from typing import List, Optional, Set, Union

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tests.e2e.harness import ExecutionContext, TestCase, TestResult, TestStatus
from tests.e2e.cases.tier1_feature_coverage import get_tier1_tests
from tests.e2e.cases.tier2_boundary_corner import get_tier2_tests
from tests.e2e.cases.tier3_cross_feature import get_tier3_tests
from tests.e2e.cases.tier4_real_world import get_tier4_tests


def load_all_tests() -> List[TestCase]:
    all_tests: List[TestCase] = []
    all_tests.extend(get_tier1_tests())
    all_tests.extend(get_tier2_tests())
    all_tests.extend(get_tier3_tests())
    all_tests.extend(get_tier4_tests())
    return all_tests


def parse_feature_ids(val: Union[int, str, List[int], Set[int]]) -> List[int]:
    """Parse a single int, comma-separated string, or collection into a sorted list of feature IDs (1 to 28)."""
    if isinstance(val, int):
        ids = [val]
    elif isinstance(val, str):
        parts = [p.strip() for p in val.split(",") if p.strip()]
        if not parts:
            raise argparse.ArgumentTypeError("empty feature specification")
        try:
            ids = [int(p) for p in parts]
        except ValueError as e:
            raise argparse.ArgumentTypeError(f"invalid integer feature ID in {val!r}: {e}") from e
    elif isinstance(val, (list, set, tuple)):
        ids = [int(x) for x in val]
    else:
        raise argparse.ArgumentTypeError(f"unsupported feature ID type: {type(val).__name__}")

    for fid in ids:
        if fid < 1 or fid > 28:
            raise argparse.ArgumentTypeError(f"feature ID {fid} out of valid range (1 to 28)")
    return sorted(list(set(ids)))


def filter_tests(
    tests: List[TestCase],
    tier: Optional[int] = None,
    milestone: Optional[str] = None,
    feature_id: Optional[Union[int, str, List[int], Set[int]]] = None,
    test_id: Optional[str] = None,
    features: Optional[Union[int, str, List[int], Set[int]]] = None,
) -> List[TestCase]:
    filtered = tests
    if tier is not None:
        filtered = [t for t in filtered if t.tier == tier]
    if milestone is not None:
        filtered = [t for t in filtered if t.milestone.upper() == milestone.upper()]
    target_feature = features if features is not None else feature_id
    if target_feature is not None:
        allowed_ids = set(parse_feature_ids(target_feature))
        filtered = [t for t in filtered if t.feature_id in allowed_ids]
    if test_id is not None:
        filtered = [t for t in filtered if t.test_id.lower() == test_id.lower()]
    return filtered


def print_test_list(tests: List[TestCase]):
    print(f"{'Test ID':<12} {'Tier':<6} {'MStone':<8} {'Feat':<6} {'Name':<32} {'Description'}")
    print("-" * 110)
    for t in tests:
        print(f"{t.test_id:<12} T{t.tier:<5} {t.milestone:<8} #{t.feature_id:<5} {t.name:<32} {t.description[:45]}")
    print("-" * 110)
    print(f"Total test cases listed: {len(tests)}")


def main() -> int:
    parser = argparse.ArgumentParser(description="gasm AArch64 QEMU E2E Test Runner")
    parser.add_argument("--tier", type=int, choices=[1, 2, 3, 4], help="Filter by tier (1, 2, 3, or 4)")
    parser.add_argument("--milestone", type=str, help="Filter by milestone (e.g. M1, M2, ..., M7)")
    parser.add_argument(
        "--feature",
        type=parse_feature_ids,
        help="Filter by feature ID or comma-delimited list of IDs (e.g. 1 or 1,2; range 1 to 28)",
    )
    parser.add_argument("--test", type=str, help="Run a specific test ID (e.g. T1.01.01)")
    parser.add_argument("--list", action="store_true", help="List available test cases and exit")
    parser.add_argument("--json", action="store_true", help="Output machine-parseable JSON summary")
    parser.add_argument("--verbose", action="store_true", help="Enable verbose per-test output")
    parser.add_argument("--fail-fast", action="store_true", help="Stop execution immediately on first failure")

    args = parser.parse_args()

    all_tests = load_all_tests()

    if args.list:
        selected = filter_tests(all_tests, args.tier, args.milestone, args.feature, args.test)
        print_test_list(selected)
        return 0

    selected_tests = filter_tests(all_tests, args.tier, args.milestone, args.feature, args.test)
    if not selected_tests:
        print("[-] No test cases matched the specified filter criteria.", file=sys.stderr)
        return 1

    ctx = ExecutionContext(repo_root=REPO_ROOT)

    if not args.json:
        print("=" * 80)
        print("  gasm AArch64 QEMU End-to-End Test Suite Runner")
        print("=" * 80)
        print(f"  Repo Root:   {ctx.repo_root}")
        print(f"  QEMU System: {ctx.qemu_system or 'NONE (Hardware validation will skip honestly)'}")
        print(f"  QEMU User:   {ctx.qemu_user or 'NONE (User emulation will skip honestly)'}")
        print(f"  LLVM-MC:     {ctx.llvm_mc or 'NONE'}")
        print(f"  Running:     {len(selected_tests)} test cases")
        print("-" * 80)

    results: List[TestResult] = []
    start_all = time.monotonic()

    passed_count = 0
    failed_count = 0
    skipped_count = 0
    error_count = 0

    for idx, test in enumerate(selected_tests, 1):
        if not args.json and args.verbose:
            print(f"[{idx}/{len(selected_tests)}] Running {test.test_id} ({test.name})...", end=" ", flush=True)

        res = test.run(ctx)
        results.append(res)

        if res.status == TestStatus.PASS:
            passed_count += 1
            if not args.json and args.verbose:
                print(f"PASS ({res.duration_s:.3f}s)")
        elif res.status == TestStatus.FAIL:
            failed_count += 1
            if not args.json:
                print(f"[FAIL] {test.test_id} ({test.name}): {res.message}")
            if args.fail_fast:
                break
        elif res.status == TestStatus.SKIP:
            skipped_count += 1
            if not args.json and args.verbose:
                print(f"SKIP ({res.message})")
        elif res.status == TestStatus.ERROR:
            error_count += 1
            if not args.json:
                print(f"[ERROR] {test.test_id} ({test.name}): {res.message}")
            if args.fail_fast:
                break

    total_duration = time.monotonic() - start_all

    # Exit code determination:
    # 0 = All passed
    # 1 = One or more failed/error
    # 2 = One or more skipped (missing host runner) and no failures
    if failed_count > 0 or error_count > 0:
        overall_exit_code = 1
    elif skipped_count > 0:
        overall_exit_code = 2
    else:
        overall_exit_code = 0

    if args.json:
        summary = {
            "total_selected": len(selected_tests),
            "passed": passed_count,
            "failed": failed_count,
            "skipped": skipped_count,
            "errors": error_count,
            "duration_s": round(total_duration, 4),
            "exit_code": overall_exit_code,
            "results": [r.to_dict() for r in results],
        }
        print(json.dumps(summary, indent=2))
        return overall_exit_code

    print("-" * 80)
    print("Test Suite Summary:")
    print(f"  Total Run:    {len(results)}")
    print(f"  Passed:       {passed_count}")
    print(f"  Failed:       {failed_count}")
    print(f"  Skipped:      {skipped_count} (missing host runner/oracle)")
    print(f"  Errors:       {error_count}")
    print(f"  Wall Time:    {total_duration:.2f}s")
    print(f"  Final Exit:   {overall_exit_code} ({'PASS' if overall_exit_code == 0 else ('FAIL' if overall_exit_code == 1 else 'SKIP_PARTIAL')})")
    print("=" * 80)

    return overall_exit_code


if __name__ == "__main__":
    sys.exit(main())

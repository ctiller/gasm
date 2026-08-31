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
tests/e2e/runner.py - Main Test Runner for x86-64 GPR Instructions in gasm.

Executes opaque-box, requirement-driven tests across Tiers 1–4.
Exit Code Conventions:
  - Exit 0: All executed tests PASSED.
  - Exit 1: One or more tests FAILED or ERROR.
  - Exit 2: One or more tests SKIPPED (e.g. missing host runner/oracle) and no failures.

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
from typing import Dict, List, Optional, Set, Union

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
    """Parse a single int, comma-separated string, or collection into a sorted list of feature IDs (1 to 25)."""
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
        if fid < 1 or fid > 25:
            raise argparse.ArgumentTypeError(f"feature ID {fid} out of valid range (1 to 25)")
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
        allowed_features = set(parse_feature_ids(target_feature))
        filtered = [t for t in filtered if t.feature_id in allowed_features]
    if test_id is not None:
        filtered = [t for t in filtered if t.test_id == test_id or t.name == test_id]
    return filtered


def run_tests(
    tests: List[TestCase], ctx: ExecutionContext, verbose: bool = False
) -> List[TestResult]:
    results: List[TestResult] = []
    for test in tests:
        if verbose:
            print(f"Running [{test.test_id}] {test.name}...", end="", flush=True)
        res = test.run(ctx)
        results.append(res)
        if verbose:
            status_str = res.status.value
            duration = f"({res.duration_s:.3f}s)"
            msg = f": {res.message}" if res.message else ""
            print(f" [{status_str}] {duration}{msg}")
    return results


def print_summary_table(results: List[TestResult], elapsed: float) -> None:
    total = len(results)
    passed = sum(1 for r in results if r.status == TestStatus.PASS)
    failed = sum(1 for r in results if r.status == TestStatus.FAIL)
    skipped = sum(1 for r in results if r.status == TestStatus.SKIP)
    errored = sum(1 for r in results if r.status == TestStatus.ERROR)

    print("\n" + "=" * 80)
    print(" x86-64 GPR E2E Test Suite Execution Summary")
    print("=" * 80)
    print(f" Total Executed: {total}")
    print(f"   [+] Passed:  {passed:4d} ({(passed/total*100) if total else 0:.1f}%)")
    print(f"   [-] Failed:  {failed:4d} ({(failed/total*100) if total else 0:.1f}%)")
    print(f"   [*] Skipped: {skipped:4d} ({(skipped/total*100) if total else 0:.1f}%)")
    print(f"   [!] Errors:  {errored:4d} ({(errored/total*100) if total else 0:.1f}%)")
    print(f" Elapsed Time: {elapsed:.3f}s")
    print("-" * 80)

    # Tier Breakdown
    print(" Tier Breakdown:")
    for tier in sorted(list(set(r.tier for r in results))):
        tier_res = [r for r in results if r.tier == tier]
        t_pass = sum(1 for r in tier_res if r.status == TestStatus.PASS)
        t_fail = sum(1 for r in tier_res if r.status == TestStatus.FAIL)
        t_skip = sum(1 for r in tier_res if r.status == TestStatus.SKIP)
        t_err = sum(1 for r in tier_res if r.status == TestStatus.ERROR)
        tier_names = {
            1: "Tier 1 (Feature Coverage)",
            2: "Tier 2 (Boundary & Corner)",
            3: "Tier 3 (Cross-Feature)",
            4: "Tier 4 (Real-World Scenarios)",
        }
        name = tier_names.get(tier, f"Tier {tier}")
        print(f"   Tier {tier} [{name}]: {len(tier_res)} total | {t_pass} pass | {t_fail} fail | {t_skip} skip | {t_err} err")

    print("-" * 80)

    # Milestone Breakdown
    print(" Milestone Breakdown:")
    m_order = ["M1", "M2", "M3", "M4", "M5", "M6"]
    present_ms = sorted(list(set(r.milestone for r in results)), key=lambda m: m_order.index(m) if m in m_order else 99)
    for m in present_ms:
        m_res = [r for r in results if r.milestone == m]
        m_pass = sum(1 for r in m_res if r.status == TestStatus.PASS)
        m_fail = sum(1 for r in m_res if r.status == TestStatus.FAIL)
        m_skip = sum(1 for r in m_res if r.status == TestStatus.SKIP)
        m_err = sum(1 for r in m_res if r.status == TestStatus.ERROR)
        print(f"   Milestone {m:2s}: {len(m_res):3d} total | {m_pass:3d} pass | {m_fail:3d} fail | {m_skip:3d} skip | {m_err:3d} err")

    print("=" * 80)

    if failed > 0 or errored > 0:
        print("\nFailures / Errors Detail (first 15):")
        shown = 0
        for r in results:
            if r.status in (TestStatus.FAIL, TestStatus.ERROR):
                shown += 1
                print(f"  - [{r.test_id}] {r.name} (Tier {r.tier}, {r.milestone}, Feat {r.feature_id}): {r.message}")
                if shown >= 15:
                    remaining = (failed + errored) - shown
                    if remaining > 0:
                        print(f"    ... and {remaining} more failing tests")
                    break
        print()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tier", type=int, choices=[1, 2, 3, 4], help="Run tests for a specific tier (1-4)")
    parser.add_argument("--milestone", type=str, help="Run tests for a specific milestone (e.g. M1, M2, M3)")
    parser.add_argument("--feature", type=str, help="Run tests for a feature ID or comma-separated IDs (1-25)")
    parser.add_argument("--features", type=str, help="Alias for --feature")
    parser.add_argument("--test", type=str, help="Run a specific test ID (e.g. T1.01.01)")
    parser.add_argument("--list", action="store_true", help="List all matching tests without running them")
    parser.add_argument("--json", action="store_true", help="Output results in JSON format")
    parser.add_argument("-v", "--verbose", action="store_true", help="Print each test as it runs")
    args = parser.parse_args()

    all_tests = load_all_tests()
    selected_tests = filter_tests(
        all_tests,
        tier=args.tier,
        milestone=args.milestone,
        feature_id=args.feature,
        test_id=args.test,
        features=args.features,
    )

    if args.list:
        print(f"Listing {len(selected_tests)} test(s):")
        for t in selected_tests:
            print(f"  {t.test_id:10s} Tier {t.tier} | {t.milestone:3s} | Feat {t.feature_id:02d} | {t.name}: {t.description}")
        return 0

    ctx = ExecutionContext()
    start_time = time.monotonic()
    results = run_tests(selected_tests, ctx, verbose=args.verbose)
    elapsed = time.monotonic() - start_time

    if args.json:
        out_dict = {
            "total": len(results),
            "passed": sum(1 for r in results if r.status == TestStatus.PASS),
            "failed": sum(1 for r in results if r.status == TestStatus.FAIL),
            "skipped": sum(1 for r in results if r.status == TestStatus.SKIP),
            "errors": sum(1 for r in results if r.status == TestStatus.ERROR),
            "elapsed_seconds": round(elapsed, 4),
            "results": [r.to_dict() for r in results],
        }
        print(json.dumps(out_dict, indent=2))
    else:
        print_summary_table(results, elapsed)

    has_failures = any(r.status in (TestStatus.FAIL, TestStatus.ERROR) for r in results)
    has_skips = any(r.status == TestStatus.SKIP for r in results)

    if has_failures:
        return 1
    elif has_skips and not has_failures:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

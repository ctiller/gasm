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

"""
scripts/check_instructions_umbrella.py - Instructions.lean umbrella completeness check (B3).

Gasm/Targets/X86_64/Instructions.lean is a hand-maintained "true umbrella": it imports every
Instructions/<Family>.lean submodule specifically so that Registry.lean's build-time environment
audit (docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate) can see every
registered `X86_64Instruction` instance -- Lean's environment walk only sees declarations
reachable through the current file's import graph, not every `.lean` file Lake happens to
compile. A new Instructions/<Foo>.lean file that is never added to this umbrella's import list is
therefore invisible to that audit: it will not be flagged as missing, because the audit never
learns it exists.

Before this script, nothing mechanically enforced that the umbrella's import list actually
matched the files on disk -- it was convention only (see docs/tasks/B1-build-perf-iteration2.md's
2026-08-27 "iteration 2 complete" note and docs/tasks/B3-stage-b-decoder-modularization.md's
"design constraint from the B1 review" note, both of which flag this as a residual gap). This
script closes it with a direct filesystem-vs-import-list diff: it does NOT eliminate the
underlying blind spot (a file that is neither on disk in this directory nor referenced anywhere
still could not be found by any purely-static check that doesn't also cross-reference `git`), but
it does mean "a Instructions/<Foo>.lean file that exists on disk but isn't imported by the
umbrella" is now a build-failing, exit-1, named-offender condition instead of a silent gap that
depends on someone remembering the convention.

A file counts as a "family" needing umbrella coverage iff it declares at least one
`instance : X86_64Instruction <Type>` -- detected structurally (regex over the file's own text),
not via a hand-maintained exclusion list, so a new piece of shared infrastructure (like
Base.lean or Obligations.lean, neither of which declares such an instance) never needs this
script itself edited to stay correct; only files that actually register a decodable/encodable
instruction are required to appear in the umbrella's import list.

Exit 0 if the umbrella's imports exactly match the instruction family files on disk. Exit 1,
naming the exact symmetric difference, otherwise.

Usage:
    python scripts/check_instructions_umbrella.py             # the gate (default)
    python scripts/check_instructions_umbrella.py --json      # machine-readable result
    python scripts/check_instructions_umbrella.py --self-test # plant real defects, prove red, revert

--self-test exists because this script was wired into `scripts/run_gates.py`'s gate table and
`.github/workflows/ci.yml` only as a follow-up: `docs/tasks/B3-stage-b-decoder-modularization.md`'s
"not done, flagged for follow-up" note gave the missing mutation test as the reason it stayed
unwired, and wiring a never-observed-red gate would have made this file exactly the kind of
decorative check it exists to prevent. A gate only ever observed to pass is not a gate
(`docs/REVIEW.md` Law 13); every other linter gate in this tree (`check_doc_facade.py`,
`check_record.py`, `check_orphan_modules.py`, `run_gates.py`) carries the same re-runnable
planted-defect fixture, and this one now does too.
"""

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
INSTRUCTIONS_DIR = REPO_ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions"
UMBRELLA_FILE = REPO_ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions.lean"
IMPORT_PREFIX = "Gasm.Targets.X86_64.Instructions."

# Matches `instance : X86_64Instruction Foo where` and `instance : X86_64Instruction Foo := ...`
# -- deliberately permissive about the RHS, since only "does this file register at least one
# instance" matters here, not the instance's own shape.
INSTANCE_DECL_RE = re.compile(r"^\s*instance\s*:\s*X86_64Instruction\b", re.MULTILINE)


def is_family_file(path: Path) -> bool:
    return bool(INSTANCE_DECL_RE.search(path.read_text(encoding="utf-8")))


def families_on_disk() -> set[str]:
    if not INSTRUCTIONS_DIR.is_dir():
        print(f"error: {INSTRUCTIONS_DIR} is not a directory", file=sys.stderr)
        sys.exit(1)
    return {
        p.stem
        for p in INSTRUCTIONS_DIR.glob("*.lean")
        if is_family_file(p)
    }


def imports_in_umbrella() -> set[str]:
    """Every `Instructions.<Name>` this file imports, raw -- includes non-family infra imports
    like Base/Obligations, which is fine; `main` below only checks the directions that matter
    (a family missing from this set, or an import pointing at a file that no longer exists)."""
    if not UMBRELLA_FILE.is_file():
        print(f"error: {UMBRELLA_FILE} does not exist", file=sys.stderr)
        sys.exit(1)
    text = UMBRELLA_FILE.read_text(encoding="utf-8")
    imported: set[str] = set()
    for line in text.splitlines():
        m = re.match(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", line)
        if not m:
            continue
        module = m.group(1)
        if module.startswith(IMPORT_PREFIX):
            imported.add(module[len(IMPORT_PREFIX):])
    return imported


def compute() -> dict:
    """Runs the whole check. Returns a plain dict so the human report, --json and --self-test
    all consume exactly the same computed result, with no second code path that could disagree
    with the one CI runs."""
    all_files_on_disk = {p.stem for p in INSTRUCTIONS_DIR.glob("*.lean")}
    families = families_on_disk()
    imported = imports_in_umbrella()

    return {
        "total_files": len(all_files_on_disk),
        "families": len(families),
        # A family (declares an X86_64Instruction instance) that this umbrella doesn't import at
        # all -- the actual audit-completeness hole this script exists to close.
        "missing_from_umbrella": sorted(families - imported),
        # An import naming a file that no longer exists on disk (stale, e.g. after a
        # rename/delete) -- imports of legitimate non-family infra (Base, Obligations, ...) are
        # NOT flagged here, since those files existing on disk is what matters, not whether
        # they're themselves a family.
        "stale_in_umbrella": sorted(imported - all_files_on_disk),
    }


def result_exit_code(result: dict) -> int:
    return 1 if (result["missing_from_umbrella"] or result["stale_in_umbrella"]) else 0


def print_report(result: dict) -> None:
    if result_exit_code(result) == 0:
        print(
            f"OK: Instructions.lean imports all {result['families']} instruction family files on "
            f"disk (of {result['total_files']} total Instructions/*.lean files); no stale "
            "imports."
        )
        return

    print("Instructions.lean umbrella completeness check FAILED.", file=sys.stderr)
    if result["missing_from_umbrella"]:
        print(
            "  Declares an X86_64Instruction instance but is NOT imported by Instructions.lean "
            f"(invisible to the Registry.lean audit): {result['missing_from_umbrella']}",
            file=sys.stderr,
        )
    if result["stale_in_umbrella"]:
        print(
            "  Imported by Instructions.lean but the file no longer exists on disk "
            f"(stale import): {result['stale_in_umbrella']}",
            file=sys.stderr,
        )


# --- --self-test ---------------------------------------------------------------
# A RE-RUNNABLE regression test for this gate itself, matching the convention
# scripts/check_orphan_modules.py / check_doc_facade.py / run_gates.py already use: plant a REAL
# defect, assert the gate goes red AND names the offender, revert, assert green again, with
# try/finally so a crash mid-test cannot leave the tree dirty.
#
# Both planted vectors are UNTRACKED scratch files that no `lake build` ever compiles (nothing
# imports them), and neither touches the umbrella file or the git index, so a concurrent agent's
# build is unaffected. The negative control matters as much as the positive one: an
# Instructions/*.lean that declares NO X86_64Instruction instance is legitimate shared
# infrastructure (Base.lean, Obligations.lean), and a gate that fired on those would have to be
# argued around, which is how gates get disabled.

SELF_TEST_FAMILY = "_UmbrellaGateSelfTestScratch"
SELF_TEST_INFRA = "_UmbrellaGateSelfTestInfra"

SELF_TEST_FAMILY_CONTENT = """\
/- check_instructions_umbrella.py --self-test scratch family (never committed).
   Declares an X86_64Instruction instance and is imported by no umbrella, which is
   exactly the defect this gate exists to catch. -/

structure UmbrellaGateSelfTestScratch where
  dummy : Nat

instance : X86_64Instruction UmbrellaGateSelfTestScratch where
"""

SELF_TEST_INFRA_CONTENT = """\
/- check_instructions_umbrella.py --self-test scratch infrastructure (never committed).
   Declares NO X86_64Instruction instance, so it is NOT a family and this gate must
   stay silent about it even though no umbrella imports it. -/

def umbrellaGateSelfTestHelper : Nat := 0
"""


def _self_test_unimported_family() -> dict:
    """Control vector 1: a file that registers an instruction but that the umbrella does not
    import must turn the gate red and name the file."""
    path = INSTRUCTIONS_DIR / f"{SELF_TEST_FAMILY}.lean"
    red = False
    names_offender = False
    red_exit = None
    try:
        path.write_text(SELF_TEST_FAMILY_CONTENT, encoding="utf-8")
        after = compute()
        red_exit = result_exit_code(after)
        red = SELF_TEST_FAMILY in after["missing_from_umbrella"]
        names_offender = red and not after["stale_in_umbrella"]
    finally:
        path.unlink(missing_ok=True)

    green_after = compute()
    return {
        "vector": "unimported_family",
        "scratch": f"Instructions/{SELF_TEST_FAMILY}.lean",
        "red_exit_code": red_exit,
        "turned_red": red,
        "named_only_the_real_offender": names_offender,
        "green_exit_code": result_exit_code(green_after),
        "green_after_revert": result_exit_code(green_after) == 0,
    }


def _self_test_non_family_ignored() -> dict:
    """Control vector 2 (NEGATIVE control, Law 13's 'must reject a known-bad input AND pass a
    known-good one'): an un-imported Instructions/*.lean that declares no X86_64Instruction
    instance is shared infrastructure, not a family, and must NOT be reported. If a future edit
    replaces the structural instance detection with a filename or exclusion-list heuristic,
    vector 1 keeps passing and THIS vector is the one that goes red."""
    path = INSTRUCTIONS_DIR / f"{SELF_TEST_INFRA}.lean"
    reported = True
    exit_code = None
    try:
        path.write_text(SELF_TEST_INFRA_CONTENT, encoding="utf-8")
        during = compute()
        reported = SELF_TEST_INFRA in during["missing_from_umbrella"]
        exit_code = result_exit_code(during)
    finally:
        path.unlink(missing_ok=True)

    return {
        "vector": "non_family_ignored",
        "scratch": f"Instructions/{SELF_TEST_INFRA}.lean",
        "reported_as_missing": reported,
        "exit_code_while_present": exit_code,
        "stayed_silent": (not reported) and exit_code == 0,
    }


def run_self_test(json_mode: bool) -> int:
    if not json_mode:
        print("#" * 78)
        print("# check_instructions_umbrella.py --self-test: planted-defect control vectors")
        print("#" * 78)

    results = []
    for label, fn, ok_key in [
        ("unimported_family", _self_test_unimported_family, None),
        ("non_family_ignored", _self_test_non_family_ignored, "stayed_silent"),
    ]:
        if not json_mode:
            print(f"\n[SELF-TEST] {label} ...")
        r = fn()
        if ok_key is None:
            ok = (r["turned_red"] and r["green_after_revert"]
                  and r["named_only_the_real_offender"]
                  and r["red_exit_code"] == 1 and r["green_exit_code"] == 0)
        else:
            ok = bool(r[ok_key])
        r["passed"] = ok
        results.append(r)
        if not json_mode:
            for key, value in r.items():
                if key in ("vector", "passed"):
                    continue
                print(f"    {key} = {value}")
            print(f"  -> {'PASS' if ok else 'FAIL'}")

    all_ok = all(r["passed"] for r in results)
    overall = "PASS" if all_ok else "FAIL"

    if json_mode:
        print(json.dumps({"self_test": overall, "results": results}, indent=2))
    else:
        print("\n" + "=" * 78)
        print(f" SELF-TEST SUMMARY: {overall}")
        for r in results:
            print(f"  - {r['vector']:<22} {'PASS' if r['passed'] else 'FAIL'}")
        print("=" * 78)

    return 0 if all_ok else 1


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Instructions.lean umbrella completeness gate (B3)"
    )
    parser.add_argument("--json", action="store_true", help="machine-readable JSON output")
    parser.add_argument("--self-test", action="store_true",
                        help="plant a real unimported family, assert red, revert, assert green")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test(args.json)

    result = compute()
    if args.json:
        print(json.dumps({**result, "exit_code": result_exit_code(result)}, indent=2))
    else:
        print_report(result)
    return result_exit_code(result)


if __name__ == "__main__":
    sys.exit(main())

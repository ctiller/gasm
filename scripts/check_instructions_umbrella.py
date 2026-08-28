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

Exit 0 if the umbrella's imports exactly match the instruction family files on disk (minus
Base.lean, which is shared infrastructure, not itself a family). Exit 1, naming the exact
symmetric difference, otherwise.
"""

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
INSTRUCTIONS_DIR = REPO_ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions"
UMBRELLA_FILE = REPO_ROOT / "Gasm" / "Targets" / "X86_64" / "Instructions.lean"
IMPORT_PREFIX = "Gasm.Targets.X86_64.Instructions."

# Base.lean is shared REX/ModR/M-parsing infrastructure every family imports, not itself a family
# with an X86_64Instruction instance to audit -- excluded from both sides of the comparison.
NOT_A_FAMILY = {"Base"}


def families_on_disk() -> set[str]:
    if not INSTRUCTIONS_DIR.is_dir():
        print(f"error: {INSTRUCTIONS_DIR} is not a directory", file=sys.stderr)
        sys.exit(1)
    return {
        p.stem
        for p in INSTRUCTIONS_DIR.glob("*.lean")
        if p.stem not in NOT_A_FAMILY
    }


def families_imported_by_umbrella() -> set[str]:
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
    return imported - NOT_A_FAMILY


def main() -> int:
    on_disk = families_on_disk()
    imported = families_imported_by_umbrella()

    missing_from_umbrella = sorted(on_disk - imported)
    stale_in_umbrella = sorted(imported - on_disk)

    if not missing_from_umbrella and not stale_in_umbrella:
        print(
            f"OK: Instructions.lean's {len(imported)} family imports exactly match "
            f"the {len(on_disk)} Instructions/*.lean family files on disk "
            f"(excluding {sorted(NOT_A_FAMILY)})."
        )
        return 0

    print("Instructions.lean umbrella completeness check FAILED.", file=sys.stderr)
    if missing_from_umbrella:
        print(
            "  On disk but NOT imported by Instructions.lean (invisible to the "
            f"Registry.lean audit): {missing_from_umbrella}",
            file=sys.stderr,
        )
    if stale_in_umbrella:
        print(
            "  Imported by Instructions.lean but the file no longer exists on disk "
            f"(stale import): {stale_in_umbrella}",
            file=sys.stderr,
        )
    return 1


if __name__ == "__main__":
    sys.exit(main())

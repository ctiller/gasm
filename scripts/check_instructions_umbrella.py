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
"""

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


def main() -> int:
    all_files_on_disk = {p.stem for p in INSTRUCTIONS_DIR.glob("*.lean")}
    families = families_on_disk()
    imported = imports_in_umbrella()

    # A family (declares an X86_64Instruction instance) that this umbrella doesn't import at all
    # -- the actual audit-completeness hole this script exists to close.
    missing_from_umbrella = sorted(families - imported)
    # An import naming a file that no longer exists on disk (stale, e.g. after a rename/delete)
    # -- imports of legitimate non-family infra (Base, Obligations, ...) are NOT flagged here,
    # since those files existing on disk is what matters, not whether they're themselves a family.
    stale_in_umbrella = sorted(imported - all_files_on_disk)

    if not missing_from_umbrella and not stale_in_umbrella:
        print(
            f"OK: Instructions.lean imports all {len(families)} instruction family files on "
            f"disk (of {len(all_files_on_disk)} total Instructions/*.lean files); no stale "
            "imports."
        )
        return 0

    print("Instructions.lean umbrella completeness check FAILED.", file=sys.stderr)
    if missing_from_umbrella:
        print(
            "  Declares an X86_64Instruction instance but is NOT imported by Instructions.lean "
            f"(invisible to the Registry.lean audit): {missing_from_umbrella}",
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

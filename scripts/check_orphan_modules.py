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
scripts/check_orphan_modules.py - orphan-module reachability gate (Law 13 ratchet).

THE DEFECT CLASS THIS EXISTS TO MAKE UNREPRESENTABLE
----------------------------------------------------
A `.lean` file is committed but is never imported, transitively, by any build root
`lakefile.toml` declares. `lake build` walks a target's import closure and nothing
else, so no `.olean` is ever produced for that file: it is committed, reviewed, and
counted in the tree, but NOTHING COMPILES IT. Every proof in it is unchecked, every
`sorry` in it is invisible to `lake exe check_gates_axioms` (whose environment walk
only sees declarations reachable from the umbrella roots), and every declaration in
it is invisible to `lake exe check_refs_coverage` for the same reason. The file
looks verified and is not.

This has now happened four times, which is what makes it a gate rather than four
fixes (docs/REVIEW.md Law 13, "findings become gates" -- a reviewer catching a bug
is evidence of a missing gate, not of a working process):

  1. d5c1171  Spikes/Spike3SortLines/{TraceStepLemmas, Windows/InstructionStepLemmas,
              Windows/InterceptLemmas}.lean -- 3 modules
  2. 7414099  Gasm/Targets/X86_64/MemoryFrame.lean + its 6 submodules -- 7 modules
  3. Stdlib/Zlib/CanonicalTableSpec.lean -- 671 committed lines of axiom-clean proof
              that nothing built, found only because CI went red downstream of it
  4. Gasm/Targets/X86_64/RoundtripGate/DispatchExhaustive.lean -- committed in
              d38ed28, unreached ever since; see scripts/orphan_allowlist.txt

Instances 3 and 4 were live simultaneously. Three of the four are under `Gasm/` or
`Spikes/`, so this is not a `Stdlib` problem and the root derivation below must
cover every declared `[[lean_lib]]`, not one favoured umbrella. Replaying this gate
against each pre-fix tree reports exactly those files and nothing else: 3, 7, 1 and
1 blocking orphan respectively.

Each instance so far was fixed by hand-adding one `import` line. Under Law 13 that
closes the instance and not the class: nothing stopped the next one.

WHY THE EXISTING GATES ARE NOT THIS GATE
----------------------------------------
`lake exe check_gates_axioms` and `lake exe check_refs_coverage` both already go red
on an orphan -- they enumerate `.lean` files from the FILESYSTEM and then fail to
open the missing `.olean`. But they report it as a bare exit 1 alongside "0 NOT
allowlisted" / "0 uncited": zero substantive violations and no named cause. Worse,
that signal does not separate the one real orphan from the 47 modules their own
closure simply does not model (the census below), so the same red means "a proof is
unchecked" and "this tool cannot see executables" indistinguishably. `docs/REVIEW.md`
Law 13 records what an unexplained red costs -- it trains people to stop reading failures.

This gate's contribution is therefore not detection, which partly existed; it is
naming the file, the umbrella, and the exact line to add, with a root model that
does not raise the other 47. Its filesystem-walk-free enumeration also means it does
not go red on an agent's uncommitted work-in-progress the way those two do (see the
enumeration section below).

WHAT IS CHECKED
---------------
Every tracked `.lean` file must be reachable, TRANSITIVELY, through `import` edges
from at least one root declared in `lakefile.toml`. Reachability is a graph walk,
not a flat membership test: a module legitimately reached via an intermediate
import (the overwhelmingly common case here -- the `Stdlib` umbrella names 30-odd
modules directly and reaches 37) is correct and is not flagged.

THE ROOTS ARE DERIVED, NEVER HARDCODED
--------------------------------------
A hardcoded root list is itself this gate's own failure mode one level up: add a
new `[[lean_lib]]` to `lakefile.toml` and every file under it would be silently
unchecked forever. So the roots are parsed out of `lakefile.toml` on every run --
every `[[lean_lib]]`'s `roots` and every `[[lean_exe]]`'s `root`. A root naming a
module with no file on disk is itself a hard failure (exit 1), not a skipped root.

BOTH lean_lib AND lean_exe ROOTS COUNT, and that is deliberate. The property being
enforced is "`lake build` compiles this file", and a `[[lean_exe]]` root is a real
build root: Lake compiles it and produces its `.olean` exactly as it does for a
library umbrella. All 46 `[[lean_exe]]` and all 4 `[[lean_lib]]` targets declared
here are in `defaultTargets`, so a plain `lake build` compiles every one of them.

THE CENSUS BEHIND THAT DECISION, because it also explains a number other gates
report. Restricting the roots to the `Gasm`/`Stdlib`/`Spikes` `[[lean_lib]]`
umbrellas alone leaves 48 modules unreachable -- the same 48 that `lake exe
check_gates_axioms` reports as "not reachable from the baseline import graph".
Classified, that population is:

    42  are themselves a declared [[lean_exe]] root (every `Spikes/*/Emit.lean`,
        every `*/Test.lean`, the fuzzer CLIs, ...)
     5  are reached only THROUGH an exe root (X86_64/{EncodingFuzzer, Fuzzer,
        NASM, Performance}.lean and Spikes/Common/WasmHostRunner.lean)
     1  is reachable from no declared root at all: RoundtripGate/
        DispatchExhaustive.lean, a documented deliberate exclusion
        (scripts/orphan_allowlist.txt)

47 of those 48 are compiled; exactly one is not. Counting them all as orphans would
make this gate 98% allowlist -- enforcement in appearance only, the failure the
doc-facade rollout warns about -- and a gate that must be argued around
is a gate that gets disabled. The 48 is a MODELLING GAP in the tools that walk only
the three lib umbrellas, not 48 defects in the tree.

The same gap explains the 23 "stale" entries `check_gates_axioms` reports against
scripts/gate_allowlist.txt: all 23 are category `axiom-only`, and every one names a
file in the 48 above. They are not stale. They correctly pre-authorize declarations
the scanner never reaches, and it calls them stale because it cannot see their
subjects. Deleting them would be the wrong fix.

NOTE that "compiled" is a weaker property than "inside the axiom gate's environment
walk": a `sorry` in those 47 modules is a compiler warning that `lake build` exits 0
on, and the axiom tool that would harden it into a failure never sees them. That is
the import-closure blind spot documented in `docs/REVIEW.md` §4.1.1. This gate does not close it and does not
claim to -- closing it means widening those tools' closure to every declared target,
which would also retire both FAILED sections described above.

ENUMERATION IS `git ls-files`, NEVER A FILESYSTEM WALK
------------------------------------------------------
THIS IS A LOAD-BEARING DESIGN PROPERTY, NOT A CONVENIENCE. If you are here to
"improve" this script by switching to `Path.rglob("*.lean")`, read all three
reasons first.

1. TRACKED-ONLY IS THE CORRECT SEMANTICS, and it is what separates a defect from
   somebody's open editor. A *committed* orphan is the defect this gate exists to
   catch: hundreds of lines of reviewed, axiom-clean proof that nothing compiles.
   An *untracked* orphan is an agent mid-edit -- a file that is not yet claimed to
   be anything, and that no CI checkout will ever contain. Firing on it would make
   the gate red for work that is proceeding normally, and this repository has
   already recorded what that costs (`docs/REVIEW.md` Law 13 and the doc-facade linter's rollout
   reasoning): a gate that fires on legitimate work trains people to stop reading
   red, and a gate nobody reads prevents nothing.

   This distinction is not hypothetical here. `lake exe check_gates_axioms` walks
   the FILESYSTEM, and on 2026-08-28 that produced two runs an hour apart that
   disagreed about `Stdlib/Zlib/CanonicalTableSpec.lean` -- red while the file was
   an agent's untracked work-in-progress, exit 0 once it was committed. Both runs
   were correct about what they measured; they were measuring different trees.
   This gate measures the tracked tree, which is the one CI checks out, so a green
   run here means the same thing on every machine and in CI.

2. Several agents write to this tree concurrently, and any of them may have an
   uncommitted `.lean` on disk at any moment. A filesystem walk makes one agent's
   scratch file everyone else's red build.

3. This repository contains nested git worktrees under `.claude/worktrees/`, each a
   full copy of the tree. A naive recursive walk therefore sees every file several
   times over; that previously produced 86 phantom CI failures.

`git ls-files` gets all three right by construction, because the index contains the
tracked tree and nothing else.

Exit 0 when every tracked `.lean` file is reachable (or carries a justified
allowlist entry). Exit 1, naming every orphan, its owning umbrella, and the exact
`import` line to add, otherwise.

Usage:
    python scripts/check_orphan_modules.py             # full report (default)
    python scripts/check_orphan_modules.py --json      # machine-readable JSON
    python scripts/check_orphan_modules.py --validate  # allowlist integrity only
    python scripts/check_orphan_modules.py --self-test # plant a real orphan, prove red, revert
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# Docs/paths may contain non-ASCII; never let a legacy console codepage turn a
# report line into a crash. (Mirrors scripts/check_refs.py / check_licenses.py.)
if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if sys.stderr.encoding and sys.stderr.encoding.lower() not in ("utf-8", "utf8"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
LAKEFILE_PATH = REPO_ROOT / "lakefile.toml"
ALLOWLIST_PATH = REPO_ROOT / "scripts" / "orphan_allowlist.txt"

VALID_ALLOWLIST_CATEGORIES = {"deliberate-standalone", "pending-wiring"}


# --- Enumeration ---------------------------------------------------------------

def list_tracked_lean_files(env: Optional[Dict[str, str]] = None) -> List[str]:
    """
    Every tracked `.lean` file, as a repo-root-relative forward-slash path.

    `git ls-files` and NOT a filesystem walk. Untracked files are EXCLUDED ON PURPOSE
    (an agent's work-in-progress is not a committed unverified proof) and nested
    `.claude/worktrees/` copies are excluded for free. See this module's docstring,
    "ENUMERATION IS `git ls-files`, NEVER A FILESYSTEM WALK", before changing this.

    `env` exists solely so --self-test can point `GIT_INDEX_FILE` at a throwaway copy
    of the index; production callers pass None.
    """
    proc = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=REPO_ROOT, capture_output=True, shell=False, env=env,
    )
    if proc.returncode != 0:
        print(
            "error: `git ls-files` failed (exit "
            f"{proc.returncode}): {proc.stderr.decode('utf-8', 'replace').strip()}",
            file=sys.stderr,
        )
        sys.exit(1)
    out = proc.stdout.decode("utf-8", "replace")
    return sorted(p for p in out.split("\0") if p.endswith(".lean"))


def module_of(rel_path: str) -> str:
    """`Stdlib/Zlib/Spec.lean` -> `Stdlib.Zlib.Spec` (Lake's own path<->module mapping)."""
    return rel_path[: -len(".lean")].replace("/", ".")


def path_of(module: str) -> str:
    """Inverse of module_of."""
    return module.replace(".", "/") + ".lean"


# --- Import parsing ------------------------------------------------------------

IMPORT_RE = re.compile(r"^import\s+(?:all\s+)?([A-Za-z0-9_.]+)\s*$")


def imports_of(rel_path: str) -> List[str]:
    """
    The modules `rel_path` imports.

    Lean requires the import section to precede every other command in a file, so
    this walks the header and STOPS at the first line that is neither blank, nor a
    comment, nor an `import`/`prelude`. That bound is what keeps prose out: this
    tree contains doc-comment lines that begin with the word "import" at column 0
    (e.g. Tools/CheckGatesAxioms.lean's "import closure in the resulting kernel
    environment"), and an unbounded regex sweep of the whole file would happily
    invent import edges out of them. Block comments (`/- ... -/`, including the
    Apache-2.0 header every file opens with) are tracked by nesting depth.
    """
    text = (REPO_ROOT / rel_path).read_text(encoding="utf-8")
    found: List[str] = []
    depth = 0
    for line in text.splitlines():
        stripped = line.strip()
        if depth > 0:
            depth += stripped.count("/-") - stripped.count("-/")
            continue
        if not stripped or stripped.startswith("--"):
            continue
        if stripped.startswith("/-"):
            depth += stripped.count("/-") - stripped.count("-/")
            continue
        m = IMPORT_RE.match(line)
        if m:
            found.append(m.group(1))
            continue
        if stripped == "prelude":
            continue
        break
    return found


# --- lakefile.toml root derivation ---------------------------------------------

def _toml_string_values(raw: str) -> List[str]:
    """Every double-quoted string in a TOML scalar-or-array right-hand side."""
    return re.findall(r'"([^"]*)"', raw)


def _parse_tables(text: str, table_name: str) -> List[Dict[str, str]]:
    """
    Every `[[<table_name>]]` array-of-tables entry, as raw key -> raw-RHS dicts.

    Deliberately a small hand parser rather than `tomllib`: this must run identically
    under whatever Python the CI image ships, `lakefile.toml` here is flat and
    comment-heavy, and the only shapes ever read back are `name`, `roots`, and `root`.
    """
    tables: List[Dict[str, str]] = []
    current: Optional[Dict[str, str]] = None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            continue
        if stripped == f"[[{table_name}]]":
            current = {}
            tables.append(current)
            continue
        if stripped.startswith("[[") or stripped.startswith("["):
            current = None
            continue
        if current is None:
            continue
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)$", stripped)
        if m:
            current[m.group(1)] = m.group(2)
    return tables


class BuildRoot:
    """One root module declared by lakefile.toml, plus which target declared it."""

    __slots__ = ("module", "target_kind", "target_name")

    def __init__(self, module: str, target_kind: str, target_name: str):
        self.module = module
        self.target_kind = target_kind      # "lean_lib" | "lean_exe"
        self.target_name = target_name


def derive_build_roots() -> Tuple[List[BuildRoot], List[str]]:
    """
    Parses lakefile.toml's `[[lean_lib]] roots` and `[[lean_exe]] root` declarations.

    NOTHING HERE IS HARDCODED, on purpose: a hardcoded root list would mean a newly
    declared library's whole subtree is silently unchecked, which is this gate's own
    defect class applied to the gate itself.
    """
    errors: List[str] = []
    if not LAKEFILE_PATH.is_file():
        return [], [f"lakefile.toml not found at {LAKEFILE_PATH}"]

    text = LAKEFILE_PATH.read_text(encoding="utf-8")
    roots: List[BuildRoot] = []

    for lib in _parse_tables(text, "lean_lib"):
        names = _toml_string_values(lib.get("name", ""))
        name = names[0] if names else "<unnamed>"
        declared = _toml_string_values(lib.get("roots", ""))
        if not declared:
            errors.append(f"lakefile.toml: [[lean_lib]] '{name}' declares no parseable `roots`")
            continue
        for module in declared:
            roots.append(BuildRoot(module, "lean_lib", name))

    for exe in _parse_tables(text, "lean_exe"):
        names = _toml_string_values(exe.get("name", ""))
        name = names[0] if names else "<unnamed>"
        declared = _toml_string_values(exe.get("root", ""))
        if not declared:
            errors.append(f"lakefile.toml: [[lean_exe]] '{name}' declares no parseable `root`")
            continue
        roots.append(BuildRoot(declared[0], "lean_exe", name))

    if not roots:
        errors.append(
            "lakefile.toml: no [[lean_lib]]/[[lean_exe]] roots parsed at all -- refusing to "
            "report a vacuously green run (with no roots, every file is trivially an orphan "
            "and this gate would instead have to be silently disabled)"
        )
    return roots, errors


# --- Allowlist -----------------------------------------------------------------

class AllowlistEntry:
    __slots__ = ("path", "category", "added", "added_by", "justification", "line_num")

    def __init__(self, path: str, category: str, added: str, added_by: str,
                 justification: str, line_num: int):
        self.path = path
        self.category = category
        self.added = added
        self.added_by = added_by
        self.justification = justification
        self.line_num = line_num


def load_allowlist() -> Tuple[Dict[str, AllowlistEntry], List[str]]:
    """
    Parses scripts/orphan_allowlist.txt: 5 `::`-delimited fields --
    `relative-file-path::category::added-date::added-by::justification`
    (the same shape as scripts/gate_allowlist.txt and scripts/license_allowlist.txt).

    Keyed on the file path, since an exemption applies to a whole module. A line with
    any other field count, an unknown category, an empty path, an empty justification,
    or a duplicate path is a HARD PARSE FAILURE -- never a silently-skipped line.
    """
    entries: Dict[str, AllowlistEntry] = {}
    errors: List[str] = []

    if not ALLOWLIST_PATH.exists():
        return entries, errors

    text = ALLOWLIST_PATH.read_text(encoding="utf-8")
    for line_num, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("::", 4)
        if len(parts) != 5:
            errors.append(
                f"orphan_allowlist.txt:{line_num}: expected 5 '::'-delimited fields "
                f"(file::category::added::added_by::justification), got {len(parts)}: {raw_line!r}"
            )
            continue
        file_path, category_raw, added, added_by, justification = (
            parts[0].strip(), parts[1].strip(), parts[2].strip(),
            parts[3].strip(), parts[4].strip(),
        )
        category = category_raw.lower()
        if not file_path:
            errors.append(f"orphan_allowlist.txt:{line_num}: empty file path")
            continue
        if category not in VALID_ALLOWLIST_CATEGORIES:
            errors.append(
                f"orphan_allowlist.txt:{line_num}: unknown category '{category_raw}' "
                f"(expected one of {sorted(VALID_ALLOWLIST_CATEGORIES)})"
            )
            continue
        if not justification:
            errors.append(f"orphan_allowlist.txt:{line_num}: missing justification")
            continue
        if file_path in entries:
            errors.append(
                f"orphan_allowlist.txt:{line_num}: duplicate entry for '{file_path}' "
                f"(first defined at line {entries[file_path].line_num}) -- duplicates are a "
                f"hard error, not silent last-wins"
            )
            continue
        entries[file_path] = AllowlistEntry(
            file_path, category, added, added_by, justification, line_num
        )

    return entries, errors


# --- Core check ----------------------------------------------------------------

class Orphan:
    __slots__ = ("rel_path", "module", "owner_lib", "owner_root_module",
                 "owner_root_path", "allowlisted", "entry")

    def __init__(self, rel_path: str, module: str, owner_lib: Optional[str],
                 owner_root_module: Optional[str], owner_root_path: Optional[str]):
        self.rel_path = rel_path
        self.module = module
        self.owner_lib = owner_lib
        self.owner_root_module = owner_root_module
        self.owner_root_path = owner_root_path
        self.allowlisted = False
        self.entry: Optional[AllowlistEntry] = None


def _owning_library(module: str, roots: List[BuildRoot]) -> Optional[BuildRoot]:
    """
    Which `[[lean_lib]]` umbrella *should* have reached this module: the library root
    with the longest matching dotted-component prefix. `Stdlib.Zlib.CanonicalTableSpec`
    -> the `Stdlib` lib, root module `Stdlib`, i.e. the file `Stdlib.lean`. Returns
    None for a module under no declared library root at all (e.g. `Tools.*`, which this
    tree reaches only through `[[lean_exe]]` roots).
    """
    parts = module.split(".")
    best: Optional[BuildRoot] = None
    best_len = 0
    for root in roots:
        if root.target_kind != "lean_lib":
            continue
        rparts = root.module.split(".")
        if parts[: len(rparts)] == rparts and len(rparts) > best_len:
            best, best_len = root, len(rparts)
    return best


def compute(env: Optional[Dict[str, str]] = None) -> Dict:
    """
    Runs the whole check. Returns a plain dict so --json, the human report and
    --self-test all consume exactly the same computed result, with no second
    code path that could disagree with the one CI runs.
    """
    files = list_tracked_lean_files(env)
    module_to_path = {module_of(f): f for f in files}

    roots, errors = derive_build_roots()
    allowlist, allowlist_errors = load_allowlist()
    errors = list(errors)

    # A declared root with no file on disk is a hard failure, not a skipped root: it
    # means lakefile.toml and the tree disagree about what exists, and silently
    # dropping it would shrink the reachable set and manufacture orphans downstream.
    missing_roots = []
    for root in roots:
        if root.module not in module_to_path:
            missing_roots.append(root)
            errors.append(
                f"lakefile.toml: [[{root.target_kind}]] '{root.target_name}' declares root "
                f"module '{root.module}', but no tracked file '{path_of(root.module)}' exists"
            )

    # Transitive reachability: BFS from every declared root over `import` edges,
    # recording the depth each module was first reached at (depth 0 == a root
    # itself). Depth is reported so "reachability is transitive, not a flat
    # umbrella-names-everything check" is an observable property of a green run
    # rather than a claim in a comment.
    depth: Dict[str, int] = {}
    frontier = [r.module for r in roots if r.module in module_to_path]
    for m in frontier:
        depth.setdefault(m, 0)
    while frontier:
        nxt: List[str] = []
        for module in frontier:
            for imported in imports_of(module_to_path[module]):
                if imported in module_to_path and imported not in depth:
                    depth[imported] = depth[module] + 1
                    nxt.append(imported)
        frontier = nxt

    orphans: List[Orphan] = []
    for module in sorted(module_to_path):
        if module in depth:
            continue
        owner = _owning_library(module, roots)
        orphan = Orphan(
            rel_path=module_to_path[module],
            module=module,
            owner_lib=owner.target_name if owner else None,
            owner_root_module=owner.module if owner else None,
            owner_root_path=path_of(owner.module) if owner else None,
        )
        entry = allowlist.get(orphan.rel_path)
        if entry is not None:
            orphan.allowlisted = True
            orphan.entry = entry
        orphans.append(orphan)

    # A stale allowlist entry (its file is no longer an orphan, or no longer exists)
    # is a hard failure, exactly as in check_gates.py / check_doc_facade.py: a
    # standing exemption for a defect that is gone is a pre-authorization for its
    # return, and this repository's allowlists are audited, not accumulated.
    orphan_paths = {o.rel_path for o in orphans}
    for path, entry in sorted(allowlist.items()):
        if path not in orphan_paths:
            reason = ("that file is no longer orphaned (it is now reachable from a declared "
                      "root) -- delete this entry"
                      if path in set(files)
                      else "that file is not a tracked .lean file (renamed or deleted) -- "
                           "delete this entry")
            allowlist_errors.append(
                f"orphan_allowlist.txt:{entry.line_num}: stale entry for '{path}': {reason}"
            )

    blocking = [o for o in orphans if not o.allowlisted]
    reachable_depths = [d for d in depth.values() if d > 0]

    return {
        "tracked_files": len(files),
        "roots": [
            {"module": r.module, "kind": r.target_kind, "target": r.target_name}
            for r in roots
        ],
        "lib_roots": sum(1 for r in roots if r.target_kind == "lean_lib"),
        "exe_roots": sum(1 for r in roots if r.target_kind == "lean_exe"),
        "reachable": len(depth),
        "max_import_depth": max(depth.values()) if depth else 0,
        "reached_indirectly": len(reachable_depths),
        "orphans": orphans,
        "blocking": blocking,
        "allowlisted": [o for o in orphans if o.allowlisted],
        "errors": errors,
        "allowlist_errors": allowlist_errors,
        "missing_roots": [r.module for r in missing_roots],
    }


# --- Reporting -----------------------------------------------------------------

def describe_fix(orphan: Orphan) -> List[str]:
    """
    The actionable half of the failure message: what to add, and where.

    Names the module, the umbrella that should have reached it, and the literal line
    to paste. The "or any module already reachable from it" clause is not hedging --
    the umbrella root is usually right, but a leaf lemma module often belongs behind
    the intermediate that consumes it, and this gate checks reachability, not
    placement.
    """
    lines = []
    if orphan.owner_root_path:
        lines.append(
            f"    umbrella that should reach it: {orphan.owner_root_path} "
            f"([[lean_lib]] '{orphan.owner_lib}', root module '{orphan.owner_root_module}')"
        )
        lines.append(f"    fix: add this line to {orphan.owner_root_path} "
                     f"(or to any module already reachable from it):")
        lines.append(f"        import {orphan.module}")
    else:
        lines.append(
            "    umbrella that should reach it: NONE -- this module sits under no "
            "[[lean_lib]] root declared in lakefile.toml"
        )
        lines.append(
            "    fix: import it from a module that is already reachable from a declared "
            "root, or declare a lakefile.toml target rooted at it:"
        )
        lines.append(f"        import {orphan.module}")
    return lines


def print_report(result: Dict) -> None:
    print("=" * 78)
    print(" Orphan-module reachability gate (docs/REVIEW.md Law 13)")
    print("=" * 78)
    print(f" tracked .lean files (git ls-files) : {result['tracked_files']}")
    print(f" roots derived from lakefile.toml   : {len(result['roots'])} "
          f"({result['lib_roots']} [[lean_lib]], {result['exe_roots']} [[lean_exe]])")
    print(f" reachable from a declared root     : {result['reachable']} "
          f"({result['reached_indirectly']} of them only via an intermediate import; "
          f"max import depth {result['max_import_depth']})")
    print(f" orphans                            : {len(result['orphans'])} "
          f"({len(result['blocking'])} blocking, {len(result['allowlisted'])} allowlisted)")

    for entry_orphan in result["allowlisted"]:
        e = entry_orphan.entry
        print(f"\n  ALLOWLISTED  {entry_orphan.rel_path}  [{e.category}]")
        print(f"    {e.justification}")

    for err in result["errors"]:
        print(f"\n  ERROR  {err}", file=sys.stderr)
    for err in result["allowlist_errors"]:
        print(f"\n  ALLOWLIST ERROR  {err}", file=sys.stderr)

    for orphan in result["blocking"]:
        print(f"\n  ORPHAN  {orphan.rel_path}", file=sys.stderr)
        print(f"    module: {orphan.module}", file=sys.stderr)
        print("    nothing imports it transitively from any lakefile.toml root, so "
              "`lake build` never compiles it", file=sys.stderr)
        print("    and no proof, `sorry` or axiom inside it is checked by anything.",
              file=sys.stderr)
        for line in describe_fix(orphan):
            print(line, file=sys.stderr)

    print("\n" + "=" * 78)
    if result["blocking"] or result["errors"] or result["allowlist_errors"]:
        print(f" FAILED: {len(result['blocking'])} orphaned module(s), "
              f"{len(result['errors'])} error(s), "
              f"{len(result['allowlist_errors'])} allowlist error(s).")
    else:
        print(f" OK: all {result['tracked_files']} tracked .lean files are reachable from a "
              f"lakefile.toml root.")
    print("=" * 78)


def result_exit_code(result: Dict) -> int:
    failed = bool(result["blocking"]) or bool(result["errors"]) or bool(result["allowlist_errors"])
    return 1 if failed else 0


def result_to_json(result: Dict) -> Dict:
    return {
        "tracked_files": result["tracked_files"],
        "roots": result["roots"],
        "reachable": result["reachable"],
        "max_import_depth": result["max_import_depth"],
        "reached_indirectly": result["reached_indirectly"],
        "blocking": [
            {"file": o.rel_path, "module": o.module, "owner_lib": o.owner_lib,
             "umbrella": o.owner_root_path}
            for o in result["blocking"]
        ],
        "allowlisted": [
            {"file": o.rel_path, "category": o.entry.category,
             "justification": o.entry.justification}
            for o in result["allowlisted"]
        ],
        "errors": result["errors"],
        "allowlist_errors": result["allowlist_errors"],
        "exit_code": result_exit_code(result),
    }


# --- --self-test ---------------------------------------------------------------
# A RE-RUNNABLE regression test for the gate itself, matching the convention
# scripts/check_doc_facade.py / run_gates.py already use: plant a
# REAL defect, assert the gate goes red, revert, assert it goes green again, with
# try/finally so a crash mid-test cannot leave the tree dirty. A gate only ever
# observed to pass is not a gate.
#
# The planted orphan must be TRACKED, because enumeration is `git ls-files` -- an
# untracked scratch file is correctly invisible to this gate. Staging it in the real
# index would mutate shared state (several agents write to this tree concurrently, and
# a stray intent-to-add entry can end up in someone else's commit), so the scratch
# file is staged into a THROWAWAY COPY of the index via GIT_INDEX_FILE instead. The
# real .git/index is never written. This still exercises the genuine `git ls-files`
# path rather than injecting a fake file list past it.

SELF_TEST_SCRATCH = "Stdlib/_OrphanGateSelfTestScratch.lean"

SELF_TEST_SCRATCH_CONTENT = """\
/- check_orphan_modules.py --self-test scratch module (never committed).
   Imported by nothing; exists only to prove this gate goes red on a real orphan. -/

namespace OrphanGateSelfTestScratch

def scratch : Nat := 0

end OrphanGateSelfTestScratch
"""


def _self_test_planted_orphan() -> Dict:
    """Control vector 1: a genuine tracked-but-unimported module must turn the gate red."""
    scratch_path = REPO_ROOT / SELF_TEST_SCRATCH
    git_dir = subprocess.run(
        ["git", "rev-parse", "--git-dir"], cwd=REPO_ROOT,
        capture_output=True, text=True, shell=False, check=True,
    ).stdout.strip()
    real_index = (REPO_ROOT / git_dir / "index").resolve()

    tmp_dir = tempfile.mkdtemp(prefix="orphan_gate_selftest_")
    tmp_index = Path(tmp_dir) / "index"
    red = False
    red_names_file = False
    red_names_umbrella = False
    red_exit = None
    try:
        shutil.copyfile(real_index, tmp_index)
        scratch_path.write_text(SELF_TEST_SCRATCH_CONTENT, encoding="utf-8")
        env = dict(os.environ)
        env["GIT_INDEX_FILE"] = str(tmp_index)
        subprocess.run(
            ["git", "add", "-N", "--", SELF_TEST_SCRATCH],
            cwd=REPO_ROOT, env=env, shell=False, check=True, capture_output=True,
        )
        after = compute(env=env)
        blocking_paths = [o.rel_path for o in after["blocking"]]
        red = SELF_TEST_SCRATCH in blocking_paths
        red_exit = result_exit_code(after)
        # The failure must be ACTIONABLE, not merely present: assert the report names
        # the file and resolves the owning umbrella (Stdlib -> Stdlib.lean).
        for orphan in after["blocking"]:
            if orphan.rel_path == SELF_TEST_SCRATCH:
                red_names_file = orphan.module == "Stdlib._OrphanGateSelfTestScratch"
                red_names_umbrella = orphan.owner_root_path == "Stdlib.lean"
    finally:
        scratch_path.unlink(missing_ok=True)
        shutil.rmtree(tmp_dir, ignore_errors=True)

    green_after = compute()
    return {
        "vector": "planted_orphan",
        "scratch": SELF_TEST_SCRATCH,
        "red_exit_code": red_exit,
        "turned_red": red,
        "names_orphan_module": red_names_file,
        "names_owning_umbrella": red_names_umbrella,
        "green_exit_code": result_exit_code(green_after),
        "green_after_revert": result_exit_code(green_after) == 0,
    }


def _self_test_untracked_wip_ignored() -> Dict:
    """
    Control vector 2 (NEGATIVE control, Law 13's "must reject a known-bad input AND pass
    a known-good one"): an UNTRACKED orphan `.lean` on disk is an agent mid-edit, not a
    committed unverified proof, and this gate must stay silent on it.

    Same scratch module as vector 1, with the one difference that makes it legitimate
    work rather than a defect: it is never staged into any index. If a future change
    swaps `git ls-files` for a filesystem walk, vector 1 keeps passing and THIS vector
    is the one that goes red.
    """
    scratch_path = REPO_ROOT / SELF_TEST_SCRATCH
    reported = True
    exit_code = None
    try:
        scratch_path.write_text(SELF_TEST_SCRATCH_CONTENT, encoding="utf-8")
        during = compute()
        reported = SELF_TEST_SCRATCH in {o.rel_path for o in during["orphans"]}
        exit_code = result_exit_code(during)
    finally:
        scratch_path.unlink(missing_ok=True)

    return {
        "vector": "untracked_wip_ignored",
        "scratch": SELF_TEST_SCRATCH,
        "reported_while_untracked": reported,
        "exit_code_while_untracked": exit_code,
        "stayed_silent": (not reported) and exit_code == 0,
    }


def _self_test_transitivity() -> Dict:
    """
    Control vector 3: reachability must be TRANSITIVE, not "the umbrella names every
    file". Asserts against the real tree that modules are in fact reached only via
    intermediate imports (depth >= 2) and are not reported -- i.e. that a green run is
    green because the walk works, not because the check is flat and vacuous.
    """
    result = compute()
    return {
        "vector": "transitive_reachability",
        "max_import_depth": result["max_import_depth"],
        "reached_indirectly": result["reached_indirectly"],
        "is_transitive": result["max_import_depth"] >= 2 and result["reached_indirectly"] > 0,
    }


def run_self_test(json_mode: bool) -> int:
    if not json_mode:
        print("#" * 78)
        print("# check_orphan_modules.py --self-test: planted-defect control vectors")
        print("#" * 78)

    results = []
    for label, fn, ok_key in [
        ("planted_orphan", _self_test_planted_orphan, None),
        ("untracked_wip_ignored", _self_test_untracked_wip_ignored, "stayed_silent"),
        ("transitive_reachability", _self_test_transitivity, "is_transitive"),
    ]:
        if not json_mode:
            print(f"\n[SELF-TEST] {label} ...")
        r = fn()
        if ok_key is None:
            ok = (r["turned_red"] and r["green_after_revert"]
                  and r["names_orphan_module"] and r["names_owning_umbrella"]
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
            print(f"  - {r['vector']:<26} {'PASS' if r['passed'] else 'FAIL'}")
        print("=" * 78)

    return 0 if all_ok else 1


# --- Entry point ---------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Orphan-module reachability gate for gasm (docs/REVIEW.md Law 13)"
    )
    parser.add_argument("--json", action="store_true", help="machine-readable JSON output")
    parser.add_argument("--validate", action="store_true",
                        help="check scripts/orphan_allowlist.txt integrity only")
    parser.add_argument("--self-test", action="store_true",
                        help="plant a real orphan module, assert red, revert, assert green")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test(args.json)

    if args.validate:
        _, allowlist_errors = load_allowlist()
        # A stale entry is only detectable against a real run, so --validate does the
        # full computation and then reports the allowlist half of it.
        result = compute()
        errors = result["allowlist_errors"]
        if args.json:
            print(json.dumps({"allowlist_errors": errors,
                              "entries": len(result["allowlisted"]),
                              "exit_code": 1 if errors else 0}, indent=2))
        else:
            for err in errors:
                print(f"  ALLOWLIST ERROR  {err}", file=sys.stderr)
            print(f"orphan_allowlist.txt: {len(result['allowlisted'])} live entr(ies), "
                  f"{len(errors)} error(s).")
        return 1 if errors else 0

    result = compute()
    if args.json:
        print(json.dumps(result_to_json(result), indent=2))
    else:
        print_report(result)
    return result_exit_code(result)


if __name__ == "__main__":
    sys.exit(main())

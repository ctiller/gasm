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
scripts/check_gates.py - Law 10 fast pre-check (defense-in-depth) for gasm

Law 10 now permits no native-evaluation exception ledger. Every
`native_decide`, native-configured `decide`, or `bv_decide` occurrence in
verification source is a hard failure until replaced by a kernel-checked or
constructive proof. `bv_decide` is recognized and gated identically because it shares `native_decide`'s exact
axiom-emission code path (`Lean.Meta.nativeEqTrue`, the same routine both
tactics call to compile a closed term, run it, and assert the result as an
axiom) -- see docs/PATHFINDER_CRC32.md #3.6-policy and docs/REVIEW.md Law 10's `bv_decide`
entry for the empirical basis -- so it falls under the identical "exhaustive
finite domain only" restriction, not a separate or lesser one.

THIS SCRIPT IS NOT THE GATE. It is a fast, line-regex/text pre-check over
.lean *source text*, kept as a secondary/defense-in-depth signal because it
runs in milliseconds without a Lean build. It is structurally unable to see
the ground truth: what a compiled declaration's kernel-recorded axiom
dependencies actually are. It can only recognize tactic *spellings* it
already knows about, and adversarial review has repeatedly found new
spellings and source-level disguises (comments forging declaration
boundaries, `set_option ... in` / `open ... in` prefixes, multi-line
configs) that a regex cannot close for good, in principle, no matter how
many special cases are added.

THE LOAD-BEARING GATE is Tools/CheckGatesAxioms.lean (run via
`lake exe check_gates_axioms`). It imports the whole project, walks every
*compiled* declaration in the resulting kernel environment, and asks Lean's
own axiom-dependency machinery (`Lean.collectAxioms`, the same walk
`#print axioms` performs) which axioms each declaration depends on -- this
is immune to every source-level disguise, because it reads what the kernel
recorded, not what the source text says. On Lean toolchain v4.33.1, the
axiom `native_decide`/`decide (native := true)` produce is NOT a single
shared `Lean.ofReduceBool` -- each occurrence synthesizes its own
declaration-local axiom nested under a `_native` sub-namespace (e.g.
`<decl>._native.native_decide.ax_i_j` or `<decl>._native.decide.ax_i_j`);
see Tools/CheckGatesAxioms.lean's header comment for how that was verified
and why it is matched by namespace component rather than a fixed substring.

This script still enforces, on the text it CAN see:
1. Every native-evaluator occurrence is a hard failure.
2. Any occurrence that cannot be unambiguously attributed to a named
   declaration (anonymous `example`, no preceding declaration, or an
   unresolved `set_option/open/variable ... in` prefix run) is a hard
   FAILURE -- attribution never falls back to an earlier, unrelated
   declaration.
3. (Warning-only) A declaration that is a regression check with an
   `_inst` suffix should not be cited by name
   inside another declaration's proof term/body.
"""

import subprocess
import sys
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8")

REPO_ROOT = Path(__file__).resolve().parent.parent


def git_tracked_files() -> List[str]:
    """Every git-tracked file path (POSIX, relative to REPO_ROOT), via
    `git ls-files -z` -- never a filesystem walk. Enumerating from git is
    what makes an untracked nested worktree checkout (e.g.
    `.claude/worktrees/agent-*/`, which contains a full second copy of this
    source tree) structurally impossible to pick up here: `git ls-files`
    can only ever report what the repository itself considers tracked, so a
    stray untracked copy of the tree sitting inside the repo directory -- or
    a `.lake/` build artifact, or anything else never added -- is invisible
    to it by construction, not by an exclusion list that the next new kind
    of stray directory could slip past.

    Runs with an explicit `cwd`, so behavior never depends on the caller's
    current working directory (repo root vs. any subdirectory).

    Fails LOUDLY if git itself is unavailable or errors, rather than ever
    falling back to a filesystem walk: a silent fallback would silently
    reintroduce the exact phantom-file bug this enumeration exists to
    prevent, precisely in the situation (git missing/broken) where nobody
    is watching for it.
    """
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z"], cwd=REPO_ROOT,
            capture_output=True, timeout=30,
        )
    except (FileNotFoundError, OSError) as e:
        print(f"[!] FATAL: 'git' is not available or could not be run ({e}). File "
              f"enumeration for this gate depends on 'git ls-files' -- refusing to fall "
              f"back to a filesystem walk, since that would silently reintroduce the "
              f"nested-worktree phantom-violation bug this enumeration exists to prevent.",
              file=sys.stderr)
        sys.exit(1)
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
        print(f"[!] FATAL: 'git ls-files' exited {proc.returncode}: {stderr}", file=sys.stderr)
        sys.exit(1)
    raw = proc.stdout.decode("utf-8", errors="replace")
    return [p for p in raw.split("\0") if p]


# Declaration keywords that open a new attribution boundary. `example` and
# anonymous `instance`/`def` blocks have no name -- they still open a new
# (anonymous) boundary so a later native_decide never silently inherits an
# earlier, unrelated *named* declaration. `macro`/`elab` are included so a
# native_decide hidden inside a custom macro/elaborator is still attributed
# to *something* rather than skipped over entirely.
DECL_KEYWORDS = (
    "inductive|structure|def|class|instance|theorem|lemma|axiom|opaque|"
    "example|macro|elab"
)
DECL_HEAD_REGEX = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|scoped|unsafe)\s+)*'
    r'(' + DECL_KEYWORDS + r')(?:\s+([a-zA-Z0-9_\.<>]+))?\s*'
)
_LEADING_IDENT_REGEX = re.compile(r'^([a-zA-Z0-9_\.<>]+)')

# `set_option foo bar in`, `open Foo.Bar in`, `variable (x : T) in` -- these
# prefix a declaration without themselves being one. Matched non-greedily up
# to the first standalone `in` token so simple option values don't run on.
PREFIX_CLAUSE_REGEX = re.compile(r'^\s*(?:set_option|open|variable)\b.*?\bin\b\s*')
# How many lines to look ahead when a line is *entirely* consumed by prefix
# clauses (the real declaration keyword is on a following line).
PREFIX_LOOKAHEAD_LINES = 6

# `native_decide` as a whole word (tactic invocation), anywhere in the text.
NATIVE_DECIDE_REGEX = re.compile(r'\bnative_decide\b')
# `decide` reaching a `+native` flag or a `(native := true)` / `native :=
# true` config, within a bounded window that may span a couple of lines
# (multi-line configs) but stops before the next declaration keyword so an
# unrelated, later native config isn't misattributed to this `decide`.
DECIDE_NATIVE_REGEX = re.compile(
    r'\bdecide\b(?:(?!\b(?:' + DECL_KEYWORDS + r')\b)[\s\S]){0,160}?'
    r'(?:\+native\b|\(\s*native\s*:=\s*true\s*\)|\bnative\s*:=\s*true\b)'
)
# `bv_decide` as a whole word (tactic invocation, with or without a trailing
# `(config := ...)`/`?` suffix -- the bare word match already catches every
# spelling), anywhere in the text. Gated identically to native_decide/decide
# (see the module docstring above and docs/PATHFINDER_CRC32.md #3.6-policy):
# `bv_decide` shares native_decide's exact axiom-emission code path
# (`Lean.Meta.nativeEqTrue`) on this toolchain, so it is not a lesser or
# separate restriction.
BV_DECIDE_REGEX = re.compile(r'\bbv_decide\b')


def strip_comments(text: str) -> str:
    """
    Blanks out `--` line comments and (nested) `/- -/` block comments,
    preserving newlines so line numbers stay aligned. This is what closes
    the "a `/- theorem crc32_empty : -/` comment forges a declaration
    boundary and defeats stale-entry detection" gap: both the declaration
    scan and the occurrence scan run against this stripped text, so text
    that only exists inside a comment can no longer masquerade as either.

    (Known limitation, acceptable for a defense-in-depth pre-check: a `--`
    or `/-` inside a string literal is not distinguished from a real
    comment marker.)
    """
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if in_line_comment:
            if c == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth > 0:
            if two == "/-":
                block_depth += 1
                out.append("  ")
                i += 2
                continue
            if two == "-/":
                block_depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if two == "--":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue
        if two == "/-":
            block_depth += 1
            out.append("  ")
            i += 2
            continue
        out.append(c)
        i += 1
    return "".join(out)


def iter_lean_files():
    """Every git-TRACKED `.lean` file (see git_tracked_files()). A file must
    be tracked to be checked: an untracked nested worktree copy, or any
    other untracked stray `.lean` file, is not part of this repository by
    construction and must never be able to produce a finding here."""
    for rel in sorted(git_tracked_files()):
        if not rel.endswith(".lean"):
            continue
        lean_file = REPO_ROOT / rel
        if ".lake" in lean_file.parts or ".system_generated" in lean_file.parts:
            continue
        yield lean_file


def strip_leading_prefixes(s: str) -> str:
    """Repeatedly strips leading `set_option/open/variable ... in` clauses
    from the front of a string (may be a single line or an accumulated
    multi-line lookahead buffer)."""
    while True:
        m = PREFIX_CLAUSE_REGEX.match(s)
        if not m or m.end() == 0:
            return s
        new_s = s[m.end():]
        if new_s == s:
            return s
        s = new_s


class Decl:
    __slots__ = ("line", "name", "kind", "anonymous")

    def __init__(self, line: int, name: str, kind: str, anonymous: bool):
        self.line = line
        self.name = name
        self.kind = kind
        self.anonymous = anonymous


def _finish_decl(decls: List[Decl], boundary_line: int, kind: str, name: Optional[str],
                  matched_text: str, match_end: int, lines: List[str], peek_from_idx: int) -> None:
    """Resolve a matched declaration keyword (`kind`) into a `Decl`, peeking
    to a following line for the name if it wrapped (only when the keyword
    was left dangling at end-of-line, and never for `example`)."""
    n = len(lines)
    if name is None:
        rest = matched_text[match_end:].strip()
        if kind != "example" and rest == "":
            k = peek_from_idx + 1
            while k < n:
                candidate = lines[k].strip()
                if candidate == "":
                    k += 1
                    continue
                peek = _LEADING_IDENT_REGEX.match(candidate)
                if peek:
                    name = peek.group(1)
                break

    if name is None:
        decls.append(Decl(boundary_line, f"<anonymous:{kind}@L{boundary_line}>", kind, True))
    else:
        decls.append(Decl(boundary_line, name, kind, False))


def collect_declarations(lines: List[str]) -> List[Decl]:
    """
    Returns declaration boundaries in file order (1-indexed lines), on
    COMMENT-STRIPPED lines. Every matched declaration keyword opens a
    boundary, named or not -- attribution must never skip past one to reach
    an earlier declaration. `set_option ... in` / `open ... in` /
    `variable ... in` prefixes (same-line or on their own line, chained or
    not) are stripped before matching; if a prefix run cannot be resolved
    to an actual declaration keyword within a bounded lookahead, it still
    opens an (anonymous) boundary rather than silently doing nothing.
    """
    decls: List[Decl] = []
    n = len(lines)
    i = 0
    while i < n:
        line = lines[i]
        stripped_line = strip_leading_prefixes(line)

        if stripped_line.strip() == "" and line.strip() != "":
            # Entirely consumed by prefix clause(s); the real keyword, if
            # any, is on a following line. Bounded lookahead, re-accumulating
            # and re-stripping as we go.
            buffer = ""
            resolved = False
            for j in range(i, min(i + PREFIX_LOOKAHEAD_LINES, n)):
                buffer = (buffer + " " + lines[j]).strip() if buffer else lines[j]
                candidate = strip_leading_prefixes(buffer)
                if candidate.strip() == "":
                    continue
                m = DECL_HEAD_REGEX.match(candidate)
                if m:
                    _finish_decl(decls, i + 1, m.group(1), m.group(2), candidate, m.end(), lines, j)
                    resolved = True
                    i = j + 1
                    break
                else:
                    break
            if not resolved:
                decls.append(Decl(i + 1, f"<anonymous:prefix@L{i + 1}>", "prefix", True))
                i += 1
            continue

        m = DECL_HEAD_REGEX.match(stripped_line)
        if not m:
            i += 1
            continue
        _finish_decl(decls, i + 1, m.group(1), m.group(2), stripped_line, m.end(), lines, i)
        i += 1

    return decls


def enclosing_decl(decls: List[Decl], line_num: int) -> Optional[Decl]:
    """Nearest preceding declaration boundary for a given line number."""
    best = None
    for decl in decls:
        if decl.line <= line_num:
            best = decl
        else:
            break
    return best


class Occurrence:
    __slots__ = ("file", "line", "kind", "decl")

    def __init__(self, file: str, line: int, kind: str, decl: Optional[Decl]):
        self.file = file
        self.line = line
        self.kind = kind
        self.decl = decl  # None (no enclosing decl at all) or a Decl


def find_occurrences_in_text(text: str) -> List[Tuple[int, str]]:
    """Returns [(char_offset, kind), ...] for every native_decide /
    decide+native / bv_decide occurrence in (comment-stripped) `text`, sorted
    by position. Operates on the full text (not per-line) so a multi-line
    `decide (native := true)` config is still found."""
    found = []
    for m in NATIVE_DECIDE_REGEX.finditer(text):
        found.append((m.start(), "native_decide"))
    for m in DECIDE_NATIVE_REGEX.finditer(text):
        found.append((m.start(), "decide+native"))
    for m in BV_DECIDE_REGEX.finditer(text):
        found.append((m.start(), "bv_decide"))
    found.sort(key=lambda t: t[0])
    return found


def collect_occurrences() -> Tuple[List[Occurrence], Dict[str, List[Decl]], Dict[str, List[str]]]:
    """Scans all .lean files (comment-stripped) for native_decide /
    decide+native occurrences."""
    occurrences: List[Occurrence] = []
    all_decls_by_file: Dict[str, List[Decl]] = {}
    all_lines_by_file: Dict[str, List[str]] = {}

    for lean_file in iter_lean_files():
        rel_path = lean_file.relative_to(REPO_ROOT).as_posix()
        try:
            raw_text = lean_file.read_text(encoding="utf-8")
        except Exception:
            continue

        text = strip_comments(raw_text)
        lines = text.splitlines()
        all_lines_by_file[rel_path] = lines

        decls = collect_declarations(lines)
        all_decls_by_file[rel_path] = decls

        for offset, kind in find_occurrences_in_text(text):
            line_num = text.count("\n", 0, offset) + 1
            decl = enclosing_decl(decls, line_num)
            occurrences.append(Occurrence(rel_path, line_num, kind, decl))

    return occurrences, all_decls_by_file, all_lines_by_file


def check_regression_citations(
    all_decls_by_file: Dict[str, List[Decl]],
    all_lines_by_file: Dict[str, List[str]],
) -> List[str]:
    """
    Warning-level heuristic (grep-level): a declaration with an `_inst`
    regression-check suffix should not be cited by name inside another
    declaration's body.
    Runs on comment-stripped lines, same as the occurrence scan.
    """
    protected: Dict[str, List[Tuple[str, int]]] = {}
    for rel_path, decls in all_decls_by_file.items():
        for decl in decls:
            if decl.anonymous:
                continue
            if decl.name.endswith("_inst"):
                protected.setdefault(decl.name, []).append((rel_path, decl.line))

    if not protected:
        return []

    name_regexes = {name: re.compile(r'\b' + re.escape(name) + r'\b') for name in protected}

    warnings: List[str] = []
    for rel_path, lines in all_lines_by_file.items():
        decls = all_decls_by_file.get(rel_path, [])
        for line_num, line in enumerate(lines, start=1):
            for name, regex in name_regexes.items():
                def_sites = protected[name]
                if (rel_path, line_num) in def_sites:
                    continue  # one of the declaration's own header lines
                if not regex.search(line):
                    continue
                referencing = enclosing_decl(decls, line_num)
                ref_name = referencing.name if referencing else None
                if ref_name == name and any(rel_path == f for f, _ in def_sites):
                    continue
                def_site_str = " / ".join(f"{f}:{l}" for f, l in def_sites)
                warnings.append(
                    f"    - '{name}' (defined at {def_site_str}) referenced at "
                    f"{rel_path}:{line_num} inside '{ref_name or '<no enclosing decl>'}'"
                )

    return warnings


def main():
    print("=" * 70)
    print(" gasm Law 10 fast pre-check (scripts/check_gates.py)")
    print("=" * 70)
    print("[i] This is defense-in-depth, NOT the gate. The load-bearing check is")
    print("    Tools/CheckGatesAxioms.lean (`lake exe check_gates_axioms`), which")
    print("    reads Lean's own compiled axiom-dependency graph rather than text.")

    occurrences, all_decls_by_file, all_lines_by_file = collect_occurrences()
    native_decide_count = sum(1 for o in occurrences if o.kind == "native_decide")
    decide_native_count = sum(1 for o in occurrences if o.kind == "decide+native")
    bv_decide_count = sum(1 for o in occurrences if o.kind == "bv_decide")
    print(f"\n[*] Found {len(occurrences)} Law-10-gated occurrence(s) in source text: "
          f"{native_decide_count} native_decide, {decide_native_count} decide+native/(native := true), "
          f"{bv_decide_count} bv_decide.")
    print("    (bare `decide` with no native config is unrestricted by Law 10)")

    unattributable: List[Occurrence] = []
    forbidden: List[Occurrence] = []

    for occ in occurrences:
        if occ.decl is None or occ.decl.anonymous:
            unattributable.append(occ)
        else:
            forbidden.append(occ)

    print("\n--- LAW 10 GATE CHECK (pre-check) ---")

    if unattributable:
        print(f"\n[!] FAILED: {len(unattributable)} occurrence(s) cannot be unambiguously attributed")
        print("    to a named declaration (anonymous `example`, unresolved `set_option/open/")
        print("    variable ... in` prefix, or no enclosing declaration at all) -- attribution")
        print("    never falls back to an earlier, unrelated declaration:")
        for occ in unattributable:
            decl_desc = occ.decl.name if occ.decl else "<no enclosing declaration>"
            print(f"    - {occ.file}:{occ.line} ({occ.kind}) -- {decl_desc}")

    if forbidden:
        print(f"\n[!] FAILED: {len(forbidden)} forbidden native evaluator occurrence(s):")
        for occ in forbidden:
            print(f"    - {occ.file}:{occ.line} ({occ.kind}) in '{occ.decl.name}'")
        print("    -> Replace every occurrence with a kernel-checked or constructive proof.")

    if not occurrences:
        print("[+] No forbidden native evaluator occurs in tracked Lean source.")

    print("\n--- REGRESSION-CHECK CITATION HEURISTIC (warning only) ---")
    citation_warnings = check_regression_citations(all_decls_by_file, all_lines_by_file)
    if citation_warnings:
        print(f"[!] WARNING: {len(citation_warnings)} possible citation(s) of `_inst`")
        print("    regression declarations from other declarations' bodies:")
        for w in citation_warnings:
            print(w)
    else:
        print("[+] No `_inst`-suffixed regression declaration appears to be")
        print("    cited by name inside any other declaration's body.")

    print("\n" + "=" * 70)
    print(f" SUMMARY: {len(occurrences)} Law-10-gated occurrence(s) found in source text "
          f"({native_decide_count} native_decide, {decide_native_count} decide+native/(native := true), "
          f"{bv_decide_count} bv_decide).")
    print(f"          {len(forbidden)} FAILING: forbidden evaluator")
    print(f"          {len(unattributable)} FAILING: unattributable")
    print(f"          {len(citation_warnings)} regression-citation warning(s)")
    print("=" * 70)

    if occurrences:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()

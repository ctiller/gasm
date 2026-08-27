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

Law 10 (kernel-checked gates; canonical text in docs/REVIEW.md on the
integration branch) says: `native_decide` may discharge a verification
obligation ONLY when the proposition is universally quantified over its
entire finite domain. Single-ground-instance checks are regression tests,
not verification, and every occurrence must be explicitly allowlisted in
scripts/gate_allowlist.txt (no `_inst`-suffix-in-a-module-name auto-pass --
that shortcut existed in an earlier revision and let new, unreviewed
pointwise checks slip in silently; it has been removed).

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
1. Every `native_decide` / `decide +native` / `decide (native := true)`
   occurrence must be allowlisted in scripts/gate_allowlist.txt, classified:
     - finite-forall : exhaustive over a finite domain (permanent). Given
                        only a SHALLOW SYNTACTIC sanity check (not a proof):
                        the declaration's statement must show a `∀`, a
                        `for .. in [a:b]` bound, a `List.range N` with
                        N > 1, or a `.all`/`.any` NOT applied directly to an
                        obvious bracketed literal list -- a stray `-- ∀` in
                        a comment does not count, since comments are
                        stripped before this check runs.
     - grandfathered : predates Law 10, single-vector check (migration
                       backlog). Reported every run, not hidden.
     - axiom-only    : an entry that exists purely for
                       Tools/CheckGatesAxioms.lean (a declaration that
                       transitively depends on a native-evaluation axiom via
                       citing another declaration, with no native_decide-
                       shaped TEXT of its own for this script to ever find).
                       Exempt from this script's stale-entry check by
                       construction.
2. Any occurrence that cannot be unambiguously attributed to a named
   declaration (anonymous `example`, no preceding declaration, or an
   unresolved `set_option/open/variable ... in` prefix run) is a hard
   FAILURE -- attribution never falls back to an earlier, unrelated
   declaration.
3. Allowlist integrity: duplicate keys and stale non-`axiom-only` entries
   are hard failures; parsing tolerates `::` inside the justification text;
   category comparison is case-insensitive.
4. (Warning-only) A declaration that is a regression check -- allowlisted
   as `grandfathered`, or `_inst`-suffixed -- should not be cited by name
   inside another declaration's proof term/body.
"""

import sys
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8")

REPO_ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST_PATH = REPO_ROOT / "scripts" / "gate_allowlist.txt"

VALID_CATEGORIES = {"finite-forall", "grandfathered", "axiom-only"}

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
    for lean_file in sorted(REPO_ROOT.glob("**/*.lean")):
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
    decide+native occurrence in (comment-stripped) `text`, sorted by
    position. Operates on the full text (not per-line) so a multi-line
    `decide (native := true)` config is still found."""
    found = []
    for m in NATIVE_DECIDE_REGEX.finditer(text):
        found.append((m.start(), "native_decide"))
    for m in DECIDE_NATIVE_REGEX.finditer(text):
        found.append((m.start(), "decide+native"))
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


class AllowlistEntry:
    __slots__ = ("category", "justification", "line_num", "fqn")

    def __init__(self, category: str, justification: str, line_num: int, fqn: str):
        self.category = category
        self.justification = justification
        self.line_num = line_num
        self.fqn = fqn


def load_allowlist() -> Tuple[Dict[Tuple[str, str], AllowlistEntry], List[str]]:
    """
    Parses scripts/gate_allowlist.txt (5 `::`-delimited fields: file, decl,
    fully-qualified name, category, justification). This script keys its own
    matching on (file, decl) -- the bare, unqualified name it can actually
    see in source text -- and only carries the `fqn` field through for
    display/consistency; Tools/CheckGatesAxioms.lean is what authoritatively
    matches on `fqn`.
    Returns:
      - entries: {(file, decl_name): AllowlistEntry}
      - errors: human-readable parse/integrity error strings (each one is
        a hard failure -- malformed lines and duplicate keys are never
        silently tolerated).
    """
    entries: Dict[Tuple[str, str], AllowlistEntry] = {}
    errors: List[str] = []

    if not ALLOWLIST_PATH.exists():
        return entries, errors

    text = ALLOWLIST_PATH.read_text(encoding="utf-8")
    for line_num, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        # maxsplit=4 so a `::` inside the free-text justification field
        # doesn't get mistaken for a delimiter.
        parts = line.split("::", 4)
        if len(parts) != 5:
            errors.append(
                f"gate_allowlist.txt:{line_num}: expected 5 '::'-delimited fields "
                f"(file::decl::fqn::category::justification), got {len(parts)}: {raw_line!r}"
            )
            continue
        file_path, decl_name, fqn, category_raw, justification = (
            parts[0].strip(), parts[1].strip(), parts[2].strip(), parts[3].strip(), parts[4].strip()
        )
        category = category_raw.lower()
        if category not in VALID_CATEGORIES:
            errors.append(
                f"gate_allowlist.txt:{line_num}: unknown category '{category_raw}' (expected one of {sorted(VALID_CATEGORIES)})"
            )
            continue
        if not fqn:
            errors.append(f"gate_allowlist.txt:{line_num}: missing fully-qualified name (3rd field)")
            continue
        if not justification:
            errors.append(f"gate_allowlist.txt:{line_num}: missing justification")
            continue

        key = (file_path, decl_name)
        if key in entries:
            errors.append(
                f"gate_allowlist.txt:{line_num}: duplicate entry for '{file_path}::{decl_name}' "
                f"(first defined at line {entries[key].line_num}) -- duplicates are a hard error, "
                f"not silent last-wins; remove or merge one of them"
            )
            continue

        entries[key] = AllowlistEntry(category, justification, line_num, fqn)

    return entries, errors


def corroboration_signal(text: str) -> Optional[str]:
    """
    Cheap, SHALLOW syntactic sanity check for a `finite-forall` allowlist
    entry -- not a proof, just a sign the statement isn't a single hardcoded
    value. Runs against comment-stripped text, so a `-- ∀` in a comment
    cannot satisfy it. Rejects degenerate signals:
      - `List.range 0` / `List.range 1` (checks nothing / one value).
      - `.all` / `.any` applied directly to an obvious bracketed literal
        list (e.g. `[1, 2, 3].all (...)`) -- that's a handful of hardcoded
        vectors wearing a quantifier's clothes, not real exhaustion.
    Returns a short description of the signal found, or None.
    """
    if "∀" in text:
        return "explicit ∀ quantifier"

    if re.search(r"for\s+\w+\s+in\s+\[", text):
        return "`for .. in [a:b]` range iteration"

    for m in re.finditer(r"List\.range\s+(\d+)\b", text):
        if int(m.group(1)) > 1:
            return f"List.range {m.group(1)}"

    for m in re.finditer(r"\.\s*(all|any)\b", text):
        prefix = text[:m.start()]
        bracket = re.search(r"(#?\[[^\[\]]*\])\s*$", prefix)
        if bracket:
            contents = bracket.group(1)
            looks_literal = (
                re.fullmatch(r"#?\[\s*[^\[\],]*(?:,\s*[^\[\],]*)*\s*\]", contents) is not None
                and "range" not in contents.lower()
                and ".." not in contents
            )
            if looks_literal:
                continue  # disguised literal-list check; does not corroborate
        if re.search(r"List\.range\s+[01]\b", prefix[-30:]):
            continue  # `.all`/`.any` over a degenerate List.range 0/1; does not corroborate
        return f".{m.group(1)}"

    return None


def check_regression_citations(
    all_decls_by_file: Dict[str, List[Decl]],
    all_lines_by_file: Dict[str, List[str]],
    allowlist: Dict[Tuple[str, str], AllowlistEntry],
) -> List[str]:
    """
    Warning-level heuristic (grep-level): a declaration that is a regression
    check -- allowlisted as `grandfathered`, or `_inst`-suffixed -- should
    not be cited by name inside another declaration's body. Keying on the
    suffix alone let identically-non-compliant grandfathered checks with
    "honest" names dodge the warning; keying on category closes that gap.
    Runs on comment-stripped lines, same as the occurrence scan.
    """
    protected: Dict[str, List[Tuple[str, int]]] = {}
    for rel_path, decls in all_decls_by_file.items():
        for decl in decls:
            if decl.anonymous:
                continue
            is_inst = decl.name.endswith("_inst")
            entry = allowlist.get((rel_path, decl.name))
            is_grandfathered = entry is not None and entry.category == "grandfathered"
            if is_inst or is_grandfathered:
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
    print(f"\n[*] Found {len(occurrences)} Law-10-gated occurrence(s) in source text: "
          f"{native_decide_count} native_decide, {decide_native_count} decide+native/(native := true).")
    print("    (bare `decide` with no native config is unrestricted by Law 10)")

    allowlist, allowlist_errors = load_allowlist()

    has_errors = False

    if allowlist_errors:
        has_errors = True
        print(f"\n[!] FAILED: {len(allowlist_errors)} allowlist integrity error(s) in scripts/gate_allowlist.txt:")
        for err in allowlist_errors:
            print(f"    - {err}")

    finite_forall: List[Tuple[Occurrence, str]] = []
    grandfathered: List[Tuple[Occurrence, str]] = []
    unattributable: List[Occurrence] = []
    not_allowlisted: List[Occurrence] = []
    forall_corroboration_failed: List[Tuple[Occurrence, str]] = []
    matched_allowlist_keys = set()

    for occ in occurrences:
        if occ.decl is None or occ.decl.anonymous:
            unattributable.append(occ)
            continue

        key = (occ.file, occ.decl.name)
        allow_entry = allowlist.get(key)

        if allow_entry is None:
            not_allowlisted.append(occ)
            continue

        matched_allowlist_keys.add(key)

        if allow_entry.category == "finite-forall":
            lines = all_lines_by_file.get(occ.file, [])
            statement_text = "\n".join(lines[occ.decl.line - 1: occ.line])
            signal = corroboration_signal(statement_text)
            if signal:
                finite_forall.append((occ, allow_entry.justification))
            else:
                forall_corroboration_failed.append((occ, allow_entry.justification))
        else:
            # `grandfathered` and `axiom-only` occurrences (an `axiom-only`
            # entry should never actually be hit by a text occurrence, by
            # construction, but if one somehow is, treat it like any other
            # allowlisted single-vector check rather than erroring).
            grandfathered.append((occ, allow_entry.justification))

    # `axiom-only` entries exist purely for Tools/CheckGatesAxioms.lean and
    # are, by construction, never matched by a text-level occurrence here --
    # exempt them from stale-entry detection.
    stale_entries = sorted(
        key for key in allowlist.keys()
        if key not in matched_allowlist_keys and allowlist[key].category != "axiom-only"
    )
    axiom_only_entries = sorted(
        key for key, entry in allowlist.items() if entry.category == "axiom-only"
    )

    print("\n--- LAW 10 GATE CHECK (pre-check) ---")

    any_gate_failure = bool(unattributable or not_allowlisted or forall_corroboration_failed or stale_entries)

    if unattributable:
        has_errors = True
        print(f"\n[!] FAILED: {len(unattributable)} occurrence(s) cannot be unambiguously attributed")
        print("    to a named declaration (anonymous `example`, unresolved `set_option/open/")
        print("    variable ... in` prefix, or no enclosing declaration at all) -- attribution")
        print("    never falls back to an earlier, unrelated declaration:")
        for occ in unattributable:
            decl_desc = occ.decl.name if occ.decl else "<no enclosing declaration>"
            print(f"    - {occ.file}:{occ.line} ({occ.kind}) -- {decl_desc}")

    if not_allowlisted:
        has_errors = True
        print(f"\n[!] FAILED: {len(not_allowlisted)} occurrence(s) are not in scripts/gate_allowlist.txt:")
        for occ in not_allowlisted:
            print(f"    - {occ.file}:{occ.line} ({occ.kind}) in '{occ.decl.name}'")
        print("    -> Add a `<file>::<decl>::<fqn>::finite-forall|grandfathered::<justification>` entry.")

    if forall_corroboration_failed:
        has_errors = True
        print(f"\n[!] FAILED: {len(forall_corroboration_failed)} `finite-forall` allowlist entr(y/ies) fail")
        print("    even the shallow syntactic sanity check (no ∀ / `for..in [a:b]` / `List.range N>1` /")
        print("    non-literal `.all`/`.any` found between the declaration header and the occurrence line):")
        for occ, justification in forall_corroboration_failed:
            print(f"    - {occ.file}:{occ.line} ({occ.decl.name}) -- allowlisted justification: {justification}")

    if stale_entries:
        has_errors = True
        print(f"\n[!] FAILED: {len(stale_entries)} allowlist entr(y/ies) do not match any current occurrence")
        print("    (stale entries are a hard failure, not a note -- prune them; `axiom-only` entries")
        print("    are exempt from this check by construction):")
        for file_path, decl_name in stale_entries:
            print(f"    - {file_path}::{decl_name}")

    if not any_gate_failure:
        print("[+] Every native_decide/decide+native occurrence found in source text is attributed")
        print("    to a named declaration with a valid, matching scripts/gate_allowlist.txt entry.")

    print("\n--- FINITE-FORALL (shallow syntactic check passed -- not a proof) ---")
    print(f"[+] {len(finite_forall)} occurrence(s):")
    for occ, justification in finite_forall:
        print(f"    - {occ.file}:{occ.line} ({occ.decl.name}) -- {justification}")

    print("\n--- GRANDFATHERED (migration backlog, visible) ---")
    print(f"[i] {len(grandfathered)} occurrence(s) predate Law 10 and remain single-vector checks:")
    for occ, justification in grandfathered:
        print(f"    - {occ.file}:{occ.line} ({occ.decl.name}) -- {justification}")

    if axiom_only_entries:
        print("\n--- AXIOM-ONLY (Tools/CheckGatesAxioms.lean's entries; invisible to this pre-check) ---")
        print(f"[i] {len(axiom_only_entries)} entr(y/ies):")
        for file_path, decl_name in axiom_only_entries:
            print(f"    - {file_path}::{decl_name}")

    print("\n--- REGRESSION-CHECK CITATION HEURISTIC (warning only) ---")
    citation_warnings = check_regression_citations(all_decls_by_file, all_lines_by_file, allowlist)
    if citation_warnings:
        print(f"[!] WARNING: {len(citation_warnings)} possible citation(s) of grandfathered/`_inst`")
        print("    regression declarations from other declarations' bodies:")
        for w in citation_warnings:
            print(w)
    else:
        print("[+] No grandfathered or `_inst`-suffixed regression declaration appears to be")
        print("    cited by name inside any other declaration's body.")

    print("\n" + "=" * 70)
    print(f" SUMMARY: {len(occurrences)} Law-10-gated occurrence(s) found in source text "
          f"({native_decide_count} native_decide, {decide_native_count} decide+native/(native := true)).")
    print(f"          {len(finite_forall)} finite-forall (shallow check passed)")
    print(f"          {len(grandfathered)} grandfathered (migration backlog)")
    print(f"          {len(axiom_only_entries)} axiom-only (defer to Tools/CheckGatesAxioms.lean)")
    print(f"          {len(not_allowlisted)} FAILING: not allowlisted")
    print(f"          {len(unattributable)} FAILING: unattributable")
    print(f"          {len(forall_corroboration_failed)} FAILING: finite-forall corroboration failed")
    print(f"          {len(stale_entries)} FAILING: stale allowlist entries")
    print(f"          {len(citation_warnings)} regression-citation warning(s)")
    print("=" * 70)

    if has_errors:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()

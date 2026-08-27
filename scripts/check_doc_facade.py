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
scripts/check_doc_facade.py - Doc-facade linter for gasm (TC21)

WHY THIS EXISTS (docs/REVIEW.md Law 13, Law 8): a document can assert that some
mechanism enforces something while nothing in the tree actually verifies the
assertion. That is more dangerous than an absent gate -- it manufactures
confidence. The 2026-08-27 adversarial review round found four instances of
exactly this in one pass: `progressProof` cited as an existing liveness
obligation (docs/REVIEW.md #4.1 item 1) when no contract carries it;
`canonicalizeTrace` described as "implemented as a normalization function"
(docs/SYSTEM_EFFECTS.md #6.3) when the function does not exist anywhere in
`Gasm.Effects` (PA5); `VerifiedReactiveProgram` described as an existing
distinct contract type (docs/EQUIVALENCE_PROOFS.md #1.1) when it is a ratified
design with no implementation (PA7); and a `MemoryPerm`-fail-to-assemble claim
(Law 11) stated as enforced when zero modules are migrated to the
capability-authoring path (PA4). Three of these four were fixed, in this same
review round, by adding an explicit "Status" sentence next to the claim
(implemented / ratified-design-pending-implementation / tracked as `PA#`) --
this linter is what makes that pattern load-bearing rather than a one-time
hand audit. Running this tool against the tree while building it found that
the fourth (`progressProof`) had NOT actually been fixed -- see "FINDINGS
AGAINST THE CURRENT TREE" below.

CONCURRENT-WORK SAFETY (read this before tightening any pattern below): a
Linux target team is, as this linter ships, writing brand-new design
documents under docs/TARGETS/ for machinery that does not exist yet -- that is
completely legitimate (Law 5: design MUST precede implementation) and MUST NOT
be flagged. The distinction this tool enforces is never "does this exist yet"
-- it is "does this document claim enforcement that nothing provides,
without saying so." The escape hatch is the `**Status**:` convention Law 9
ratified (also: "tracked as `PA#`/`TC#`/`N#`/...", "ratified design", "not yet
implemented", "design-only", "does not yet exist", "fully designed but
dormant" -- see STATUS_MARKER_RE) -- CONTRIBUTING.md now documents it
prominently for exactly this reason. Every trigger pattern below was tuned
empirically against the full current docs/ tree (including the
still-in-progress docs/TARGETS/*.md and docs/GRAPHICS_ARCHITECTURE.md design
docs) specifically to confirm it does not fire on ordinary forward-looking
design prose; see the two "WHY THIS SHAPE, NOT A BROADER ONE" notes below.

WHAT THIS CHECKS (two defect shapes; a third candidate shape was evaluated and
REJECTED -- see "REJECTED SHAPES" below):

1. MECHANISM_ABSENT -- a backtick-quoted, Lean-identifier-shaped token appears
   within ~80 characters of an enforcement-claim phrase ("MUST"/"must",
   "is implemented as/in/by", "is specified as", "already/currently
   implements", "is currently enforced", "carries", "enforces"/"enforced",
   "guarantees", "is realized as") on the SAME LINE (this repository's prose
   is not hard-wrapped; a markdown "sentence" is reliably one physical line --
   see the module for the empirical check that motivated line-scoping over
   paragraph-scoping), the identifier does not appear anywhere in the `.lean`
   tree (any token occurrence, not just a declaration site -- deliberately
   lenient, see IDENTIFIER PRESENCE below), and no `**Status**:`-shaped escape
   marker appears anywhere in the same blank-line-delimited paragraph.

   WHY THIS SHAPE, NOT A BROADER ONE (the false positive that shaped this
   design): an earlier draft paired ANY backtick identifier with a MUST/must
   anywhere in the same PARAGRAPH. Tested against the live tree, this
   immediately mis-flagged `` `warningAsError` `` in docs/REVIEW.md #4.1 item 4
   -- a real, existing lakefile.toml key mentioned in an aside 30+ words away
   from that paragraph's actual "must be allowlisted" clause, which belongs to
   a different sentence entirely. Requiring same-LINE proximity (not
   paragraph) and requiring the trigger phrase to appear BEFORE the
   identifier (not merely nearby) eliminates that class: a parenthetical
   naming its own claimed mechanism (`` (`Identifier`) ``, `` `X` is
   implemented as `Identifier` ``) is a narrow, rare, and specific shape, and
   grep-testing the trigger+proximity pattern against every file under docs/
   found exactly the three real instances documented in FINDINGS below --
   zero incidental collisions.

2. GATE_SCRIPT_MISSING / GATE_NOT_WIRED -- scoped to docs/REVIEW.md only (the
   authoritative gate registry; see #4.1.1's own words: "so that Pillar 1's
   'gate policy compliance' line is a citable specification"). A line
   containing a gate-registration phrase ("must return exit code 0", "must
   exit 0", "must exit code 0", "must pass", "must also pass/exit/return",
   "**Gate**:") and a backtick-quoted `scripts/*.py|*.sh|*.ps1` path or
   `lake exe <name>` mention is checked two ways: does the script/exe exist on
   disk at all (GATE_SCRIPT_MISSING if not -- the `check_calibration.py`
   case), and if it exists, does it appear wired into
   `scripts/run_gates.py`'s GATE_TABLE (a literal-substring check against that
   script's own source text) or, for a `lake exe` target, into both
   `lakefile.toml`'s `[[lean_exe]]` list and `run_gates.py`'s table
   (GATE_NOT_WIRED if not -- the `check_licenses.py`-was-never-wired-in case,
   discovered this week). Same `**Status**:`-style escape, same paragraph
   scope (an already-disclosed gap, like `check_calibration.py`'s own "not
   yet implemented and not yet registered" sentence, is not re-reported).

   WHY SCOPED TO docs/REVIEW.md ONLY: other docs mention utility scripts
   (`scripts/task_frontier.py`, `scripts/migrate_intel_sdm_refs.py`,
   `scripts/fuzz_gzip.py`) that are legitimately not part of the automated
   merge-gate table -- they are one-off tools, not claimed gates. Applying
   this check tree-wide would flag every such mention as "not wired,"
   which is not a defect; docs/REVIEW.md #4.1/#4.1.1 is the one place in the
   tree that specifically claims "X is a required, registered gate," so it is
   the one place where "claimed as a gate but not wired" is a real drift.

IDENTIFIER PRESENCE (the absence test underlying check 1): an identifier
"exists in the tree" if it appears as a token ANYWHERE in any `.lean` file's
text -- not restricted to a declaration site. This is deliberately the most
lenient plausible reading of "exists," chosen to keep false positives near
zero: it was verified, for every identifier this project's own Law text names
as an illustrative example (`MemoryPerm`, `VirtualAlloc`, `fetchPages`,
`PageSource`, `sorryAx`, `ofReduceBool`, `ofReduceNat`, `check_gates_axioms`,
`check_refs_coverage`, ...), that each one really does appear somewhere in the
`.lean` tree's text (a usage comment, a docstring, a real declaration) -- so
this check only ever fires on a name that is TRULY unmentioned in code
anywhere, exactly the `progressProof`/`canonicalizeTrace`/
`VerifiedReactiveProgram` shape. The cost of this leniency is a small
false-negative risk (an identifier mentioned only in an unrelated comment
would count as "present"); that is an accepted, documented trade in the
precision direction Law 13 and this task both prioritize.

IDENTIFIER CANDIDATE FILTER: a backtick span counts as a "Lean-identifier
candidate" only if it is a single bare token (no `/`, no `.`, no spaces --
this alone excludes every file path, command line, and multi-word phrase) AND
either mixes upper- and lower-case letters, or contains an underscore next to
a lowercase letter. This excludes bare English words (`free`, `read`),
Lean keywords (`instance`, `abbrev`, `initialize` -- all lowercase, no
underscore), and task/decision IDs (`PA5`, `TC21`, `D23` -- uppercase+digits,
no lowercase letter), while keeping CamelCase/lowerCamelCase Lean identifiers
and snake_case tool/tactic names.

REJECTED SHAPE: "a quantified enforcement claim ('100%', 'every', 'all',
'zero') about something a gate is supposed to establish, without a verifiable
binding to that gate." This is NOT implemented here, for two reasons. First,
`scripts/check_record.py`'s UNVERIFIED_COMPLETENESS_CLAIM check already scans
`docs/REVIEW.md` (it is in that tool's CORE_DOC_FILES) for exactly this
phrase-shaped claim; a second, near-duplicate implementation in this file
would itself be the Law 12 "unlinked twins" defect this project's own Laws
prohibit. Second, and more fundamentally: verifying that a claim like "100%
citation validity" is actually TRUE (as opposed to merely paired with a
plausible-looking nearby citation) requires re-running the cited gate and
semantically checking its output against the claim -- exactly the kind of
check `check_record.py`'s own module docstring admits it cannot do ("this
check is inherently a heuristic phrase-match, not a semantic verifier"). A
prose linter cannot mechanically distinguish "100%, verified" from "100%,
silently wrong" (the precise defect docs/REVIEW.md #4.1.2 documents already
happened once) without executing and interpreting the gate itself, which is
out of scope for a static text check. Reported as a named limitation, not
implemented, per this task's explicit instruction to reject what cannot be
made precise.

REJECTED SHAPE (the `MemoryPerm` case, specifically): "a document names an
identifier that DOES exist, but the enforcement/usage level it claims (e.g.
'MUST fail to assemble') is not actually realized because nothing in the tree
exercises the capability path that identifier represents." This is
structurally undetectable by presence/absence text matching -- `MemoryPerm`
is a completely real `structure` in `Gasm/Core/Permissions.lean`, so any
identifier-existence check is (correctly) silent on it. Catching this class
would require a semantic usage census (how many modules actually route
memory-touching instructions through the capability-authoring path today, and
does that count match what the claim implies) -- a different, much harder
kind of tool than a doc-facade prose linter, and one this task's "reject what
you cannot make precise" instruction covers directly. `docs/REVIEW.md` Law 11
already carries this project's manual fix for the one known instance (an
explicit `**Status**:` sentence); no mechanical prevention for the general
class is implemented here.

REJECTED SHAPE: "a legal or status file asserts a property of the tree that
can be checked directly against the tree" (the `NOTICE` case). This is
already bound, for the one concrete instance that motivated it, by
`scripts/check_publishable.py`. Generalizing it further would require a
bespoke check PER CLAIM (there is no single mechanical pattern for "this
English sentence about `NOTICE` corresponds to this specific tree property"
that would not also match countless unrelated sentences) -- rejected as
too bespoke to generalize into a linter rule.

ALLOWLIST: scripts/doc_facade_allowlist.txt, 5 `::`-delimited fields (same
shape as every other allowlist in this repository):

    <check>::<key>::<added>::<added-by>::<justification>

`<check>` is one of `mechanism-absent`, `gate-script-missing`,
`gate-not-wired`. `<key>` is `<file>:<line>:<token>` for every check (the
file relative to the repo root, the 1-based line number after fenced-code-
block stripping, and the flagged identifier/script/exe name -- unique because
a single line can name more than one candidate). A line with any other field
count, an unknown check name, an empty key, or an empty justification is a
hard parse failure -- never a silently-skipped line, matching every other
Law-10-style allowlist in this repository. A stale entry (its (check, key) no
longer trips anything) is also a hard failure, same discipline as
`scripts/check_record.py`.

Usage:
    python scripts/check_doc_facade.py            # full report (default)
    python scripts/check_doc_facade.py --json      # machine-readable JSON
    python scripts/check_doc_facade.py --self-test # plant/verify/revert each
                                                     # check; re-runnable
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if sys.stderr.encoding and sys.stderr.encoding.lower() not in ("utf-8", "utf8"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = REPO_ROOT / "docs"
REVIEW_MD = DOCS_DIR / "REVIEW.md"
RUN_GATES_PY = REPO_ROOT / "scripts" / "run_gates.py"
LAKEFILE_TOML = REPO_ROOT / "lakefile.toml"
ALLOWLIST_PATH = REPO_ROOT / "scripts" / "doc_facade_allowlist.txt"

VALID_ALLOWLIST_CHECKS = {"mechanism-absent", "gate-script-missing", "gate-not-wired"}

# --- Identifier candidate filter -------------------------------------------------

IDENT_TOKEN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def _looks_like_lean_identifier(tok: str) -> bool:
    if len(tok) < 3 or not IDENT_TOKEN_RE.match(tok):
        return False
    has_upper = any(c.isupper() for c in tok)
    has_lower = any(c.islower() for c in tok)
    has_us = "_" in tok
    return (has_upper and has_lower) or (has_us and has_lower)


# --- .lean tree token presence (lenient: any token occurrence, not just decls) ---

LEAN_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_LEAN_TOKENS: Optional[Set[str]] = None


def _lean_tokens() -> Set[str]:
    global _LEAN_TOKENS
    if _LEAN_TOKENS is None:
        tokens: Set[str] = set()
        for p in REPO_ROOT.rglob("*.lean"):
            parts = set(p.parts)
            if ".git" in parts or ".lake" in parts:
                continue
            try:
                text = p.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError):
                continue
            tokens.update(LEAN_WORD_RE.findall(text))
        _LEAN_TOKENS = tokens
    return _LEAN_TOKENS


def _identifier_in_lean_tree(ident: str) -> bool:
    return ident in _lean_tokens()


# --- Doc file scoping: docs/*.md recursively, excluding docs/adr/ and docs/tasks/ -

def iter_scanned_docs() -> List[Path]:
    if not DOCS_DIR.is_dir():
        return []
    out = []
    for p in sorted(DOCS_DIR.rglob("*.md")):
        rel = p.relative_to(DOCS_DIR).as_posix()
        if rel.startswith("adr/") or rel.startswith("tasks/"):
            continue
        out.append(p)
    return out


def _strip_fenced_code_blocks(text: str) -> str:
    """Blank out ``` ... ``` fenced blocks (mermaid diagrams, ASCII art, example
    code) while preserving line count, so line numbers stay accurate and a
    literal backtick or the word "must" inside a diagram/example is never
    mistaken for prose making a claim."""
    lines = text.splitlines(keepends=True)
    out = []
    in_fence = False
    for line in lines:
        if line.strip().startswith("```"):
            in_fence = not in_fence
            out.append("\n" if line.endswith("\n") else "")
            continue
        if in_fence:
            out.append("\n" if line.endswith("\n") else "")
        else:
            out.append(line)
    return "".join(out)


# --- The Status-marker escape hatch (Law 9's ratified convention) ---------------

STATUS_MARKER_RE = re.compile(
    r"\*\*Status\*\*:"
    r"|tracked as `?(?:PA|TC|N|F|G|B|M|OS)\d+"
    r"|ratified design"
    r"|not yet implemented"
    r"|does not yet exist"
    r"|design-only"
    r"|fully designed but dormant"
    r"|pending implementation"
    r"|implementation tracked as"
    r"|not yet registered"
    r"|untracked backlog"
    r"|not yet assigned a task",
    re.IGNORECASE,
)


ITEM_START_RE = re.compile(r"^(\s*)(?:[-*]\s|\d+\.\s)")


def _item_bounds(lines: List[str], line_no: int) -> Optional[Tuple[int, int]]:
    """Bounds of the single bulleted/numbered list item containing line_no, as
    (start_line, end_line), 1-based inclusive -- or None if line_no is not
    inside one (e.g. plain paragraph prose). Deliberately narrower than "the
    whole blank-line-delimited paragraph": this document's #4.1 Pillar 1 list
    has NO blank lines between items 1-8, so a paragraph-wide escape lookup
    let item 4's unrelated "closure-coverage completion is tracked as TC15"
    incorrectly suppress a finding about `progressProof` in item 1 -- found by
    actually running this tool against the tree while building it (see module
    docstring). Scoping to one list item at a time (stopping the backward
    search at the first blank line, so it never leaks across paragraphs or
    sections either) fixes that while still covering every real fix in the
    tree today: each is a Status marker on the SAME bulleted item as its
    claim (`check_calibration.py`'s spans several wrapped continuation lines
    of one `- ` item, which this still captures in full)."""
    start = None
    indent = None
    for j in range(line_no, 0, -1):
        cur = lines[j - 1]
        if cur.strip() == "" and j != line_no:
            break
        m = ITEM_START_RE.match(cur)
        if m:
            start = j
            indent = len(m.group(1))
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start + 1, len(lines) + 1):
        line = lines[j - 1]
        if line.strip() == "":
            end = j - 1
            break
        m2 = ITEM_START_RE.match(line)
        if m2 and len(m2.group(1)) <= indent:
            end = j - 1
            break
    return (start, end)


def _escape_window(lines: List[str], line_no: int) -> Tuple[int, int]:
    """The window a Status-marker escape is searched in for a claim on
    line_no: the enclosing list item if there is one (see _item_bounds),
    otherwise a small fixed window around the line -- generous enough to
    cover the two known plain-prose instances (`canonicalizeTrace`,
    `VerifiedReactiveProgram`), both of which carry their Status marker on
    the very same line as the claim, but narrow enough not to reach into an
    unrelated neighboring paragraph."""
    bounds = _item_bounds(lines, line_no)
    if bounds is not None:
        return bounds
    lo = max(1, line_no - 4)
    hi = min(len(lines), line_no + 4)
    return (lo, hi)


def _has_status_escape(lines: List[str], start: int, end: int) -> bool:
    window = "\n".join(lines[start - 1:end])
    return bool(STATUS_MARKER_RE.search(window))


# --- Finding -----------------------------------------------------------------

class Finding:
    __slots__ = ("check", "detail", "allowlisted")

    def __init__(self, check: str, detail: str, allowlisted: bool = False):
        self.check = check
        self.detail = detail
        self.allowlisted = allowlisted


# --- Allowlist ------------------------------------------------------------------

class AllowlistEntry:
    __slots__ = ("check", "key", "added", "added_by", "justification", "line_num")

    def __init__(self, check, key, added, added_by, justification, line_num):
        self.check = check
        self.key = key
        self.added = added
        self.added_by = added_by
        self.justification = justification
        self.line_num = line_num


def load_allowlist() -> Tuple[Dict[Tuple[str, str], AllowlistEntry], List[str]]:
    entries: Dict[Tuple[str, str], AllowlistEntry] = {}
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
                f"doc_facade_allowlist.txt:{line_num}: expected 5 '::'-delimited "
                f"fields (check::key::added::added_by::justification), got {len(parts)}: {raw_line!r}"
            )
            continue
        check, key, added, added_by, justification = (p.strip() for p in parts)
        if check not in VALID_ALLOWLIST_CHECKS:
            errors.append(
                f"doc_facade_allowlist.txt:{line_num}: unknown check '{check}' "
                f"(expected one of {sorted(VALID_ALLOWLIST_CHECKS)})"
            )
            continue
        if not key:
            errors.append(f"doc_facade_allowlist.txt:{line_num}: empty key")
            continue
        if not justification:
            errors.append(f"doc_facade_allowlist.txt:{line_num}: missing justification")
            continue
        dup_key = (check, key)
        if dup_key in entries:
            errors.append(
                f"doc_facade_allowlist.txt:{line_num}: duplicate entry for "
                f"'{check}::{key}' (first defined at line {entries[dup_key].line_num}) -- "
                f"duplicates are a hard error, not silent last-wins"
            )
            continue
        entries[dup_key] = AllowlistEntry(check, key, added, added_by, justification, line_num)

    return entries, errors


# --- CHECK 1: MECHANISM_ABSENT ---------------------------------------------------

TRIGGER_WORDS = r"must|implemented|enforces|enforced|carries|guarantees|realized"
PAREN_CITE_RE = re.compile(
    r"\b(?:%s)\b.{0,80}?\(\s*`([A-Za-z_][A-Za-z0-9_']*)`" % TRIGGER_WORDS,
    re.IGNORECASE,
)
PRESENT_CLAIM_RE = re.compile(
    r"\b(?:is implemented as|is implemented in|is implemented by|is specified as|"
    r"already implements|currently implements|is currently enforced|is realized as)\b"
    r".{0,80}?`([A-Za-z_][A-Za-z0-9_']*)`",
    re.IGNORECASE,
)


def _raw_mechanism_absent() -> Dict[str, str]:
    """Maps allowlist key ('<file>:<line>:<ident>') -> human detail, for every
    currently-firing (non-escaped) MECHANISM_ABSENT instance. Shared by the
    live check and the stale-allowlist sweep."""
    out: Dict[str, str] = {}
    for path in iter_scanned_docs():
        rel = path.relative_to(REPO_ROOT).as_posix()
        raw = path.read_text(encoding="utf-8")
        stripped = _strip_fenced_code_blocks(raw)
        lines = stripped.splitlines()
        seen_on_line: Set[Tuple[int, str]] = set()
        for i, line in enumerate(lines, start=1):
            for rx in (PAREN_CITE_RE, PRESENT_CLAIM_RE):
                for m in rx.finditer(line):
                    ident = m.group(1)
                    if not _looks_like_lean_identifier(ident):
                        continue
                    if (i, ident) in seen_on_line:
                        continue
                    seen_on_line.add((i, ident))
                    if _identifier_in_lean_tree(ident):
                        continue
                    s, e = _escape_window(lines, i)
                    if _has_status_escape(lines, s, e):
                        continue
                    key = f"{rel}:{i}:{ident}"
                    out[key] = (
                        f"{rel}:{i}: backtick identifier `{ident}` appears in an "
                        f"enforcement-claim context ({m.group(0)!r}) but does not appear "
                        f"anywhere in the .lean tree, and no adjacent Status marker "
                        f"(lines {s}-{e}) discloses it as designed-not-built."
                    )
    return out


def check_mechanism_absent(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    findings = []
    for key, detail in sorted(_raw_mechanism_absent().items()):
        if ("mechanism-absent", key) in allowlist:
            entry = allowlist[("mechanism-absent", key)]
            findings.append(Finding("MECHANISM_ABSENT", f"{detail} Allowlisted: {entry.justification}", True))
            continue
        findings.append(Finding(
            "MECHANISM_ABSENT",
            f"{detail} Either add a `**Status**:` sentence (docs/REVIEW.md Law 9's "
            f"convention: implemented / ratified design pending implementation, citing "
            f"a tracking task) next to the claim, or add a "
            f"scripts/doc_facade_allowlist.txt entry ('mechanism-absent::{key}::...') "
            f"recording why not."
        ))
    return findings


# --- CHECK 2/3: GATE_SCRIPT_MISSING / GATE_NOT_WIRED (docs/REVIEW.md only) ------

GATE_CLAIM_RE = re.compile(
    r"must return exit code 0|must exit 0|must exit code 0|must pass|"
    r"must also (?:pass|exit|return)|\*\*Gate\*\*:",
    re.IGNORECASE,
)
SCRIPT_MENTION_RE = re.compile(r"`(?:python )?(scripts/[\w./-]+\.(?:py|sh|ps1))(?:\s[^`]*)?`")
EXE_MENTION_RE = re.compile(r"`lake exe ([A-Za-z_][A-Za-z0-9_]*)`")

_RUN_GATES_TEXT: Optional[str] = None
_LAKEFILE_TEXT: Optional[str] = None


def _run_gates_text() -> str:
    global _RUN_GATES_TEXT
    if _RUN_GATES_TEXT is None:
        _RUN_GATES_TEXT = RUN_GATES_PY.read_text(encoding="utf-8") if RUN_GATES_PY.is_file() else ""
    return _RUN_GATES_TEXT


def _lakefile_text() -> str:
    global _LAKEFILE_TEXT
    if _LAKEFILE_TEXT is None:
        _LAKEFILE_TEXT = LAKEFILE_TOML.read_text(encoding="utf-8") if LAKEFILE_TOML.is_file() else ""
    return _LAKEFILE_TEXT


def _raw_gate_claims() -> Dict[str, Tuple[str, str]]:
    """Maps allowlist key ('docs/REVIEW.md:<line>:<name>') -> (check, detail) for
    every currently-firing (non-escaped) GATE_SCRIPT_MISSING/GATE_NOT_WIRED
    instance. Shared by the live check and the stale-allowlist sweep."""
    out: Dict[str, Tuple[str, str]] = {}
    if not REVIEW_MD.is_file():
        return out
    rel = "docs/REVIEW.md"
    raw = REVIEW_MD.read_text(encoding="utf-8")
    stripped = _strip_fenced_code_blocks(raw)
    lines = stripped.splitlines()
    gt_text = _run_gates_text()
    lf_text = _lakefile_text()
    for i, line in enumerate(lines, start=1):
        if not GATE_CLAIM_RE.search(line):
            continue
        for m in SCRIPT_MENTION_RE.finditer(line):
            script = m.group(1)
            key = f"{rel}:{i}:{script}"
            if key in out:
                continue
            if not (REPO_ROOT / script).is_file():
                s, e = _escape_window(lines, i)
                if _has_status_escape(lines, s, e):
                    continue
                out[key] = ("gate-script-missing",
                            f"{rel}:{i}: `{script}` is named as a required gate here, "
                            f"but that file does not exist on disk.")
            elif script not in gt_text:
                s, e = _escape_window(lines, i)
                if _has_status_escape(lines, s, e):
                    continue
                out[key] = ("gate-not-wired",
                            f"{rel}:{i}: `{script}` is named as a required gate here and "
                            f"exists on disk, but is not wired into scripts/run_gates.py's "
                            f"gate table -- a gate that exists but nothing invokes binds "
                            f"nothing.")
        for m in EXE_MENTION_RE.finditer(line):
            exe = m.group(1)
            key = f"{rel}:{i}:{exe}"
            if key in out:
                continue
            exe_defined = f'name = "{exe}"' in lf_text
            exe_wired = f'"exe", "{exe}"' in gt_text
            if not exe_defined:
                s, e = _escape_window(lines, i)
                if _has_status_escape(lines, s, e):
                    continue
                out[key] = ("gate-script-missing",
                            f"{rel}:{i}: `lake exe {exe}` is named as a required gate here, "
                            f"but no `[[lean_exe]] name = \"{exe}\"` target exists in "
                            f"lakefile.toml.")
            elif not exe_wired:
                s, e = _escape_window(lines, i)
                if _has_status_escape(lines, s, e):
                    continue
                out[key] = ("gate-not-wired",
                            f"{rel}:{i}: `lake exe {exe}` is named as a required gate here "
                            f"and the target exists, but is not wired into "
                            f"scripts/run_gates.py's gate table.")
    return out


def check_gate_claims(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    findings = []
    for key, (check, detail) in sorted(_raw_gate_claims().items()):
        check_name = "GATE_SCRIPT_MISSING" if check == "gate-script-missing" else "GATE_NOT_WIRED"
        if (check, key) in allowlist:
            entry = allowlist[(check, key)]
            findings.append(Finding(check_name, f"{detail} Allowlisted: {entry.justification}", True))
            continue
        findings.append(Finding(
            check_name,
            f"{detail} Either wire it into scripts/run_gates.py (and docs/REVIEW.md #4.1's "
            f"enumerated list) in the same change that adds the claim, add a `**Status**:`/"
            f"'not yet registered' disclosure (as scripts/check_calibration.py's own entry "
            f"does), or add a scripts/doc_facade_allowlist.txt entry "
            f"('{check}::{key}::...') recording why not."
        ))
    return findings


# --- Runner -----------------------------------------------------------------------

def run_all() -> Tuple[List[Finding], List[str]]:
    global _LEAN_TOKENS, _RUN_GATES_TEXT, _LAKEFILE_TEXT
    _LEAN_TOKENS = None
    _RUN_GATES_TEXT = None
    _LAKEFILE_TEXT = None

    allowlist, allowlist_errors = load_allowlist()
    findings: List[Finding] = []
    findings.extend(check_mechanism_absent(allowlist))
    findings.extend(check_gate_claims(allowlist))

    raw_mechanism = set(_raw_mechanism_absent().keys())
    raw_gate = _raw_gate_claims()

    for (check, key), entry in allowlist.items():
        if check == "mechanism-absent" and key not in raw_mechanism:
            allowlist_errors.append(
                f"doc_facade_allowlist.txt:{entry.line_num}: entry 'mechanism-absent::{key}' "
                f"is stale -- that claim no longer fires (fixed, or the identifier now "
                f"exists, or a Status marker was added); remove the entry."
            )
        elif check in ("gate-script-missing", "gate-not-wired"):
            hit = raw_gate.get(key)
            if hit is None or hit[0] != check:
                allowlist_errors.append(
                    f"doc_facade_allowlist.txt:{entry.line_num}: entry '{check}::{key}' is "
                    f"stale -- that claim no longer fires that way; remove or update the entry."
                )

    return findings, allowlist_errors


def main():
    parser = argparse.ArgumentParser(description="Doc-facade linter for gasm (TC21)")
    parser.add_argument("--json", action="store_true", help="machine-readable JSON output")
    parser.add_argument("--self-test", action="store_true",
                         help="plant/verify/revert a defect for each check; re-runnable regression test")
    args = parser.parse_args()

    if args.self_test:
        sys.exit(run_self_test(args.json))

    findings, allowlist_errors = run_all()
    blocking = [f for f in findings if not f.allowlisted]
    allowlisted = [f for f in findings if f.allowlisted]
    has_errors = bool(blocking or allowlist_errors)

    by_check: Dict[str, int] = {}
    for f in blocking:
        by_check[f.check] = by_check.get(f.check, 0) + 1

    if args.json:
        out = {
            "ok": not has_errors,
            "blocking_count": len(blocking),
            "by_check": by_check,
            "blocking": [{"check": f.check, "detail": f.detail} for f in blocking],
            "allowlisted": [{"check": f.check, "detail": f.detail} for f in allowlisted],
            "allowlist_errors": allowlist_errors,
        }
        print(json.dumps(out, indent=2))
        sys.exit(1 if has_errors else 0)

    print("=" * 70)
    print(" gasm Doc-Facade Linter (scripts/check_doc_facade.py, TC21)")
    print("=" * 70)
    print("[*] Checks: MECHANISM_ABSENT, GATE_SCRIPT_MISSING, GATE_NOT_WIRED")

    if allowlist_errors:
        has_errors = True
        print(f"\n[!] FAILED: {len(allowlist_errors)} doc_facade_allowlist.txt integrity error(s):")
        for e in allowlist_errors:
            print(f"    - {e}")

    if blocking:
        print(f"\n[!] FAILED: {len(blocking)} blocking finding(s):")
        for check_name, count in sorted(by_check.items()):
            print(f"\n  --- {check_name} ({count}) ---")
            for f in blocking:
                if f.check == check_name:
                    print(f"    - {f.detail}")
    else:
        print("\n[+] No blocking findings.")

    if allowlisted:
        print(f"\n[i] {len(allowlisted)} finding(s) exempted via scripts/doc_facade_allowlist.txt:")
        for f in allowlisted:
            print(f"    - [{f.check}] {f.detail}")

    print("\n" + "=" * 70)
    print(f" SUMMARY: {len(blocking)} blocking, {len(allowlisted)} allowlisted, "
          f"{len(allowlist_errors)} allowlist error(s).")
    print("=" * 70)

    sys.exit(1 if has_errors else 0)


# --------------------------------------------------------------------------------
# --self-test: a RE-RUNNABLE regression test for the gate itself (mirrors
# scripts/check_record.py's / scripts/run_gates.py's pattern exactly: plant a
# defect into the REAL tree, assert the SPECIFIC check goes red, revert, assert
# green again -- with try/finally so a crash mid-test cannot leave the tree
# dirty). A gate only ever seen to pass is untested.
# --------------------------------------------------------------------------------

def _run_check_json() -> Dict:
    findings, allowlist_errors = run_all()
    blocking = [f for f in findings if not f.allowlisted]
    by_check: Dict[str, int] = {}
    for f in blocking:
        by_check[f.check] = by_check.get(f.check, 0) + 1
    return {"by_check": by_check, "allowlist_errors": allowlist_errors}


def _self_test_mechanism_absent() -> Dict:
    original = REVIEW_MD.read_text(encoding="utf-8")
    probe = (
        "\n\n- TC21 --self-test scratch (never committed): this mechanism is "
        "implemented as a validation layer (`TC21SelfTestScratchMechanism`) with "
        "no status marker on purpose.\n"
    )
    try:
        REVIEW_MD.write_text(original + probe, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("MECHANISM_ABSENT", 0) > 0
    finally:
        REVIEW_MD.write_text(original, encoding="utf-8")
    green_after = _run_check_json()["by_check"].get("MECHANISM_ABSENT", 0) == 0
    return {"defect": "mechanism_absent", "check": "MECHANISM_ABSENT",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_gate_script_missing() -> Dict:
    original = REVIEW_MD.read_text(encoding="utf-8")
    probe = (
        "\n\n- TC21 --self-test scratch (never committed): "
        "`python scripts/tc21_selftest_scratch_never_real.py` must return exit "
        "code 0 for this scratch gate-claim control.\n"
    )
    try:
        REVIEW_MD.write_text(original + probe, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("GATE_SCRIPT_MISSING", 0) > 0
    finally:
        REVIEW_MD.write_text(original, encoding="utf-8")
    green_after = _run_check_json()["by_check"].get("GATE_SCRIPT_MISSING", 0) == 0
    return {"defect": "gate_script_missing", "check": "GATE_SCRIPT_MISSING",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_gate_not_wired() -> Dict:
    original = REVIEW_MD.read_text(encoding="utf-8")
    scratch_script = REPO_ROOT / "scripts" / "_tc21_selftest_scratch_gate.py"
    scratch_content = (
        "#!/usr/bin/env python3\n"
        "# TC21 --self-test scratch script (never committed): exists on disk but\n"
        "# deliberately not wired into scripts/run_gates.py's gate table, to prove\n"
        "# GATE_NOT_WIRED fires on a real-but-unwired script.\n"
        "import sys\nsys.exit(0)\n"
    )
    probe = (
        "\n\n- TC21 --self-test scratch (never committed): "
        "`python scripts/_tc21_selftest_scratch_gate.py` must exit 0 for this "
        "scratch gate-wiring control.\n"
    )
    try:
        scratch_script.write_text(scratch_content, encoding="utf-8")
        REVIEW_MD.write_text(original + probe, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("GATE_NOT_WIRED", 0) > 0
    finally:
        REVIEW_MD.write_text(original, encoding="utf-8")
        scratch_script.unlink(missing_ok=True)
    green_after = _run_check_json()["by_check"].get("GATE_NOT_WIRED", 0) == 0
    return {"defect": "gate_not_wired", "check": "GATE_NOT_WIRED",
            "turned_red": red, "green_after_revert": green_after}


def run_self_test(json_mode: bool) -> int:
    if not json_mode:
        print("#" * 100)
        print("# check_doc_facade.py --self-test: re-runnable planted-defect control vectors")
        print("#" * 100)

    results = []
    for label, fn in [
        ("mechanism_absent", _self_test_mechanism_absent),
        ("gate_script_missing", _self_test_gate_script_missing),
        ("gate_not_wired", _self_test_gate_not_wired),
    ]:
        if not json_mode:
            print(f"\n[SELF-TEST] {label} ...")
        r = fn()
        results.append(r)
        if not json_mode:
            ok = r["turned_red"] and r["green_after_revert"]
            print(f"  turned_red={r['turned_red']}  green_after_revert={r['green_after_revert']}  "
                  f"-> {'PASS' if ok else 'FAIL'}")

    all_ok = all(r["turned_red"] and r["green_after_revert"] for r in results)
    overall = "PASS" if all_ok else "FAIL"

    if json_mode:
        print(json.dumps({"self_test": overall, "results": results}, indent=2))
    else:
        print("\n" + "=" * 100)
        print(f" SELF-TEST SUMMARY: {overall}")
        for r in results:
            print(f"  - {r['defect']:<24} check={r['check']:<20} "
                  f"turned_red={r['turned_red']!s:<6} green_after_revert={r['green_after_revert']!s:<6}")
        print("=" * 100)

    return 0 if all_ok else 1


if __name__ == "__main__":
    main()

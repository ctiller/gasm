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

WHAT THIS CHECKS (three defect shapes; three further candidate shapes were evaluated
and REJECTED -- see "REJECTED SHAPES" below):

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

3. THEOREM_FENCE_ABSENT (TC22) -- a ```lean-fenced block DISPLAYS a `theorem`/`lemma`
   declaration header whose declared name is declared NOWHERE in the `.lean` tree, and
   neither the enclosing document section nor the file's own preamble carries a
   `**Status**:`-family disclosure. Checks 1 and 2 both operate on prose with fenced
   blocks STRIPPED (`_strip_fenced_code_blocks`), so a fabricated theorem shown as code
   was structurally invisible to them; this check is the complement. It is the
   highest-value shape in this repository: a displayed theorem carries the visual
   authority of checked code in a project whose whole premise is that displayed theorems
   are real. Two confirmed instances had slipped through -- `docs/TARGETS/X86_64.md` §3's
   `x86_mov_store_is_release` (fixed by hand, 2026-08-28, commit f597a53) and
   `docs/STDLIB_ZLIB.md` §6.2/§6.3's six roundtrip-soundness theorems.

   NAME RESOLUTION -- DECLARATION SITES, NOT TOKEN PRESENCE (the one measured design
   parameter where this check deliberately chooses the stricter interpretation of
   `docs/REVIEW.md` Law 8): the declared name resolves if and only if it
   appears at a DECLARATION SITE in some `.lean` file -- i.e. a line matching
   `<modifiers> (theorem|lemma|def|structure|inductive|abbrev|instance|class|axiom|opaque)
   <name>` -- matched either fully-qualified (namespace-prefixed) or on its final
   dot-component. TC22 proposed reusing check 1's deliberately-lenient "token appears
   anywhere in the `.lean` text" test. Measured against the tree at f597a53, that variant
   finds 18 instances and MISSES `docs/STDLIB_ZLIB.md` §6.2's `deflate_roundtrip_soundness`
   -- because that name appears in four DOC COMMENTS in `Stdlib/Zlib/Equivalence.lean`
   (:220, :361, :1523, :1883) naming it as the open universal obligation, and nowhere as a
   declaration. A name that the source tree itself describes as not-yet-proven is the
   single worst false negative this check could have, so token presence is rejected here.
   Declaration-site resolution finds 19: the same 18 plus that one. The cost of the
   stricter test is one extra false-positive class -- a doc legitimately displaying a
   Mathlib/core theorem this repository does not itself declare -- which measured zero
   instances in the current corpus and is handled by the allowlist if one appears. (Checks
   1 and 2 keep token presence: they scan PROSE, where a mention in a comment really does
   mean the identifier is not fabricated.)

   WHAT THIS CHECK CANNOT CATCH, deliberately and by construction:
   - **A name that exists but with a DIFFERENT STATEMENT.** This is real and out of scope.
     `docs/STDLIB_ZLIB.md` §6.2's fabricated block was wrong twice over: the names did not
     exist, AND the displayed signatures returned `some data` where every real function in
     `Stdlib/Zlib` returns `Except ZlibError`. A textual linter cannot compare a displayed
     Lean type against an elaborated one; only querying the compiled environment could, and
     that is rejected below. Reviewers, not this gate, own statement fidelity.
   - **Hypotheses silently dropped or added.** Same reason: `compress_roundtrip_of_fixed_choice`
     carries a bit-cost precondition that a doc could omit while keeping the name; this
     check would stay green.
   - **`def`/`structure`/`inductive`/`abbrev`/`class` headers.** Restricted to
     `theorem`/`lemma` on measurement: the all-declaration-kinds variant fires 66 times
     across the corpus, essentially all of them legitimate design sketches
     (`docs/MEMORY_HOOK.md`'s `RegionSpec`/`MemCostModel`, `docs/TARGETS/ARM.md`,
     `docs/SOFTWARE_MODELING_SDLC.md`'s worked examples). A gate at that noise level would
     be turned off, and sketching a proposed data type is not the defect being prevented --
     displaying a proof that does not exist is.

   WHY NOT QUERY THE COMPILED ENVIRONMENT (the more precise alternative, rejected): a
   `lake env lean` probe that `#check`s each displayed name would resolve names exactly,
   see through `export`/`open`/aliases, and could in principle compare statements. It is
   rejected because it couples a doc linter to a WORKING BUILD of a large Lean project:
   this gate would then fail red whenever the tree does not compile -- precisely when
   documentation drift is most likely and an always-runnable prose check is most useful --
   and it would replace a pure text scan (one `git ls-files`, one pass over the `.lean`
   text, no toolchain) with an elaboration of the whole environment. Grepping declaration
   sites is cheap, deterministic, build-independent, and (measured above) catches both
   known instances. The trade accepted is the statement-fidelity blind spot named above.

   ESCAPES, in the order tried (the current implementation of the Law 8 disclosure
   policy):
   (a) SECTION-SCOPED: a `**Status**:`-family marker (STATUS_MARKER_RE) anywhere in the
       enclosing document section -- from the nearest preceding `#`-heading line through
       the line before the next heading -- OR in any ANCESTOR section's intro prose (a
       marker on `## 4` discloses for `### 4.1`..`### 4.3`; see
       `_section_escape_windows`). Deliberately covers text BOTH before and after the
       block, because that is the shape the project's own hand-fix used: commit f597a53
       retired the `x86_mov_store_is_release` block and put its `**Status**:` disclosure
       in the paragraph that followed where the block had been.
   (b) FILE-LEVEL DESIGN DECLARATION: an explicit `**Status**:`-led LINE in the file's
       PREAMBLE -- everything from the start of the file through the end of its first
       `##`-level section. This escape exists because measurement showed the section-scoped
       escape alone rescues almost none of the legitimate cases: design documents in this
       repository disclose their nature ONCE, at file level (`docs/MEMORY_HOOK.md` §1
       "Status and scope": "this is a design document, not a report of built machinery"),
       not per section. Law 9's paragraph-scoped convention, which checks 1 and 2 rely on,
       simply does not transfer to a document whose every fenced block is aspirational.
       Note this escape uses FILE_STATUS_MARKER_RE, deliberately STRICTER than the
       section escape's STATUS_MARKER_RE -- see that constant for the measured false
       negative (`docs/EQUIVALENCE_PROOFS.md`) that forced the distinction.
   (c) ALLOWLIST: `scripts/doc_facade_allowlist.txt`, check name `theorem-fence-absent`.
       Used for the cases where neither marker would be HONEST -- a pedagogical worked
       example (`docs/SOFTWARE_MODELING_SDLC.md`'s `get_after_put`) or a syntax
       illustration over a placeholder name (`docs/READ_BINDER_CONTRACT.md`'s
       `foo_correct`) is not a "design pending implementation", and stamping a design
       Status on it would be a second, subtler doc-facade defect.

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
underscore), and task/decision-shaped IDs (`PA5`, `TC21`, `Q23` -- uppercase+digits,
no lowercase letter), while keeping CamelCase/lowerCamelCase Lean identifiers
and snake_case tool/tactic names.

REJECTED SHAPE: "a quantified enforcement claim ('100%', 'every', 'all',
'zero') about something a gate is supposed to establish, without a verifiable
binding to that gate." A retired gate attempted to detect this with phrase
matching, but the approach was not a semantic verifier and is deliberately not
reintroduced here. Verifying that a claim like "100%
citation validity" is actually TRUE (as opposed to merely paired with a
plausible-looking nearby citation) requires re-running the cited gate and
semantically checking its output against the claim -- exactly the kind of
check a static phrase matcher cannot do. A
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
longer trips anything) is also a hard failure, the same mutation-tested
discipline used by the other live gates.

Usage:
    python scripts/check_doc_facade.py            # full report (default)
    python scripts/check_doc_facade.py --json      # machine-readable JSON
    python scripts/check_doc_facade.py --self-test # plant/verify/revert each
                                                     # check; re-runnable
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if sys.stderr.encoding and sys.stderr.encoding.lower() not in ("utf-8", "utf8"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent


def git_tracked_files() -> List[str]:
    """Every git-tracked file path (POSIX, relative to REPO_ROOT), via
    `git ls-files -z` -- never a filesystem walk. See scripts/check_gates.py's
    identically-named helper for the full rationale: this is what makes an
    untracked nested worktree checkout (e.g. `.claude/worktrees/agent-*/`)
    structurally impossible to pick up, rather than merely excluded by name.
    Without this, a nested worktree copy's `.lean` text could make this
    linter's identifier-presence check falsely believe a claimed-but-absent
    identifier "exists in the tree" -- a false NEGATIVE that would hide a
    real doc-facade defect, which is worse than the noisy false positive the
    other affected gates in this repo produce. Fails loudly (exits 1) if git
    is unavailable -- never falls back to a filesystem walk."""
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z"], cwd=REPO_ROOT,
            capture_output=True, timeout=30,
        )
    except (FileNotFoundError, OSError) as e:
        print(f"[!] FATAL: 'git' is not available or could not be run ({e}). File "
              f"enumeration for this gate depends on 'git ls-files' -- refusing to fall "
              f"back to a filesystem walk (that would silently reintroduce the "
              f"nested-worktree false-negative bug this enumeration exists to prevent).",
              file=sys.stderr)
        sys.exit(1)
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
        print(f"[!] FATAL: 'git ls-files' exited {proc.returncode}: {stderr}", file=sys.stderr)
        sys.exit(1)
    raw = proc.stdout.decode("utf-8", errors="replace")
    return [p for p in raw.split("\0") if p]
DOCS_DIR = REPO_ROOT / "docs"
REVIEW_MD = DOCS_DIR / "REVIEW.md"
RUN_GATES_PY = REPO_ROOT / "scripts" / "run_gates.py"
LAKEFILE_TOML = REPO_ROOT / "lakefile.toml"
ALLOWLIST_PATH = REPO_ROOT / "scripts" / "doc_facade_allowlist.txt"

VALID_ALLOWLIST_CHECKS = {"mechanism-absent", "gate-script-missing", "gate-not-wired",
                          "theorem-fence-absent"}

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
        for rel in git_tracked_files():
            if not rel.endswith(".lean"):
                continue
            p = REPO_ROOT / rel
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


# --- Doc file scoping: docs/*.md recursively, excluding legacy process-record subtrees -

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


# --- CHECK 3: THEOREM_FENCE_ABSENT (TC22) --------------------------------------

# Declaration-header shape, shared by BOTH sides of this check: the .lean-tree census that
# builds the set of names that really are declared, and the doc-side scan that finds what a
# fenced block claims. Using one regex for both is deliberate -- the two sides can never
# drift into disagreeing about what "a declaration header" looks like.
DECL_KEYWORDS = ("theorem", "lemma", "def", "structure", "inductive", "abbrev",
                 "instance", "class", "axiom", "opaque")
_DECL_MODIFIERS = (r"(?:@\[[^\]]*\]\s*)*"
                   r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local|nonrec)\s+)*")
# Lean identifiers routinely carry Greek letters, subscripts and primes; `!`/`?` are legal
# trailing characters (`get!`, `digitBytesToNat?`). Dots are allowed so a fully-qualified
# header (`Stdlib.Http11.foo`) or a `where`-block child (`decodeDynamicTables.go`) parses.
_IDENT_CHARS = r"[A-Za-z_Α-ωᵢ-ᵪ][A-Za-z0-9_'!?Α-ω₀-₉ᵢ-ᵪ.]*"
DECL_HEADER_RE = re.compile(
    r"^\s*" + _DECL_MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\s+(" + _IDENT_CHARS + r")"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w'.]*)")
END_RE = re.compile(r"^\s*end\b")

# ```lean / ```lean4 opening fence (case-insensitive); the closing fence is any ``` line.
LEAN_FENCE_OPEN_RE = re.compile(r"^\s*```+\s*(lean4?)\s*$", re.IGNORECASE)
FENCE_ANY_RE = re.compile(r"^\s*```")
HEADING_RE = re.compile(r"^\s{0,3}#{1,6}\s")
H2_RE = re.compile(r"^\s{0,3}##\s")

_LEAN_DECL_NAMES: Optional[Set[str]] = None


def _lean_declared_names() -> Set[str]:
    """Every name DECLARED in the tracked `.lean` tree, in both its bare form and (when
    inside a `namespace`) its fully-qualified form. See the module docstring's "NAME
    RESOLUTION -- DECLARATION SITES, NOT TOKEN PRESENCE" note for why check 3 uses this
    and not `_lean_tokens()`: `deflate_roundtrip_soundness` is a token in four doc
    comments in Stdlib/Zlib/Equivalence.lean and a declaration in none of them, and it is
    exactly the fabricated theorem this check exists to catch.

    The namespace tracker is a plain depth counter over `namespace`/`end`, which is what
    this codebase's files actually use (one `namespace X ... end X` per file, occasionally
    nested). It is deliberately approximate: an over- or under-qualified prefix only ever
    costs a fully-qualified match, and the bare final component is always registered too,
    so the resolution below never becomes stricter than "the name is declared somewhere."
    Anonymous `instance : Foo Bar` headers are skipped (the regex requires a name, and a
    `:`-led header simply does not match)."""
    global _LEAN_DECL_NAMES
    if _LEAN_DECL_NAMES is None:
        names: Set[str] = set()
        for rel in git_tracked_files():
            if not rel.endswith(".lean"):
                continue
            p = REPO_ROOT / rel
            parts = set(p.parts)
            if ".git" in parts or ".lake" in parts:
                continue
            try:
                text = p.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError):
                continue
            ns: List[str] = []
            for line in text.splitlines():
                m_ns = NAMESPACE_RE.match(line)
                if m_ns:
                    ns.append(m_ns.group(1))
                    continue
                if END_RE.match(line) and ns:
                    ns.pop()
                    continue
                m = DECL_HEADER_RE.match(line)
                if not m:
                    continue
                name = m.group(2).rstrip(".")
                if not name:
                    continue
                names.add(name)
                names.add(name.split(".")[-1])
                if ns:
                    names.add(".".join(ns) + "." + name)
        _LEAN_DECL_NAMES = names
    return _LEAN_DECL_NAMES


def _declared_in_lean_tree(name: str) -> bool:
    declared = _lean_declared_names()
    return name in declared or name.split(".")[-1] in declared


def _lean_fence_blocks(lines: List[str]) -> List[Tuple[int, int]]:
    """Every ```lean-fenced block's BODY bounds as (first_body_line, last_body_line),
    1-based inclusive; an unterminated fence runs to end of file. Only fences whose info
    string is exactly `lean`/`lean4` are returned -- a ```text or ```bash block showing
    Lean-looking text is not a claim that the code elaborates."""
    out: List[Tuple[int, int]] = []
    i = 0
    n = len(lines)
    while i < n:
        if LEAN_FENCE_OPEN_RE.match(lines[i]):
            j = i + 1
            while j < n and not FENCE_ANY_RE.match(lines[j]):
                j += 1
            if j > i + 1:
                out.append((i + 2, j))
            i = j + 1
        else:
            i += 1
    return out


def _heading_level(line: str) -> int:
    stripped = line.lstrip()
    n = 0
    while n < len(stripped) and stripped[n] == "#":
        n += 1
    return n


def _next_heading_after(lines: List[str], start: int) -> int:
    """1-based index of the first heading line strictly after `start`, or len+1."""
    for j in range(start + 1, len(lines) + 1):
        if HEADING_RE.match(lines[j - 1]):
            return j
    return len(lines) + 1


def _section_escape_windows(lines: List[str], line_no: int) -> List[Tuple[int, int]]:
    """Every line range a section-scoped `**Status**:` marker may legitimately live in for
    a block at `line_no`, as (start, end) 1-based inclusive:

      * the ENCLOSING section -- nearest preceding heading through the line before the next
        heading. Covers text both BEFORE and AFTER the block deliberately: commit f597a53,
        the project's own hand-fix of the `x86_mov_store_is_release` case, put its
        `**Status**:` disclosure in the paragraph that FOLLOWED where the block had been.
      * each ANCESTOR section's INTRO -- for every heading above it of strictly smaller
        level (`## 4` above `### 4.2`), the range from that heading to the next heading of
        any level. Markdown sections nest and readers read them that way: a `**Status**:`
        on `## 4. The Three Independent Split Theorems` really does disclose for `### 4.1`
        through `### 4.3`, and requiring it to be restated in each subsection would push
        authors toward three copies of one sentence. Only the ancestor's own INTRO prose is
        included, never a sibling subsection's body, so §4.1's text can never suppress a
        finding in §4.2."""
    windows: List[Tuple[int, int]] = []
    start = 1
    level = 0
    for j in range(line_no, 0, -1):
        if HEADING_RE.match(lines[j - 1]):
            start = j
            level = _heading_level(lines[j - 1])
            break
    windows.append((start, _next_heading_after(lines, start) - 1))
    if level:
        cur = level
        for j in range(start - 1, 0, -1):
            if not HEADING_RE.match(lines[j - 1]):
                continue
            lv = _heading_level(lines[j - 1])
            if lv < cur:
                windows.append((j, _next_heading_after(lines, j) - 1))
                cur = lv
                if cur == 1:
                    break
    return windows


# The file-level escape (b) requires a STRICTER marker than the section-level escape (a):
# an explicit `**Status**:`-led LINE, not any member of STATUS_MARKER_RE's loose phrase
# family. Measured reason: STATUS_MARKER_RE applied to a whole preamble mis-rescued
# `docs/EQUIVALENCE_PROOFS.md`'s three `memcpy_*` theorem blocks, because that file's §1
# contains the phrase "ratified design, implementation tracked as PA7" inside a bullet about
# an entirely different mechanism (`VerifiedReactiveProgram`). A blanket that covers every
# fenced block in a file must be a deliberate, file-scope declaration -- one line, at line
# start, saying so -- not a phrase that happens to appear near the top.
FILE_STATUS_MARKER_RE = re.compile(r"^\s*(?:[-*]\s+|>\s*)?\*\*Status\*\*:", re.MULTILINE)


def _has_file_status_declaration(lines: List[str], start: int, end: int) -> bool:
    return bool(FILE_STATUS_MARKER_RE.search("\n".join(lines[start - 1:end])))


def _preamble_bounds(lines: List[str]) -> Tuple[int, int]:
    """The file's PREAMBLE: line 1 through the end of its first `##`-level section (i.e.
    the line before the SECOND `##` heading), or the whole file if it has fewer than two.
    This is the window escape (b) -- the file-level design declaration -- searches."""
    h2s = [j for j in range(1, len(lines) + 1) if H2_RE.match(lines[j - 1])]
    if len(h2s) < 2:
        return (1, len(lines))
    return (1, h2s[1] - 1)


def iter_theorem_fence_docs() -> List[Path]:
    """Scope for check 3: the linter's existing normative doc set (docs/**/*.md minus
    legacy process-record subtrees) PLUS every root-level tracked `*.md` (all
    normative, and all reachable before docs/ by a new reader). Measured: adding the
    root files and the excluded subtrees changes the finding count by zero today, so this
    scope is the widest one available at no noise cost."""
    out = list(iter_scanned_docs())
    for rel in git_tracked_files():
        if rel.endswith(".md") and "/" not in rel:
            out.append(REPO_ROOT / rel)
    return sorted(set(out))


def _raw_theorem_fence_absent() -> Dict[str, str]:
    """Maps allowlist key ('<file>:<line>:<name>') -> human detail for every currently
    firing (non-escaped) THEOREM_FENCE_ABSENT instance. Shared by the live check and the
    stale-allowlist sweep. Line numbers are raw (this check does NOT strip fences -- the
    fences are its subject), so they point at the declaration header itself."""
    out: Dict[str, str] = {}
    for path in iter_theorem_fence_docs():
        try:
            raw = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        rel = path.relative_to(REPO_ROOT).as_posix()
        lines = raw.splitlines()
        pre_lo, pre_hi = _preamble_bounds(lines)
        file_escaped = _has_file_status_declaration(lines, pre_lo, pre_hi)
        for (body_lo, body_hi) in _lean_fence_blocks(lines):
            for i in range(body_lo, body_hi + 1):
                m = DECL_HEADER_RE.match(lines[i - 1])
                if not m:
                    continue
                kind, name = m.group(1), m.group(2).rstrip(".")
                if kind not in ("theorem", "lemma") or not name:
                    continue
                if _declared_in_lean_tree(name):
                    continue
                if file_escaped:
                    continue
                windows = _section_escape_windows(lines, body_lo)
                if any(_has_status_escape(lines, s, e) for (s, e) in windows):
                    continue
                key = f"{rel}:{i}:{name}"
                shown = ", ".join(f"{s}-{e}" for (s, e) in windows)
                out[key] = (
                    f"{rel}:{i}: a ```lean block displays `{kind} {name}`, but no `.lean` "
                    f"file declares that name (searched every declaration header in the "
                    f"tracked tree, fully-qualified and bare). No `**Status**:`-family "
                    f"marker in the enclosing section or any ancestor section's intro "
                    f"(lines {shown}), and no `**Status**:`-led line in the file preamble "
                    f"(lines {pre_lo}-{pre_hi}), discloses it as unbuilt."
                )
    return out


def check_theorem_fence_absent(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    findings = []
    for key, detail in sorted(_raw_theorem_fence_absent().items()):
        if ("theorem-fence-absent", key) in allowlist:
            entry = allowlist[("theorem-fence-absent", key)]
            findings.append(Finding("THEOREM_FENCE_ABSENT",
                                    f"{detail} Allowlisted: {entry.justification}", True))
            continue
        findings.append(Finding(
            "THEOREM_FENCE_ABSENT",
            f"{detail} Fix it one of four ways. (1) If the theorem exists under another "
            f"name, correct the block to the real name and real statement. (2) If it does "
            f"not exist and the block is a TARGET, mark it aspirational: put a line of the "
            f"form `**Status**: not yet implemented; tracked as PA16.` (any of "
            f"`**Status**:`, 'ratified design', 'not yet implemented', 'does not yet "
            f"exist', 'design-only', 'pending implementation', 'tracked as `PA#`/`TC#`/"
            f"`N#`/`F#`/`G#`/`B#`/`M#`/`OS#`') anywhere in the SAME `#`-heading section as "
            f"the block -- before or after it, either works -- or in the intro of any "
            f"ancestor section (a marker on `## 4` covers `### 4.1`..`### 4.3`). (3) If "
            f"the WHOLE FILE is a "
            f"design document, put that same marker in the file preamble (before the "
            f"second `##` heading) once, the way docs/MEMORY_HOOK.md #1 does, and every "
            f"block in the file is covered. (4) If neither marker would be honest -- a "
            f"pedagogical example or a placeholder name is not a 'design pending "
            f"implementation' -- add a scripts/doc_facade_allowlist.txt entry "
            f"('theorem-fence-absent::{key}::<date>::<who>::<why>')."
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
    global _LEAN_TOKENS, _LEAN_DECL_NAMES, _RUN_GATES_TEXT, _LAKEFILE_TEXT
    _LEAN_TOKENS = None
    _LEAN_DECL_NAMES = None
    _RUN_GATES_TEXT = None
    _LAKEFILE_TEXT = None

    allowlist, allowlist_errors = load_allowlist()
    findings: List[Finding] = []
    findings.extend(check_mechanism_absent(allowlist))
    findings.extend(check_gate_claims(allowlist))
    findings.extend(check_theorem_fence_absent(allowlist))

    raw_mechanism = set(_raw_mechanism_absent().keys())
    raw_gate = _raw_gate_claims()
    raw_fence = set(_raw_theorem_fence_absent().keys())

    for (check, key), entry in allowlist.items():
        if check == "theorem-fence-absent" and key not in raw_fence:
            allowlist_errors.append(
                f"doc_facade_allowlist.txt:{entry.line_num}: entry 'theorem-fence-absent::{key}' "
                f"is stale -- that block no longer fires (the theorem now exists, the block was "
                f"corrected or removed, a Status marker was added, or the line moved); remove or "
                f"update the entry."
            )
        elif check == "mechanism-absent" and key not in raw_mechanism:
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
    print("[*] Checks: MECHANISM_ABSENT, GATE_SCRIPT_MISSING, GATE_NOT_WIRED, "
          "THEOREM_FENCE_ABSENT")

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
# scripts/run_gates.py's pattern exactly: plant a
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


#  TC22 controls. The historical RED vector -- `docs/TARGETS/X86_64.md` §3's
#  `x86_mov_store_is_release` block -- cannot be replanted in place: commit f597a53 deleted
#  the block AND added `**Status**:` disclosures to that section, so escape (a) would now
#  (correctly) swallow it and the "control" would prove nothing. Instead the exact
#  historical block is replanted into a scratch document, three times over, in the three
#  configurations that matter -- unmarked (must fire), section-marked (must not), and
#  file-preamble-marked (must not). Asserting the delta is EXACTLY +1 is what makes this a
#  control rather than a smoke test: it proves the check fires on the fabricated block and
#  proves both escapes suppress the very same block, in one run.
_TC22_FABRICATED_BLOCK = (
    "```lean\n"
    "theorem x86_mov_store_is_release (m : MachineState x86_64) (addr : Addr) (val : BitVec 64) :\n"
    "  m.getMemoryType addr = .WriteBack →\n"
    "  m.isNonTemporalInstr = false →\n"
    "  PreservesStoreStoreOrder ∧ PreservesLoadStoreOrder\n"
    "```\n"
)

_TC22_SCRATCH_UNMARKED = (
    "# TC22 --self-test scratch (never committed)\n\n"
    "## 1. Unmarked section -- MUST fire\n\n"
    "The block below is the exact fabricated theorem commit f597a53 removed from\n"
    "docs/TARGETS/X86_64.md #3. Nothing here discloses that it does not exist.\n\n"
    + _TC22_FABRICATED_BLOCK +
    "\n## 2. Section-marked -- MUST NOT fire (escape a)\n\n"
    "**Status**: not yet implemented; the same fabricated block, disclosed section-locally.\n\n"
    + _TC22_FABRICATED_BLOCK
)

_TC22_SCRATCH_FILE_MARKED = (
    "# TC22 --self-test scratch, file-level marked (never committed)\n\n"
    "## 1. Status and scope\n\n"
    "**Status**: this is a design document, not a report of built machinery.\n\n"
    "## 2. The block -- MUST NOT fire (escape b)\n\n"
    + _TC22_FABRICATED_BLOCK
)


def _self_test_theorem_fence_absent() -> Dict:
    unmarked = DOCS_DIR / "_tc22_selftest_scratch_unmarked.md"
    file_marked = DOCS_DIR / "_tc22_selftest_scratch_file_marked.md"
    baseline = _run_check_json()["by_check"].get("THEOREM_FENCE_ABSENT", 0)
    try:
        unmarked.write_text(_TC22_SCRATCH_UNMARKED, encoding="utf-8")
        file_marked.write_text(_TC22_SCRATCH_FILE_MARKED, encoding="utf-8")
        planted = _run_check_json()["by_check"].get("THEOREM_FENCE_ABSENT", 0)
    finally:
        unmarked.unlink(missing_ok=True)
        file_marked.unlink(missing_ok=True)
    reverted = _run_check_json()["by_check"].get("THEOREM_FENCE_ABSENT", 0)
    # Exactly one of the three planted fabricated blocks may fire: the unmarked one.
    red = planted == baseline + 1
    return {"defect": "theorem_fence_absent", "check": "THEOREM_FENCE_ABSENT",
            "turned_red": red, "green_after_revert": reverted == baseline,
            "baseline": baseline, "with_three_planted_blocks": planted,
            "after_revert": reverted}


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
        ("theorem_fence_absent", _self_test_theorem_fence_absent),
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

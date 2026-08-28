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
scripts/check_record.py - Decision-record integrity gate for gasm

WHY THIS EXISTS: D23 (`docs/adr/0031-flatten-not-history-scrub.md`) makes
`PLAN.md`, `docs/adr/`, and `docs/tasks/` the SOLE SURVIVING decision history
of this project once the repository is flattened -- commit messages stop
being a durable record. An unchecked record is one that drifts, and this one
demonstrably did: a hand-maintained index of owner quotes
(`docs/adr/OWNER_DIRECTIVES.md`) went 12 messages stale while its own header
claimed to be "the full inventory of the owner's directives", and a
duplicate decision ID (two different decisions both numbered D25) sat in
`PLAN.md` undetected. Both were only caught by a human adversarial review --
which is itself evidence of a MISSING GATE (Law 13: a reviewer catching a
defect by hand is a defect report AND a missing-gate report).

This is also, precisely, the same failure class the project's repair epic
names for the MODEL layer ("broadly detect unintended duplication growing").
`OWNER_DIRECTIVES.md` was unintended duplication in the DOCUMENTATION layer:
a second, hand-maintained source of truth for facts whose ground truth is
the session trajectory, which drifted from that source within hours of
being written. The fix in both layers is the same shape: stop hand-copying
a fact that has one real source, and gate the record that remains instead.

WHAT THIS CHECKS (all five, every run):

1. DUPLICATE_DECISION_ID -- every `**D<N>` / `**D<N>-<letter>` decision
   definition in PLAN.md is a unique ID. Never allowlistable: a genuine
   duplicate ID must be renumbered, not exempted -- that is precisely the
   defect this check exists to catch.
2. DECISION_MISSING_ADR -- every decision ID defined in PLAN.md has a
   corresponding ADR (an `docs/adr/NNNN-*.md` file whose `## Status` section
   cites it as `PLAN.md D<N>`), or an explicit allowlist entry recording why
   it does not.
3. ADR_MISSING_PROVENANCE -- every numbered ADR (`docs/adr/NNNN-*.md`)
   carries a `## Provenance` section, or an explicit allowlist entry.
4. DANGLING_CROSS_REFERENCE -- every markdown link (`[text](path)`) and
   every backtick-quoted file path (that has a directory component; a bare
   filename with no `/` is excluded as under-determined) inside PLAN.md,
   docs/adr/*.md, docs/tasks/*.md, TCB.md, MODEL_DEBT.md, and docs/REVIEW.md
   resolves to a real file on disk, or has an explicit allowlist entry. A
   `references/**` path or a literal `NNNN` template placeholder is out of
   scope (see `_in_scope_cross_ref`'s docstring for why). A reference to a
   deleted or renamed decision-record file is exactly the class of defect
   deleting `OWNER_DIRECTIVES.md` risked creating in four files -- this
   check exists so the next one is caught by CI, not by a human audit.
5. UNVERIFIED_COMPLETENESS_CLAIM -- a phrase asserting a document is a
   "full inventory", "complete list", "comprehensive list", etc. of
   something must be paired with either a nearby citation of the mechanical
   check that verifies it, or an explicit allowlist entry recording why the
   claim is trusted without one. This is the subtlest check and the most
   important: `OWNER_DIRECTIVES.md`'s header claimed to be "the full
   inventory of the owner's directives" and nothing ever checked that claim
   against the transcript it claimed to index. This check is inherently a
   heuristic phrase-match, not a semantic verifier -- it cannot confirm a
   completeness claim IS true, only that someone has taken responsibility
   for it (a cited check, or a recorded, reviewable reason it is trusted
   without one). Treat it as a tripwire, not a proof.

ALLOWLIST: scripts/decision_record_allowlist.txt, 5 `::`-delimited fields
(same shape as scripts/gate_allowlist.txt / scripts/license_allowlist.txt):

    <check>::<key>::<added>::<added-by>::<justification>

`<check>` is one of `no-adr`, `no-provenance`, `completeness-claim`,
`dangling-ref` (checks 2, 3, 5, 4 respectively -- check 1, duplicate IDs, is
never allowlistable, by design: a genuine duplicate has no legitimate
excuse, only a fix). `<key>` is the decision ID (`D22`), the ADR number
(`0021`), `<file>:<line>` for a completeness claim, or `<file>@<target>`
(note: `@`, not `::`, as the inner separator -- `<key>` is itself one of
the 5 outer `::`-delimited fields, so it cannot contain `::`) for a
dangling reference. A line with any other field count, an unknown check
name, or an empty justification is a hard parse failure, never a
silently-skipped line.

Usage:
    python scripts/check_record.py            # full report (default)
    python scripts/check_record.py --json      # machine-readable JSON
    python scripts/check_record.py --self-test # plant/verify/revert each check (re-runnable)
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

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
    Fails loudly (exits 1) if git is unavailable -- never falls back to a
    filesystem walk."""
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z"], cwd=REPO_ROOT,
            capture_output=True, timeout=30,
        )
    except (FileNotFoundError, OSError) as e:
        print(f"[!] FATAL: 'git' is not available or could not be run ({e}). File "
              f"enumeration for this gate depends on 'git ls-files' -- refusing to fall "
              f"back to a filesystem walk (that would silently reintroduce the "
              f"nested-worktree phantom-file bug this enumeration exists to prevent).",
              file=sys.stderr)
        sys.exit(1)
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
        print(f"[!] FATAL: 'git ls-files' exited {proc.returncode}: {stderr}", file=sys.stderr)
        sys.exit(1)
    raw = proc.stdout.decode("utf-8", errors="replace")
    return [p for p in raw.split("\0") if p]
ALLOWLIST_PATH = REPO_ROOT / "scripts" / "decision_record_allowlist.txt"
PLAN_MD = REPO_ROOT / "PLAN.md"
ADR_DIR = REPO_ROOT / "docs" / "adr"
TASKS_DIR = REPO_ROOT / "docs" / "tasks"
TCB_MD = REPO_ROOT / "TCB.md"
MODEL_DEBT_MD = REPO_ROOT / "MODEL_DEBT.md"
REVIEW_MD = REPO_ROOT / "docs" / "REVIEW.md"

VALID_ALLOWLIST_CHECKS = {"no-adr", "no-provenance", "completeness-claim", "dangling-ref"}

# --- Patterns -----------------------------------------------------------------

# Decision-ID definitions in PLAN.md: **D23 --  or  **D16** -- (both styles are
# used in the file today; the closing ** is optional because the em-dash can
# sit either inside or outside the bold span). The `-[a-z]` suffix group is
# POSSESSIVE (`?+`): without it, "D16-a" backtracks on failing to find a dash
# right after "-a", falls back to NOT consuming "-a", and then matches the
# bare hyphen in "-a" itself as the id/title separator -- silently splitting
# one "D16-a" definition into a spurious second "D16" one. The terminator
# excludes a bare hyphen immediately followed by a letter for the same
# reason (that shape is a suffix, not a separator).
DECISION_DEF_RE = re.compile(r"\*\*(D\d+(?:-[a-z])?+)\*{0,2}\s*(?:[—–]|-(?=[\s(]))")

# What an ADR's Status section uses to declare which PLAN.md decision(s) it
# records, e.g. "(PLAN.md D17.)" or "(PLAN.md D16, D16-a.)".
ADR_STATUS_PLAN_REF_RE = re.compile(r"PLAN\.md\s+((?:D\d+(?:-[a-z])?\s*,?\s*)+)")
DECISION_ID_RE = re.compile(r"D\d+(?:-[a-z])?")

ADR_FILENAME_RE = re.compile(r"^(\d{4})-.*\.md$")

# Markdown links: [text](path). Excludes bare-scheme URLs and pure anchors.
MD_LINK_RE = re.compile(r"\[[^\]\n]*\]\(([^)\s]+)\)")
# Backtick-quoted bare file paths ending in a known doc/source extension,
# optionally with a #anchor, immediately closed by a backtick (so a Lean
# citation like `Uop.lean:57-68` -- which has a trailing :range, not an
# immediate closing backtick -- does not false-positive).
BACKTICK_PATH_RE = re.compile(
    r"`([A-Za-z0-9_./-]+\.(?:md|py|lean|txt|json|ya?ml|toml))(#[\w.\-]+)?`"
)

COMPLETENESS_PHRASES = [
    "full inventory", "complete list", "complete inventory",
    "comprehensive list", "comprehensive inventory", "entire inventory",
    "fully complete", "complete record", "complete index",
    "exhaustive inventory", "exhaustive list",
]
COMPLETENESS_RE = re.compile(
    "(" + "|".join(re.escape(p) for p in COMPLETENESS_PHRASES) + ")", re.IGNORECASE
)
# A "nearby verifying check" proxy: a script invocation or gate name close to
# the claim. Deliberately generous (recall over precision) since a false
# "paired" verdict just means a human reviews it manually via the report line,
# while a false "unpaired" verdict is loud and self-correcting.
NEARBY_CHECK_RE = re.compile(r"scripts/[\w_]+\.py|lake exe \w+|`lake build`")

CORE_DOC_FILES = [PLAN_MD, TCB_MD, MODEL_DEBT_MD, REVIEW_MD]


def iter_adr_files() -> List[Path]:
    if not ADR_DIR.is_dir():
        return []
    out = []
    for p in sorted(ADR_DIR.glob("*.md")):
        if ADR_FILENAME_RE.match(p.name):
            out.append(p)
    return out


def iter_all_scanned_files() -> List[Path]:
    files = list(CORE_DOC_FILES)
    if ADR_DIR.is_dir():
        files.extend(sorted(ADR_DIR.glob("*.md")))
    if TASKS_DIR.is_dir():
        files.extend(sorted(TASKS_DIR.glob("*.md")))
    return [f for f in files if f.is_file()]


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
                f"decision_record_allowlist.txt:{line_num}: expected 5 '::'-delimited "
                f"fields (check::key::added::added_by::justification), got {len(parts)}: {raw_line!r}"
            )
            continue
        check, key, added, added_by, justification = (p.strip() for p in parts)
        if check not in VALID_ALLOWLIST_CHECKS:
            errors.append(
                f"decision_record_allowlist.txt:{line_num}: unknown check '{check}' "
                f"(expected one of {sorted(VALID_ALLOWLIST_CHECKS)})"
            )
            continue
        if not justification:
            errors.append(f"decision_record_allowlist.txt:{line_num}: missing justification")
            continue
        dup_key = (check, key)
        if dup_key in entries:
            errors.append(
                f"decision_record_allowlist.txt:{line_num}: duplicate entry for "
                f"'{check}::{key}' (first defined at line {entries[dup_key].line_num}) -- "
                f"duplicates are a hard error, not silent last-wins"
            )
            continue
        entries[dup_key] = AllowlistEntry(check, key, added, added_by, justification, line_num)

    return entries, errors


# --- Finding ---------------------------------------------------------------------

class Finding:
    __slots__ = ("check", "detail", "allowlisted")

    def __init__(self, check: str, detail: str, allowlisted: bool = False):
        self.check = check
        self.detail = detail
        self.allowlisted = allowlisted


# --- CHECK 1: duplicate decision IDs --------------------------------------------

def check_duplicate_decision_ids() -> List[Finding]:
    if not PLAN_MD.is_file():
        return [Finding("DUPLICATE_DECISION_ID", "PLAN.md not found", allowlisted=False)]
    text = PLAN_MD.read_text(encoding="utf-8")
    seen: Dict[str, List[int]] = {}
    for i, line in enumerate(text.splitlines(), start=1):
        for m in DECISION_DEF_RE.finditer(line):
            seen.setdefault(m.group(1), []).append(i)
    findings = []
    for decision_id, lines in sorted(seen.items()):
        if len(lines) > 1:
            findings.append(Finding(
                "DUPLICATE_DECISION_ID",
                f"PLAN.md: decision ID '{decision_id}' is defined {len(lines)} times "
                f"(lines {', '.join(str(l) for l in lines)}) -- every cross-reference to "
                f"it is now ambiguous. Never allowlistable: renumber one occurrence."
            ))
    return findings


def all_decision_ids() -> Dict[str, List[int]]:
    if not PLAN_MD.is_file():
        return {}
    text = PLAN_MD.read_text(encoding="utf-8")
    seen: Dict[str, List[int]] = {}
    for i, line in enumerate(text.splitlines(), start=1):
        for m in DECISION_DEF_RE.finditer(line):
            seen.setdefault(m.group(1), []).append(i)
    return seen


# --- CHECK 2: every decision has an ADR -----------------------------------------

def adr_covered_decision_ids() -> Dict[str, str]:
    """Maps decision-id -> adr filename, from every ADR's Status section."""
    covered: Dict[str, str] = {}
    for adr in iter_adr_files():
        text = adr.read_text(encoding="utf-8")
        # Only look in the Status section (between '## Status' and the next '## ').
        m = re.search(r"##\s*Status\s*\n(.*?)(?=\n##\s|\Z)", text, re.DOTALL)
        status_text = m.group(1) if m else text
        for ref_m in ADR_STATUS_PLAN_REF_RE.finditer(status_text):
            for did in DECISION_ID_RE.findall(ref_m.group(1)):
                covered[did] = adr.name
    return covered


def check_decisions_missing_adr(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    ids = all_decision_ids()
    covered = adr_covered_decision_ids()
    findings = []
    for decision_id in sorted(ids, key=lambda d: (int(re.match(r"D(\d+)", d).group(1)), d)):
        if decision_id in covered:
            continue
        key = decision_id
        if ("no-adr", key) in allowlist:
            entry = allowlist[("no-adr", key)]
            findings.append(Finding(
                "DECISION_MISSING_ADR",
                f"PLAN.md {decision_id}: no dedicated ADR -- allowlisted: {entry.justification}",
                allowlisted=True,
            ))
            continue
        findings.append(Finding(
            "DECISION_MISSING_ADR",
            f"PLAN.md {decision_id}: no ADR's Status section cites it as 'PLAN.md {decision_id}', "
            f"and no scripts/decision_record_allowlist.txt entry ('no-adr::{decision_id}::...') "
            f"records why not."
        ))
    return findings


# --- CHECK 3: every ADR has Provenance -------------------------------------------

def check_adrs_missing_provenance(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    findings = []
    for adr in iter_adr_files():
        m = ADR_FILENAME_RE.match(adr.name)
        number = m.group(1)
        text = adr.read_text(encoding="utf-8")
        if re.search(r"^##\s*Provenance\s*$", text, re.MULTILINE):
            continue
        if ("no-provenance", number) in allowlist:
            entry = allowlist[("no-provenance", number)]
            findings.append(Finding(
                "ADR_MISSING_PROVENANCE",
                f"docs/adr/{adr.name}: no '## Provenance' section -- allowlisted: {entry.justification}",
                allowlisted=True,
            ))
            continue
        findings.append(Finding(
            "ADR_MISSING_PROVENANCE",
            f"docs/adr/{adr.name}: no '## Provenance' section, and no "
            f"scripts/decision_record_allowlist.txt entry ('no-provenance::{number}::...') "
            f"records why not."
        ))
    return findings


# --- CHECK 4: cross-references resolve -------------------------------------------

def _strip_anchor(target: str) -> str:
    return target.split("#", 1)[0]


_BASENAME_INDEX: Optional[Dict[str, bool]] = None


def _invalidate_basename_index() -> None:
    """Must be called at the start of every top-level check run (run_all), not
    just once per process: --self-test calls run_all() repeatedly within one
    process while planting/reverting files on disk between calls, and a
    process-lifetime-cached index would silently serve stale existence data
    across those calls."""
    global _BASENAME_INDEX
    _BASENAME_INDEX = None


def _basename_exists_anywhere(basename: str) -> bool:
    """Repo-wide basename search, as a last-resort tolerance for a path written
    relative to a convention this tool doesn't special-case. Indexed once per
    check RUN (see _invalidate_basename_index), not per lookup -- a naive
    per-target scan over the whole tree made --self-test's repeated
    full-suite runs pathologically slow (a full scan per unresolved target,
    repeated across 5 sub-tests).

    Indexed from `git ls-files` (tracked files only), not a filesystem walk:
    a file must be tracked to count as "resolving" a cross-reference here.
    This also closes a real correctness gap, not just a performance one -- a
    filesystem walk would let an untracked nested worktree copy (e.g.
    `.claude/worktrees/agent-*/docs/adr/0001-foo.md`) falsely satisfy this
    last-resort tolerance for a reference that is genuinely dangling in the
    real repository, silently hiding the exact defect this check exists to
    catch."""
    global _BASENAME_INDEX
    if _BASENAME_INDEX is None:
        index: Dict[str, bool] = {}
        for rel in git_tracked_files():
            index[Path(rel).name] = True
        _BASENAME_INDEX = index
    return basename in _BASENAME_INDEX


def _resolve(referencing_file: Path, target: str) -> bool:
    """True if `target` (a relative path, possibly with a #anchor) resolves to a
    real file, trying (in order): relative to the referencing file's directory,
    relative to the repo root, and an indexed repo-wide basename search as a
    last resort (so a legitimate `../` or root-relative convention mismatch is
    not misreported as broken)."""
    path_part = _strip_anchor(target)
    if not path_part:
        return True  # pure same-file anchor, e.g. "#section" -- not a file ref
    if path_part.startswith(("http://", "https://", "mailto:")):
        return True
    candidate = (referencing_file.parent / path_part).resolve()
    if candidate.is_file():
        return True
    candidate2 = (REPO_ROOT / path_part).resolve()
    if candidate2.is_file():
        return True
    return _basename_exists_anywhere(Path(path_part).name)


def _in_scope_cross_ref(target: str) -> bool:
    """Scopes check 4 to the decision record's own domain, deliberately excluding
    two classes of non-finding: (a) `references/**` paths -- a separate,
    fast-moving subsystem (a live corpus-migration/deletion workstream) whose
    prose narrates past and present file existence as fact, not as navigation
    pointers, so a mention of a file it deleted ("binary.md was deleted") is
    correct prose, not rot; (b) template placeholders containing the literal
    string `NNNN` (e.g. `docs/adr/NNNN-short-slug.md`), which is the documented
    numbering convention's own example text, never a real reference. A bare
    filename with no directory component (`binary.md`, `Main.lean`) is also
    excluded outside a proper markdown link -- there is not enough structure in
    a bare backtick-quoted word to be confident it was meant as a navigable
    pointer rather than a narrative mention of a short name."""
    path_part = _strip_anchor(target)
    if not path_part:
        return False
    if path_part.startswith(("http://", "https://", "mailto:")):
        return False
    if "NNNN" in path_part:
        return False
    if path_part.startswith("references/") or path_part.startswith("../references/"):
        return False
    return True


def raw_dangling_refs() -> Dict[str, str]:
    """Maps allowlist key ('<file>@<target>') -> human-readable detail, for
    every currently-dangling in-scope cross-reference. Shared by the live
    check and the stale-allowlist-entry sweep."""
    out: Dict[str, str] = {}
    for f in iter_all_scanned_files():
        text = f.read_text(encoding="utf-8")
        rel = f.relative_to(REPO_ROOT).as_posix()
        targets = set()
        for m in MD_LINK_RE.finditer(text):
            targets.add(m.group(1))
        for m in BACKTICK_PATH_RE.finditer(text):
            path_part = m.group(1)
            if "/" not in path_part:
                continue  # bare filename, no directory -- see _in_scope_cross_ref
            targets.add(path_part + (m.group(2) or ""))
        for target in sorted(targets):
            if not _in_scope_cross_ref(target):
                continue
            if not _resolve(f, target):
                out[f"{rel}@{target}"] = (
                    f"{rel}: reference to '{target}' does not resolve to any file on disk."
                )
    return out


def check_dangling_cross_references(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    findings = []
    for key, detail in sorted(raw_dangling_refs().items()):
        if ("dangling-ref", key) in allowlist:
            entry = allowlist[("dangling-ref", key)]
            findings.append(Finding("DANGLING_CROSS_REFERENCE",
                                     f"{detail} Allowlisted: {entry.justification}",
                                     allowlisted=True))
            continue
        findings.append(Finding(
            "DANGLING_CROSS_REFERENCE",
            f"{detail} Fix the reference, restore/rename the file, or add "
            f"scripts/decision_record_allowlist.txt entry ('dangling-ref::{key}::...') "
            f"recording why not."
        ))
    return findings


# --- CHECK 5: unverified completeness claims -------------------------------------

def check_unverified_completeness_claims(allowlist: Dict[Tuple[str, str], AllowlistEntry]) -> List[Finding]:
    findings = []
    for f in iter_all_scanned_files():
        text = f.read_text(encoding="utf-8")
        rel = f.relative_to(REPO_ROOT).as_posix()
        lines = text.splitlines()
        for i, line in enumerate(lines, start=1):
            for m in COMPLETENESS_RE.finditer(line):
                # Look at a small window around the match (this line plus one
                # before/after) for a nearby verifying-check citation.
                window = "\n".join(lines[max(0, i - 2):min(len(lines), i + 1)])
                if NEARBY_CHECK_RE.search(window):
                    continue
                key = f"{rel}:{i}"
                if ("completeness-claim", key) in allowlist:
                    entry = allowlist[("completeness-claim", key)]
                    findings.append(Finding(
                        "UNVERIFIED_COMPLETENESS_CLAIM",
                        f"{key}: {m.group(1)!r} -- allowlisted: {entry.justification}",
                        allowlisted=True,
                    ))
                    continue
                findings.append(Finding(
                    "UNVERIFIED_COMPLETENESS_CLAIM",
                    f"{key}: {m.group(1)!r} is a completeness claim with no nearby mechanical-check "
                    f"citation (a scripts/*.py / lake exe mention within one line) and no "
                    f"scripts/decision_record_allowlist.txt entry "
                    f"('completeness-claim::{key}::...') recording why it is trusted without one."
                ))
    return findings


# --- Runner -----------------------------------------------------------------------

def run_all() -> Tuple[List[Finding], List[str]]:
    _invalidate_basename_index()
    allowlist, allowlist_errors = load_allowlist()
    findings: List[Finding] = []
    findings.extend(check_duplicate_decision_ids())
    findings.extend(check_decisions_missing_adr(allowlist))
    findings.extend(check_adrs_missing_provenance(allowlist))
    findings.extend(check_dangling_cross_references(allowlist))
    findings.extend(check_unverified_completeness_claims(allowlist))

    # Stale allowlist entries: an entry whose (check, key) no longer trips
    # anything is a hard failure, mirroring check_licenses.py's / check_gates.py's
    # stale-entry policy -- an allowlist must reflect real, current exceptions
    # only. Re-derive each check's raw (pre-allowlist) detection set directly.
    raw_missing_adr = {d for d in all_decision_ids() if d not in adr_covered_decision_ids()}
    raw_missing_prov = set()
    for adr in iter_adr_files():
        text = adr.read_text(encoding="utf-8")
        if not re.search(r"^##\s*Provenance\s*$", text, re.MULTILINE):
            raw_missing_prov.add(ADR_FILENAME_RE.match(adr.name).group(1))
    raw_completeness_keys = set()
    for f in iter_all_scanned_files():
        text = f.read_text(encoding="utf-8")
        rel = f.relative_to(REPO_ROOT).as_posix()
        lines = text.splitlines()
        for i, line in enumerate(lines, start=1):
            for m in COMPLETENESS_RE.finditer(line):
                window = "\n".join(lines[max(0, i - 2):min(len(lines), i + 1)])
                if NEARBY_CHECK_RE.search(window):
                    continue
                raw_completeness_keys.add(f"{rel}:{i}")

    for (check, key), entry in allowlist.items():
        if check == "no-adr" and key not in raw_missing_adr:
            allowlist_errors.append(
                f"decision_record_allowlist.txt:{entry.line_num}: entry 'no-adr::{key}' is stale "
                f"-- that decision now has an ADR (or never needed one); remove the entry."
            )
        elif check == "no-provenance" and key not in raw_missing_prov:
            allowlist_errors.append(
                f"decision_record_allowlist.txt:{entry.line_num}: entry 'no-provenance::{key}' is "
                f"stale -- that ADR now has a Provenance section; remove the entry."
            )
        elif check == "completeness-claim" and key not in raw_completeness_keys:
            allowlist_errors.append(
                f"decision_record_allowlist.txt:{entry.line_num}: entry 'completeness-claim::{key}' "
                f"is stale -- no unpaired completeness claim at that location anymore; remove the "
                f"entry."
            )
        elif check == "dangling-ref" and key not in raw_dangling_refs():
            allowlist_errors.append(
                f"decision_record_allowlist.txt:{entry.line_num}: entry 'dangling-ref::{key}' is "
                f"stale -- that reference now resolves (or no longer exists); remove the entry."
            )

    return findings, allowlist_errors


def main():
    parser = argparse.ArgumentParser(description="Decision-record integrity gate for gasm")
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
    print(" gasm Decision-Record Integrity Checker (scripts/check_record.py)")
    print("=" * 70)
    print("[*] Checks: DUPLICATE_DECISION_ID, DECISION_MISSING_ADR, "
          "ADR_MISSING_PROVENANCE, DANGLING_CROSS_REFERENCE, "
          "UNVERIFIED_COMPLETENESS_CLAIM")

    if allowlist_errors:
        has_errors = True
        print(f"\n[!] FAILED: {len(allowlist_errors)} decision_record_allowlist.txt integrity error(s):")
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
        print(f"\n[i] {len(allowlisted)} finding(s) exempted via scripts/decision_record_allowlist.txt:")
        for f in allowlisted:
            print(f"    - [{f.check}] {f.detail}")

    print("\n" + "=" * 70)
    print(f" SUMMARY: {len(blocking)} blocking, {len(allowlisted)} allowlisted, "
          f"{len(allowlist_errors)} allowlist error(s).")
    print("=" * 70)

    sys.exit(1 if has_errors else 0)


# --------------------------------------------------------------------------------
# --self-test: a RE-RUNNABLE regression test for the gate itself (mirrors
# scripts/run_gates.py's TCB T4 meta-gate fixture pattern exactly: plant a
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


def _self_test_duplicate_id() -> Dict:
    original = PLAN_MD.read_text(encoding="utf-8")
    # Duplicate an existing, real decision ID onto a second bullet.
    probe_line = "\n- **D1 — TC5 --self-test scratch duplicate (never committed).**\n"
    try:
        PLAN_MD.write_text(original + probe_line, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("DUPLICATE_DECISION_ID", 0) > 0
    finally:
        PLAN_MD.write_text(original, encoding="utf-8")
    green_after = _run_check_json()["by_check"].get("DUPLICATE_DECISION_ID", 0) == 0
    return {"defect": "duplicate_decision_id", "check": "DUPLICATE_DECISION_ID",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_missing_adr() -> Dict:
    original = PLAN_MD.read_text(encoding="utf-8")
    probe_line = (
        "\n- **D9999 — TC5 --self-test scratch decision with no ADR "
        "(never committed).**: placeholder text.\n"
    )
    try:
        PLAN_MD.write_text(original + probe_line, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("DECISION_MISSING_ADR", 0) > 0
    finally:
        PLAN_MD.write_text(original, encoding="utf-8")
    green_after = _run_check_json()["by_check"].get("DECISION_MISSING_ADR", 0) == 0
    return {"defect": "decision_missing_adr", "check": "DECISION_MISSING_ADR",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_missing_provenance() -> Dict:
    probe = ADR_DIR / "9999-self-test-scratch.md"
    content = (
        "# 9999. TC5 self-test scratch ADR (never committed)\n\n"
        "## Status\n\nAccepted, 2026-08-27.\n\n"
        "## Context\n\nScratch fixture.\n\n"
        "## Decision\n\nScratch fixture.\n\n"
        "## Consequences\n\nScratch fixture.\n"
        # Deliberately no '## Provenance' section.
    )
    try:
        probe.write_text(content, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("ADR_MISSING_PROVENANCE", 0) > 0
    finally:
        probe.unlink(missing_ok=True)
    green_after = _run_check_json()["by_check"].get("ADR_MISSING_PROVENANCE", 0) == 0
    return {"defect": "adr_missing_provenance", "check": "ADR_MISSING_PROVENANCE",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_dangling_reference() -> Dict:
    original = PLAN_MD.read_text(encoding="utf-8")
    probe_line = (
        "\nSee [`9999`](adr/9999-does-not-exist-tc5-selftest.md) for details "
        "(TC5 --self-test scratch, never committed).\n"
    )
    try:
        PLAN_MD.write_text(original + probe_line, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("DANGLING_CROSS_REFERENCE", 0) > 0
    finally:
        PLAN_MD.write_text(original, encoding="utf-8")
    green_after = _run_check_json()["by_check"].get("DANGLING_CROSS_REFERENCE", 0) == 0
    return {"defect": "dangling_cross_reference", "check": "DANGLING_CROSS_REFERENCE",
            "turned_red": red, "green_after_revert": green_after}


def _self_test_completeness_claim() -> Dict:
    original = PLAN_MD.read_text(encoding="utf-8")
    probe_line = (
        "\nTC5 --self-test scratch (never committed): this paragraph is the full "
        "inventory of every scratch fixture ever planted here, unpaired with any "
        "mechanical check on purpose.\n"
    )
    try:
        PLAN_MD.write_text(original + probe_line, encoding="utf-8")
        after = _run_check_json()
        red = after["by_check"].get("UNVERIFIED_COMPLETENESS_CLAIM", 0) > 0
    finally:
        PLAN_MD.write_text(original, encoding="utf-8")
    green_after = _run_check_json()["by_check"].get("UNVERIFIED_COMPLETENESS_CLAIM", 0) == 0
    return {"defect": "unverified_completeness_claim", "check": "UNVERIFIED_COMPLETENESS_CLAIM",
            "turned_red": red, "green_after_revert": green_after}


def run_self_test(json_mode: bool) -> int:
    if not json_mode:
        print("#" * 100)
        print("# check_record.py --self-test: re-runnable planted-defect control vectors")
        print("#" * 100)

    results = []
    for label, fn in [
        ("duplicate_decision_id", _self_test_duplicate_id),
        ("decision_missing_adr", _self_test_missing_adr),
        ("adr_missing_provenance", _self_test_missing_provenance),
        ("dangling_cross_reference", _self_test_dangling_reference),
        ("unverified_completeness_claim", _self_test_completeness_claim),
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
            print(f"  - {r['defect']:<32} check={r['check']:<28} "
                  f"turned_red={r['turned_red']!s:<6} green_after_revert={r['green_after_revert']!s:<6}")
        print("=" * 100)

    return 0 if all_ok else 1


if __name__ == "__main__":
    main()

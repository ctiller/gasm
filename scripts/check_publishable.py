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
scripts/check_publishable.py - Pre-Flatten Publishability Gate for gasm

The top-level mechanical gate for the publishability contract in
docs/REFERENCE_INDEX.md §6.6. This script
is the PUBLISHABILITY gate: "is anything in this tree unsafe or improper to
publish." It deliberately does not re-implement checks that already have a
dedicated, better-scoped owner elsewhere in scripts/ -- it shells out to them
and folds their exit code in, the same way scripts/check_refs.py is its own
standalone tool rather than being absorbed into something else:

    - scripts/check_licenses.py   owns Apache-2.0 header coverage on
                                   first-party source. Not duplicated here.
    - scripts/check_references.py owns citation-level validation against the
                                   references.json registry (slugs resolve,
                                   anchors exist, hashes match) once that
                                   registry lands (docs/REFERENCE_INDEX.md).
                                   Not duplicated here. This script only asks
                                   the much blunter question "does a REF:
                                   still point at the banned references/
                                   tree at all" -- see check_no_reference_prose().

What IS this script's own job, because nothing else in scripts/ owns it:
1. Secret / credential pattern sweep (tracked files AND anything sitting in
   the working tree regardless of .gitignore, since a stale ignore rule must
   not hide a leak).
2. Machine-local / personal path sweep (C:\\Users\\<name>, /home/<name>,
   /Users/<name>, file:/// links, worktree/build paths that leak a real
   machine's layout).
3. Tracked build/binary residue (anything matching known build-artifact
   extensions that is nonetheless tracked by git).
4. THE LOUD CHECK -- owner ruling (relayed 2026-08-27): "I don't want third
   party prose in the repo by the time we publish." This is broader than
   redistributability: it does not matter whether a references/ corpus is
   legally clearable (see docs/THIRD_PARTY_LICENSES.md) -- NONE of it may
   ship. Any file under references/, and any Lean `REF:` citation resolving
   to a path under references/, is an unconditional hard failure with NO
   allowlist override. This is intentionally the least forgiving check in
   the script.
5. Root LICENSE / NOTICE presence (a legal ship-blocking obligation, distinct
   from #4 -- see the module docstring's distinction below).
6. NOTICE-vs-reality consistency -- see check_notice_matches_references_state():
   NOTICE's "third-party content is NOT included" claim is bound to whether
   references/ actually holds any file, in both directions. Same
   no-allowlist-override treatment as #4: a false claim in a legal file is
   worse than the raw presence of the prose it lies about, so nothing may
   excuse it via a justification field.

A file under references/ is BANNED THIRD-PARTY PROSE (check #4). LICENSE and
NOTICE at repository root are REQUIRED LICENSE TEXT -- gasm's own Apache-2.0
grant and (until the references/ migration lands) the attribution NOTICE
compliance requires for what is still vendored; these are a legal obligation
to ship, not documentation, and must never be treated as "third-party content
to remove." First-party prose that merely describes a third-party system in
this project's own words (e.g. docs/TARGETS/WINDOWS.md's account of the
Win32 ABI) is neither of the above -- it is ours, and it is fine to keep. Do
not conflate the three.

A finding may be suppressed only via scripts/publish_allowlist.txt, in the
same 5-field `::`-delimited shape as scripts/gate_allowlist.txt and
scripts/license_allowlist.txt. THIRD_PARTY_PROSE and REF_CITES_BANNED_PROSE
findings have no allowlist override by design (see load_allowlist()).

FILE ENUMERATION -- TRACKED vs. UNTRACKED (read this before touching
iter_repo_files()): this script used to walk the raw filesystem
(`REPO_ROOT.rglob("*")`), which is exactly the "crying wolf" bug the rest of
this gate suite was fixed for -- an untracked nested worktree checkout under
`.claude/worktrees/agent-*/` contains a full second copy of this source
tree, so a plain filesystem walk re-discovers every already-allowlisted
finding at a bogus nested path the allowlist (keyed on real paths) can never
match, and duplicates every SECRET/MACHINE_PATH finding under a path that
will never be published. Now: this script enumerates git-TRACKED files
(`git ls-files`) UNION git-UNTRACKED-BUT-NOT-IGNORED files (`git ls-files
--others --exclude-standard`) -- see iter_repo_files(). Deliberately EXCLUDES
anything gitignored:
  - A nested worktree under `.claude/` is (once `.claude/` is gitignored,
    see this commit) excluded from BOTH sets -- it can never be
    double-scanned under a nested path again, closing the same bug class as
    every other gate in this suite.
  - Untracked-but-IGNORED content in general (`.lake/` build output, caches,
    `__pycache__`, a real `.venv/`) is no longer scanned either. This is a
    deliberate narrowing from the previous "regardless of .gitignore" design,
    not an oversight: the actual risk this script exists to catch is content
    that could end up PUBLISHED, and content `.gitignore` excludes will not
    accidentally ship via the normal `git add` / `git add -A` workflow
    everyone here actually uses. Scanning it anyway is exactly what caused
    the nested-worktree false-positive class. A file that is untracked and
    NOT yet ignored, by contrast, is one `git add -A` away from shipping --
    that is the real remaining risk, and it is still fully scanned (see
    below), just distinguished in the report as "untracked" rather than
    conflated with what is already committed.

This directly answers the "untracked != will never be published" concern:
"untracked" only means "safe" if nobody ever runs `git add -A`/`git add .`
afterward. So SECRET and MACHINE_PATH findings in an untracked-but-unignored
file are NOT silently dropped -- they are still reported under the same
check_id, with the finding's detail noting the file is untracked, so a
reviewer sees both "this ships today" (tracked) and "this would ship on the
next careless `git add -A`" (untracked, unignored) without conflating the
two into a single undifferentiated pile.

Usage:
    python scripts/check_publishable.py            # run all checks
    python scripts/check_publishable.py --list-only # print findings, always exit 0
    python scripts/check_publishable.py --skip-subprocess-checks
                                                     # skip shelling out to
                                                     # check_licenses.py (for
                                                     # environments where that
                                                     # dependency isn't set up)

Exit code is 0 iff there are zero non-allowlisted findings AND every
delegated subprocess check (check_licenses.py) also exits 0.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import List, NamedTuple, Set

if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if sys.stderr.encoding and sys.stderr.encoding.lower() not in ("utf-8", "utf8"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST_PATH = REPO_ROOT / "scripts" / "publish_allowlist.txt"
LICENSE_PATH = REPO_ROOT / "LICENSE"
NOTICE_PATH = REPO_ROOT / "NOTICE"
REFERENCES_DIR = REPO_ROOT / "references"

# Checks whose findings can NEVER be suppressed via the allowlist, no matter
# what justification is offered. THIRD_PARTY_PROSE and REF_CITES_BANNED_PROSE
# implement the owner's "no third-party prose in the repo" ruling directly --
# an allowlist entry for either would silently reintroduce exactly the thing
# this script exists to catch.
NO_OVERRIDE_CHECKS = {"THIRD_PARTY_PROSE", "REF_CITES_BANNED_PROSE", "NOTICE_CLAIM_MISMATCH"}

VALID_ALLOWLIST_CATEGORIES = {"SECRET", "MACHINE_PATH", "TRACKED_BINARY", "ROOT_LICENSE_TEXT"}

EXCLUDED_DIR_NAMES = {".git", ".jj", ".lake", "__pycache__", ".venv", "node_modules", ".system_generated"}

TEXT_EXTENSIONS_TO_SCAN = {
    ".lean", ".py", ".md", ".toml", ".json", ".txt", ".yml", ".yaml", ".cfg", ".ini",
    ".gitignore", ".c", ".h", ".cpp", ".sh", ".ps1",
}

TRACKED_BINARY_EXTENSIONS = {
    ".exe", ".o", ".obj", ".olean", ".ilean", ".c", ".wasm", ".wat", ".pyc",
    ".dll", ".so", ".dylib", ".bin", ".dat", ".zip", ".tar", ".gz", ".7z",
    ".class", ".pdb",
}

SECRET_PATTERNS = [
    ("AWS Access Key ID", re.compile(r"AKIA[0-9A-Z]{16}")),
    ("AWS Secret Key (assignment)", re.compile(r"(?i)aws_secret_access_key\s*[:=]\s*['\"]?[A-Za-z0-9/+=]{30,}")),
    ("GitHub Token", re.compile(r"gh[pousr]_[A-Za-z0-9]{36,}")),
    ("Generic Bearer Token", re.compile(r"(?i)bearer\s+[a-z0-9._-]{20,}")),
    ("Slack Token", re.compile(r"xox[baprs]-[A-Za-z0-9-]{10,}")),
    ("Private Key Block", re.compile(r"-----BEGIN (RSA|EC|OPENSSH|PGP|DSA|PRIVATE) KEY-----")),
    ("Generic API Key Assignment", re.compile(r"(?i)\b(api[_-]?key|secret[_-]?key|client[_-]?secret)\b\s*[:=]\s*['\"][A-Za-z0-9_\-]{16,}['\"]")),
    ("Password Assignment", re.compile(r"(?i)\bpassword\b\s*[:=]\s*['\"][^'\"]{4,}['\"]")),
    ("Connection String w/ Credentials", re.compile(r"(?i)(postgres|mysql|mongodb|redis)://[^:\s]+:[^@\s]+@")),
    ("OpenAI-style Secret Key", re.compile(r"sk-[A-Za-z0-9]{20,}")),
    ("JWT", re.compile(r"eyJ[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}")),
]

# Any path segment of this shape names a real machine's user account or a
# real machine's local build layout.
MACHINE_LOCAL_PATTERNS = [
    ("Windows user path", re.compile(r"[A-Za-z]:\\\\?Users\\\\?[A-Za-z0-9_.-]+", re.IGNORECASE)),
    ("Windows user path (fwd slash)", re.compile(r"[A-Za-z]:/Users/[A-Za-z0-9_.-]+", re.IGNORECASE)),
    ("file:/// local link", re.compile(r"file:///[a-zA-Z]:/", re.IGNORECASE)),
    ("POSIX home path", re.compile(r"/(?:home|Users)/[A-Za-z0-9_.-]+")),
    ("worktree build path", re.compile(r"worktrees[\\/][A-Za-z0-9_.-]+[\\/]\.lake", re.IGNORECASE)),
]

REF_REGEX = re.compile(r"/-\s*REF:\s*([^#\s]+)#", re.MULTILINE)


class Finding(NamedTuple):
    check_id: str
    path: str
    detail: str
    allowlisted: bool


class RepoFile(NamedTuple):
    path: Path
    rel: str
    tracked: bool


def _git_ls(args: List[str]) -> List[str]:
    """Runs a `git ls-files`-family command with an explicit cwd (so behavior
    never depends on the caller's current working directory) and returns its
    NUL-separated output as a list of POSIX-relative paths. Fails LOUDLY
    (exits 1) if git is unavailable or errors -- see module docstring's
    "FILE ENUMERATION" section for why a filesystem-walk fallback here would
    silently reintroduce the exact bug this replaces."""
    try:
        proc = subprocess.run(
            ["git"] + args, cwd=REPO_ROOT, capture_output=True, timeout=30,
        )
    except (FileNotFoundError, OSError) as e:
        print(f"[!] FATAL: 'git' is not available or could not be run ({e}). File "
              f"enumeration for this gate depends on git -- refusing to fall back to a "
              f"filesystem walk (that would silently reintroduce the nested-worktree "
              f"phantom-finding bug this enumeration exists to prevent).", file=sys.stderr)
        sys.exit(1)
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
        print(f"[!] FATAL: 'git {' '.join(args)}' exited {proc.returncode}: {stderr}", file=sys.stderr)
        sys.exit(1)
    raw = proc.stdout.decode("utf-8", errors="replace")
    return [p for p in raw.split("\0") if p]


def git_tracked_files() -> List[str]:
    """Every git-tracked file path (POSIX, relative to REPO_ROOT)."""
    return _git_ls(["ls-files", "-z"])


def git_untracked_not_ignored_files() -> List[str]:
    """Every untracked file path NOT excluded by .gitignore (POSIX, relative
    to REPO_ROOT) -- i.e. exactly what `git add -A` would sweep in next.
    Once `.claude/` is gitignored, a nested worktree checkout never appears
    here (or in git_tracked_files()) at all."""
    return _git_ls(["ls-files", "-z", "--others", "--exclude-standard"])


def iter_repo_files():
    """Tracked files UNION untracked-but-not-gitignored files -- see the
    module docstring's "FILE ENUMERATION" section for the full reasoning.
    Each yielded RepoFile records whether it is currently tracked, so
    callers can distinguish "this ships today" from "this would ship on the
    next careless `git add -A`" instead of conflating the two."""
    seen: Set[str] = set()
    for rel in git_tracked_files():
        p = REPO_ROOT / rel
        if not p.is_file():
            continue
        if any(part in EXCLUDED_DIR_NAMES for part in p.parts):
            continue
        seen.add(rel)
        yield RepoFile(p, rel, True)
    for rel in git_untracked_not_ignored_files():
        if rel in seen:
            continue
        p = REPO_ROOT / rel
        if not p.is_file():
            continue
        if any(part in EXCLUDED_DIR_NAMES for part in p.parts):
            continue
        yield RepoFile(p, rel, False)


def load_allowlist() -> List[dict]:
    """5 `::`-delimited fields, matching scripts/gate_allowlist.txt and
    scripts/license_allowlist.txt's convention:
        <check_id>::<path-or-'*'>::<added-date>::<added-by>::<justification>
    A malformed line, an unknown check_id, or an attempt to allowlist a
    NO_OVERRIDE_CHECKS check_id is a hard parse error, not a silent skip."""
    entries: List[dict] = []
    if not ALLOWLIST_PATH.exists():
        return entries
    errors = []
    for line_num, raw in enumerate(ALLOWLIST_PATH.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("::", 4)
        if len(parts) != 5:
            errors.append(f"publish_allowlist.txt:{line_num}: expected 5 '::'-delimited fields, got {len(parts)}: {raw!r}")
            continue
        check_id, path, added, added_by, justification = (p.strip() for p in parts)
        if check_id in NO_OVERRIDE_CHECKS:
            errors.append(f"publish_allowlist.txt:{line_num}: check_id '{check_id}' has NO allowlist "
                           f"override by design (owner ruling: no third-party prose in the tree) -- "
                           f"remove the offending content instead of allowlisting it")
            continue
        if check_id not in VALID_ALLOWLIST_CATEGORIES:
            errors.append(f"publish_allowlist.txt:{line_num}: unknown check_id '{check_id}' "
                           f"(expected one of {sorted(VALID_ALLOWLIST_CATEGORIES)})")
            continue
        if not justification:
            errors.append(f"publish_allowlist.txt:{line_num}: missing justification")
            continue
        entries.append({"check_id": check_id, "path": path, "added": added,
                         "added_by": added_by, "justification": justification})
    if errors:
        print(f"[!] WARNING: {len(errors)} malformed publish_allowlist.txt entr{'y' if len(errors)==1 else 'ies'}:")
        for e in errors:
            print(f"    - {e}")
    return entries


def is_allowlisted(allowlist: List[dict], check_id: str, rel_path: str) -> bool:
    if check_id in NO_OVERRIDE_CHECKS:
        return False
    for e in allowlist:
        if e["check_id"] == check_id and (e["path"] == rel_path or e["path"] == "*"):
            return True
    return False


def _untracked_note(rf: "RepoFile") -> str:
    return "" if rf.tracked else (
        " [UNTRACKED: not yet part of a commit -- currently safe only because nobody has "
        "run `git add -A`/`git add .` since this file appeared; fix or gitignore it before "
        "that happens]"
    )


def check_secrets(allowlist: List[dict]) -> List[Finding]:
    findings = []
    for rf in iter_repo_files():
        if rf.path.suffix.lower() not in TEXT_EXTENSIONS_TO_SCAN and rf.path.name != ".gitignore":
            continue
        try:
            text = rf.path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for name, pattern in SECRET_PATTERNS:
            if pattern.search(text):
                findings.append(Finding("SECRET", rf.rel, f"{name} pattern matched{_untracked_note(rf)}",
                                         is_allowlisted(allowlist, "SECRET", rf.rel)))
    return findings


def check_machine_local_paths(allowlist: List[dict]) -> List[Finding]:
    findings = []
    for rf in iter_repo_files():
        if rf.path.suffix.lower() not in TEXT_EXTENSIONS_TO_SCAN:
            continue
        try:
            text = rf.path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for name, pattern in MACHINE_LOCAL_PATTERNS:
            matches = pattern.findall(text)
            if matches:
                sample = matches[0]
                findings.append(Finding("MACHINE_PATH", rf.rel,
                                         f"{name} ({len(matches)} occurrence(s), e.g. {sample!r})"
                                         f"{_untracked_note(rf)}",
                                         is_allowlisted(allowlist, "MACHINE_PATH", rf.rel)))
    return findings


def check_tracked_binaries(allowlist: List[dict]) -> List[Finding]:
    # NOTE: previously silently SKIPPED this check on any git failure (a soft
    # warning, exit 0 either way) -- the exact "fail-soft on a missing/broken
    # git" trap this whole gate suite is being hardened against elsewhere.
    # git_tracked_files() now fails LOUDLY instead, matching the rest of this
    # script's file enumeration.
    findings = []
    for rel in git_tracked_files():
        ext = Path(rel).suffix.lower()
        if ext in TRACKED_BINARY_EXTENSIONS:
            findings.append(Finding("TRACKED_BINARY", rel, f"tracked file has build-artifact extension '{ext}'",
                                     is_allowlisted(allowlist, "TRACKED_BINARY", rel)))
    return findings


def check_no_reference_prose() -> List[Finding]:
    """Owner ruling: zero third-party prose in the tree at publish. This is
    the loud, unconditional check -- every file under references/ is a
    finding, full stop, regardless of what docs/THIRD_PARTY_LICENSES.md says
    about its redistributability. No allowlist override (see NO_OVERRIDE_CHECKS)."""
    findings = []
    if not REFERENCES_DIR.is_dir():
        return findings
    files = sorted(p for p in REFERENCES_DIR.rglob("*") if p.is_file())
    for p in files:
        rel = p.relative_to(REPO_ROOT).as_posix()
        findings.append(Finding("THIRD_PARTY_PROSE", rel,
                                 "file under references/ - owner ruling bans ALL third-party prose "
                                 "from the tree at publish, independent of redistributability", False))
    return findings


def check_ref_citations_into_references() -> List[Finding]:
    """Blunt companion to check_no_reference_prose(): any Lean `REF:`
    citation whose target path starts with `references/` is itself a
    finding, because once references/ is deleted (per the ruling above)
    every such citation is dangling by construction. This does NOT validate
    anchors, hashes, or slugs against the new references.json registry --
    that is scripts/check_references.py's job once it exists; this only
    answers "does this citation still point at the banned tree at all.\""""
    findings = []
    for rel in git_tracked_files():
        if not rel.endswith(".lean"):
            continue
        p = REPO_ROOT / rel
        if any(part in EXCLUDED_DIR_NAMES for part in p.parts):
            continue
        try:
            text = p.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        hits = [m.group(1) for m in REF_REGEX.finditer(text) if m.group(1).startswith("references/")]
        if hits:
            findings.append(Finding("REF_CITES_BANNED_PROSE", rel,
                                     f"{len(hits)} REF: citation(s) still target references/ "
                                     f"(e.g. {hits[0]!r}) - must be re-pointed at the references.json "
                                     f"slug registry (docs/REFERENCE_INDEX.md) before references/ can "
                                     f"be deleted", False))
    return findings


NOTICE_NO_THIRD_PARTY_MARKER = (
    "This distribution does not include third-party documentation, specification"
)


def check_notice_matches_references_state() -> List[Finding]:
    """Binds NOTICE's "no third-party content is included" claim to reality:
    that sentence is true if and only if references/ actually holds no files.
    Found by an adversarial review (2026-08-27) as the sharpest issue in the
    whole references/ migration: NOTICE affirmatively asserting "not
    included" while references/ still shipped real third-party prose would
    be a false statement in a legal file, actively disclaiming an
    attribution obligation that in fact applied -- worse than the raw
    presence of the prose alone (a reader has no reason to double-check a
    claim this specific). No allowlist override: same category as
    THIRD_PARTY_PROSE/REF_CITES_BANNED_PROSE (NO_OVERRIDE_CHECKS) -- a false
    legal-file claim is not something a justification field can excuse."""
    findings = []
    if not NOTICE_PATH.exists():
        return findings  # missing NOTICE is check_root_license_text()'s job
    text = NOTICE_PATH.read_text(encoding="utf-8")
    claims_no_third_party = NOTICE_NO_THIRD_PARTY_MARKER in text
    refs_has_files = REFERENCES_DIR.is_dir() and any(p.is_file() for p in REFERENCES_DIR.rglob("*"))
    if claims_no_third_party and refs_has_files:
        findings.append(Finding("NOTICE_CLAIM_MISMATCH", "NOTICE",
                                 "NOTICE claims third-party content is NOT included, but references/ "
                                 "still contains file(s) -- this is an affirmatively FALSE statement "
                                 "in a legal file, disclaiming an attribution obligation that in fact "
                                 "applies. Either the claim must be removed/qualified or references/ "
                                 "must be emptied before publish.", False))
    elif refs_has_files and not claims_no_third_party:
        findings.append(Finding("NOTICE_CLAIM_MISMATCH", "NOTICE",
                                 "references/ contains file(s) but NOTICE does not carry its "
                                 "no-third-party-content claim -- if this is deliberate (real "
                                 "third-party content now vendored with proper attribution), fine; "
                                 "if NOTICE simply was not updated, that is a stale legal file.", False))
    elif claims_no_third_party and not refs_has_files:
        pass  # the desired, currently-true state: claim present, references/ empty.
    # (neither claims_no_third_party nor refs_has_files: nothing to reconcile.)
    return findings


def check_root_license_text(allowlist: List[dict]) -> List[Finding]:
    findings = []
    for name, path in (("LICENSE", LICENSE_PATH), ("NOTICE", NOTICE_PATH)):
        if not path.exists():
            findings.append(Finding("ROOT_LICENSE_TEXT", name, f"repository root has no {name} file "
                                     f"(this is required legal text, not documentation - see module docstring)",
                                     is_allowlisted(allowlist, "ROOT_LICENSE_TEXT", name)))
    return findings


def run_subprocess_check(args: List[str], label: str) -> bool:
    """Runs a delegated check script in the foreground and returns True iff
    it exited 0. Never piped -- the caller's own exit code must reflect this
    directly, the same discipline docs/REFERENCE_INDEX.md §6.6 requires of
    a human running these tools by hand."""
    print(f"\n--- delegated check: {label} ---")
    sys.stdout.flush()
    try:
        result = subprocess.run([sys.executable] + args, cwd=REPO_ROOT)
    except Exception as e:
        print(f"[!] FAILED to run {label}: {e}")
        return False
    return result.returncode == 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Pre-flatten publishability gate for gasm")
    parser.add_argument("--list-only", action="store_true", help="print all findings but always exit 0")
    parser.add_argument("--skip-subprocess-checks", action="store_true",
                         help="skip delegating to scripts/check_licenses.py")
    args = parser.parse_args()

    print("=" * 70)
    print(" gasm Pre-Flatten Publishability Gate")
    print("=" * 70)

    allowlist = load_allowlist()
    print(f"[*] Loaded {len(allowlist)} allowlist entr{'y' if len(allowlist) == 1 else 'ies'} from "
          f"{ALLOWLIST_PATH.relative_to(REPO_ROOT).as_posix()}")

    all_findings: List[Finding] = []
    all_findings += check_secrets(allowlist)
    all_findings += check_machine_local_paths(allowlist)
    all_findings += check_tracked_binaries(allowlist)
    all_findings += check_root_license_text(allowlist)
    all_findings += check_no_reference_prose()
    all_findings += check_ref_citations_into_references()
    all_findings += check_notice_matches_references_state()

    blocking = [f for f in all_findings if not f.allowlisted]
    suppressed = [f for f in all_findings if f.allowlisted]

    by_check = {}
    for f in all_findings:
        by_check.setdefault(f.check_id, []).append(f)

    for check_id, findings in sorted(by_check.items()):
        loud = " *** NO ALLOWLIST OVERRIDE ***" if check_id in NO_OVERRIDE_CHECKS else ""
        print(f"\n--- {check_id} ({len(findings)} finding(s)){loud} ---")
        # references/ can be 1000+ findings; summarize rather than flooding.
        display = findings[:20]
        for f in display:
            tag = "ALLOWLISTED" if f.allowlisted else "BLOCKING"
            print(f"    [{tag}] {f.path}: {f.detail}")
        if len(findings) > len(display):
            print(f"    ... and {len(findings) - len(display)} more (see full listing with a narrower "
                  f"tool if needed, e.g. `find references -type f`)")

    subprocess_ok = True
    if not args.skip_subprocess_checks:
        subprocess_ok = run_subprocess_check(["scripts/check_licenses.py"], "scripts/check_licenses.py (Apache-2.0 header coverage)")

    print("\n" + "=" * 70)
    print(f" SUMMARY: {len(blocking)} blocking finding(s), {len(suppressed)} allowlisted finding(s).")
    print(f"          delegated check_licenses.py: {'PASS' if subprocess_ok else 'FAIL' if not args.skip_subprocess_checks else 'SKIPPED'}")
    print("=" * 70)

    if args.list_only:
        return 0
    return 1 if (blocking or not subprocess_ok) else 0


if __name__ == "__main__":
    sys.exit(main())

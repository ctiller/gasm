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
scripts/check_licenses.py - Apache-2.0 header linter for gasm

gasm is Apache License 2.0. Enforces that every in-scope first-party file
carries the standard short-form Apache header (copyright line + the
"Licensed under the Apache License, Version 2.0" paragraph + the
apache.org URL + the "AS IS" disclaimer paragraph), in the comment syntax
appropriate to its file type.

IN SCOPE (first-party source we license):
    Gasm/**/*.lean, Stdlib/**/*.lean, Spikes/**/*.lean, Tools/**/*.lean,
    root *.lean (Gasm.lean, Stdlib.lean, Spikes.lean),
    scripts/*.py, scripts/*.ps1, scripts/*.sh, lakefile.toml,
    .github/**/*.yml, .github/**/*.yaml, .github/CODEOWNERS
    (added when CI was established -- GitHub Actions workflows and issue-form
    YAML are first-party executable/config source same as a build script, and
    YAML's `#` comment syntax is identical to Python/shell/TOML's for this
    tool's purposes; CODEOWNERS is a filename-matched special case, same
    convention as lakefile.toml below.)

EXPLICITLY OUT OF SCOPE:
    references/**  -- every file there is third-party vendored reference
                       material (specs, grammars, manuals) and must NEVER
                       receive our copyright header. This tool counts and
                       reports how many files it excluded there, every run,
                       so the exclusion is visible rather than silent (an
                       empty/absent count would be indistinguishable from
                       "didn't look").
    .lake/, .git/, and any other generated/VCS-internal directory.
    Markdown documentation (`docs/**`, root and `scripts/*.md` files): a deliberate
    judgment call, not an oversight --
    see docs/REVIEW.md / the commit introducing this tool for the
    reasoning. Prose documentation is covered by the repository LICENSE
    as a whole; this project does not stamp per-file boilerplate onto
    prose docs the way it does onto compiled/executable source.

COPYRIGHT HOLDER: edit COPYRIGHT_LINE below -- and ONLY there -- to change
the copyright line this tool expects (and that every in-scope file must
carry). Everything else derives from it.

Comparison is by NORMALIZED content, not byte equality: comment markers
(`/- -/`, `#`, a leading `#!` shebang) are stripped, whitespace is
collapsed, and blank lines are dropped before comparing the header's
content lines against the expected paragraph. This is deliberately
tolerant of the different comment syntaxes Lean/Python/PowerShell/
shell/TOML each require for the same boilerplate text.

There is no exception mechanism.  Every in-scope first-party file must
carry the header; files under third-party `references/` are outside the
first-party scope rather than exempted from it.

Usage:
    python scripts/check_licenses.py            # full report (default)
    python scripts/check_licenses.py --json      # machine-readable JSON
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Docs/paths may contain non-ASCII; never let a legacy console codepage turn
# a report line into a crash. (Mirrors scripts/check_refs.py / check_gates.py.)
if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if sys.stderr.encoding and sys.stderr.encoding.lower() not in ("utf-8", "utf8"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent

# --- The one line to edit if the copyright holder ever needs to change. ---
# FLAGGED IN THE INTRODUCING REPORT: "Craig Tiller" is the repo's git author
# identity, used here as a reasonable default -- NOT a legal determination
# of the correct holder (individual vs. an entity may be the owner's call).
COPYRIGHT_LINE = "Copyright 2026 Craig Tiller"

# The standard Apache 2.0 short-form boilerplate paragraph (identical for
# every file in this repo; only the copyright line above ever varies).
LICENSE_BODY_LINES = [
    'Licensed under the Apache License, Version 2.0 (the "License");',
    "you may not use this file except in compliance with the License.",
    "You may obtain a copy of the License at",
    "http://www.apache.org/licenses/LICENSE-2.0",
    "Unless required by applicable law or agreed to in writing, software",
    'distributed under the License is distributed on an "AS IS" BASIS,',
    "WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.",
    "See the License for the specific language governing permissions and",
    "limitations under the License.",
]

EXPECTED_HEADER_LINES = [COPYRIGHT_LINE] + LICENSE_BODY_LINES



def normalize_line(line: str) -> str:
    """Collapse internal whitespace and strip leading/trailing whitespace,
    so differing indentation / comment-marker spacing never causes a false
    mismatch."""
    return re.sub(r"\s+", " ", line.strip())


def normalize_lines(lines: List[str]) -> List[str]:
    """Normalizes each line and drops blanks -- blank-line placement between
    paragraphs is not semantically meaningful for this comparison."""
    out = []
    for line in lines:
        norm = normalize_line(line)
        if norm:
            out.append(norm)
    return out


EXPECTED_NORMALIZED = normalize_lines(EXPECTED_HEADER_LINES)


# --- File-type-specific header extraction -----------------------------------

LEAN_BLOCK_RE = re.compile(r"\A(?:\s*\n)*[ \t]*/-(.*?)-/", re.DOTALL)
HASH_RE = re.compile(r"^\s*#(.*)$")
SHEBANG_RE = re.compile(r"^#!")


def extract_lean_header(text: str) -> Optional[List[str]]:
    """The very first `/- ... -/` block comment at the top of the file (only
    whitespace/blank lines may precede it). Non-greedy, so it stops at the
    first `-/` and never swallows a later, legitimate `/- REF: ... -/`
    citation into the same match."""
    m = LEAN_BLOCK_RE.match(text)
    if not m:
        return None
    return m.group(1).splitlines()


def extract_hash_header(text: str) -> Optional[List[str]]:
    """Contiguous leading `#`-prefixed lines, skipping one leading shebang
    line if present. Stops at the first non-`#`, non-blank-leading-run line."""
    lines = text.splitlines()
    i = 0
    if i < len(lines) and SHEBANG_RE.match(lines[i]):
        i += 1
    header_lines = []
    seen_any = False
    while i < len(lines):
        m = HASH_RE.match(lines[i])
        if not m:
            break
        header_lines.append(m.group(1))
        seen_any = True
        i += 1
    if not seen_any:
        return None
    return header_lines


FILE_KIND_EXTRACTORS = {
    "lean": extract_lean_header,
    "python": extract_hash_header,
    "powershell": extract_hash_header,
    "shell": extract_hash_header,
    "toml": extract_hash_header,
    "yaml": extract_hash_header,
}


def classify_file(path: Path) -> Optional[str]:
    suffix = path.suffix.lower()
    if suffix == ".lean":
        return "lean"
    if suffix == ".py":
        return "python"
    if suffix == ".ps1":
        return "powershell"
    if suffix == ".sh":
        return "shell"
    if suffix in (".yml", ".yaml"):
        return "yaml"
    if path.name == "lakefile.toml":
        return "toml"
    if path.name == "CODEOWNERS":
        return "yaml"  # `#`-comment syntax, same extractor as yaml/toml/etc.
    return None


# --- In-scope file enumeration ------------------------------------------------

FIRST_PARTY_LEAN_DIRS = ["Gasm", "Stdlib", "Spikes", "Tools"]
ROOT_LEAN_FILES = ["Gasm.lean", "Stdlib.lean", "Spikes.lean"]
SCRIPTS_GLOBS = ["*.py", "*.ps1", "*.sh"]
EXCLUDED_DIR_PARTS = {".lake", ".git", ".system_generated"}


def iter_in_scope_files() -> List[Path]:
    files: List[Path] = []

    for dirname in FIRST_PARTY_LEAN_DIRS:
        d = REPO_ROOT / dirname
        if not d.is_dir():
            continue
        for p in sorted(d.glob("**/*.lean")):
            if EXCLUDED_DIR_PARTS & set(p.parts):
                continue
            files.append(p)

    for name in ROOT_LEAN_FILES:
        p = REPO_ROOT / name
        if p.is_file():
            files.append(p)

    scripts_dir = REPO_ROOT / "scripts"
    if scripts_dir.is_dir():
        for pattern in SCRIPTS_GLOBS:
            for p in sorted(scripts_dir.glob(pattern)):
                files.append(p)

    lakefile = REPO_ROOT / "lakefile.toml"
    if lakefile.is_file():
        files.append(lakefile)

    github_dir = REPO_ROOT / ".github"
    if github_dir.is_dir():
        for pattern in ("**/*.yml", "**/*.yaml"):
            for p in sorted(github_dir.glob(pattern)):
                if EXCLUDED_DIR_PARTS & set(p.parts):
                    continue
                files.append(p)
        codeowners = github_dir / "CODEOWNERS"
        if codeowners.is_file():
            files.append(codeowners)

    return sorted(set(files))


def count_excluded_references() -> int:
    refs_dir = REPO_ROOT / "references"
    if not refs_dir.is_dir():
        return 0
    return sum(1 for p in refs_dir.glob("**/*") if p.is_file())


# --- Core check ----------------------------------------------------------------

class FileResult:
    __slots__ = ("rel_path", "kind", "status", "detail")

    def __init__(self, rel_path: str, kind: str, status: str, detail: str = ""):
        self.rel_path = rel_path
        self.kind = kind
        self.status = status  # "ok" | "missing" | "malformed"
        self.detail = detail


def check_file(path: Path) -> FileResult:
    rel_path = path.relative_to(REPO_ROOT).as_posix()
    kind = classify_file(path)
    if kind is None:
        return FileResult(rel_path, "unknown", "malformed", "unrecognized file type for header extraction")

    try:
        text = path.read_text(encoding="utf-8")
    except Exception as e:
        return FileResult(rel_path, kind, "malformed", f"could not read file: {e}")

    extractor = FILE_KIND_EXTRACTORS[kind]
    header_lines = extractor(text)
    if header_lines is None:
        return FileResult(rel_path, kind, "missing", "no header comment block found at top of file")

    actual_normalized = normalize_lines(header_lines)
    if actual_normalized[:len(EXPECTED_NORMALIZED)] == EXPECTED_NORMALIZED:
        return FileResult(rel_path, kind, "ok")

    # Distinguish "some header present but wrong" from a clean absence, for
    # a more useful diagnostic.
    if actual_normalized and actual_normalized[0] == normalize_line(COPYRIGHT_LINE):
        return FileResult(rel_path, kind, "malformed", "copyright line present but license body text does not match")
    return FileResult(rel_path, kind, "malformed", "header block present but does not match the expected Apache-2.0 boilerplate")


def run_check() -> Tuple[List[FileResult], int]:
    """Returns (results, excluded_references_count)."""
    files = iter_in_scope_files()
    excluded_count = count_excluded_references()

    results: List[FileResult] = []
    for path in files:
        results.append(check_file(path))

    return results, excluded_count


def main():
    parser = argparse.ArgumentParser(description="Apache-2.0 header linter for gasm's first-party source")
    parser.add_argument("--json", action="store_true", help="machine-readable JSON output")
    args = parser.parse_args()

    results, excluded_count = run_check()

    ok = [r for r in results if r.status == "ok"]
    missing = [r for r in results if r.status == "missing"]
    malformed = [r for r in results if r.status == "malformed"]

    by_kind: Dict[str, int] = {}
    for r in results:
        by_kind[r.kind] = by_kind.get(r.kind, 0) + 1

    has_errors = bool(missing or malformed)

    if args.json:
        out = {
            "ok": not has_errors,
            "total_in_scope": len(results),
            "by_kind": by_kind,
            "compliant": len(ok),
            "missing": [r.rel_path for r in missing],
            "malformed": [{"file": r.rel_path, "detail": r.detail} for r in malformed],
            "excluded_references_count": excluded_count,
        }
        print(json.dumps(out, indent=2))
        sys.exit(1 if has_errors else 0)

    print("=" * 70)
    print(" gasm Apache-2.0 License Header Checker (scripts/check_licenses.py)")
    print("=" * 70)
    print(f"[*] {len(results)} in-scope first-party file(s) checked:")
    for kind, count in sorted(by_kind.items()):
        print(f"    - {kind}: {count}")
    print(f"[*] Excluded {excluded_count} file(s) under references/ (third-party vendored material, "
          f"never receives a first-party header).")

    print("\n--- LICENSE HEADER CHECK ---")
    if missing:
        print(f"\n[!] FAILED: {len(missing)} file(s) missing an Apache-2.0 header entirely:")
        for r in missing:
            print(f"    - {r.rel_path}")

    if malformed:
        print(f"\n[!] FAILED: {len(malformed)} file(s) have a malformed/non-matching header:")
        for r in malformed:
            print(f"    - {r.rel_path}: {r.detail}")

    if not missing and not malformed:
        print("[+] Every in-scope first-party file carries a matching Apache-2.0 header.")

    print("\n" + "=" * 70)
    print(f" SUMMARY: {len(results)} in-scope file(s), {len(ok)} compliant, "
          f"{len(missing)} missing, {len(malformed)} malformed.")
    print(f"          {excluded_count} references/ file(s) excluded (third-party, not first-party-licensed).")
    print("=" * 70)

    sys.exit(1 if has_errors else 0)


if __name__ == "__main__":
    main()

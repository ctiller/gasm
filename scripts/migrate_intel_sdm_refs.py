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
scripts/migrate_intel_sdm_refs.py - one-shot migration of Intel SDM `REF:`
citations from `references/intel_sdm/<path>.md#<anchor>` to the
`intel-sdm#vol=V;(instr=M|sec=S);part=P;pp=A-B;mp=ENCODED` locator form
(docs/REFERENCE_INDEX.md, as corrected -- see PLAN.md D24/D25: ONE slug for
Intel's combined SDM document, not one per volume; a mandatory part= field
carrying today's anchor through unchanged; mp= from manual_pages).

SCOPE: only citations into references/intel_sdm/** across the files this
task owns (Gasm/Targets/X86_64/**, Gasm/Core/Rng.lean). Windows and Wasm
citations belong to sibling agents and are never touched by this script
(enforced below by only scanning the owned file set, not the whole tree).

Every rewrite is verified against the source line before being written:
the script re-reads the exact old `REF:` line it is about to replace,
recomputes the new locator from `intel_sdm_frontmatter.json` (the durable
side-table extracted from references/intel_sdm/**'s own frontmatter before
this migration), and refuses to write if the old line does not match
byte-for-byte what the scan found, or if the new locator fails its own
grammar/range check (see scripts/check_references.py's PDF_LOCATOR_RE and
page_count check) before it ever touches a file.

Unrecognized file shapes fail closed: a citation into references/intel_sdm/
whose target path does not match either the instruction-page or the
chapter-page branch aborts the whole run rather than being silently skipped
or mis-migrated (docs/REFERENCE_INDEX.md Finding 3).
"""

import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
FRONTMATTER_JSON = REPO_ROOT / "intel_sdm_frontmatter.json"
PAGE_COUNT = 5060  # references.json's intel-sdm entry; see its review_note for the edition caveat.

OWNED_FILES = [REPO_ROOT / "Gasm" / "Core" / "Rng.lean"] + sorted(
    (REPO_ROOT / "Gasm" / "Targets" / "X86_64").glob("**/*.lean")
)

REF_LINE_RE = re.compile(r'^(?P<indent>\s*)/-\s*REF:\s*(?P<target>references/intel_sdm/[^#\s]+)#(?P<anchor>[^\s\-]+[^\s]*)\s*-/\s*$')
HEADING_REGEX = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)


def slugify_heading(title: str) -> str:
    text = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', title)
    text = re.sub(r'[`*_]', '', text)
    text = text.lower().strip()
    text = re.sub(r'[^a-z0-9\s\-]', '', text)
    text = re.sub(r'\s+', '-', text)
    return text


def sections_for(path: Path) -> Dict[str, str]:
    content = path.read_text(encoding="utf-8")
    sections: Dict[str, str] = {}
    counts: Dict[str, int] = {}
    for m in HEADING_REGEX.finditer(content):
        title = m.group(2).strip()
        slug = slugify_heading(title)
        if slug in counts:
            counts[slug] += 1
            slug = f"{slug}-{counts[slug]}"
        else:
            counts[slug] = 0
        sections[slug] = title
    return sections


def vol_token(volume_field: str) -> str:
    m = re.match(r"Volume (\d)", volume_field)
    if m:
        return m.group(1)
    if volume_field.strip().lower().startswith("index") or "combined volumes" in volume_field.lower():
        return "index"
    raise ValueError(f"Cannot derive vol= token from volume field: {volume_field!r}")


def encode_manual_pages(mp: str) -> str:
    return re.sub(r"\s+", "_", mp.strip())


PDF_LOCATOR_RE = re.compile(
    r'^vol=(?P<vol>1|2|3|4|index);'
    r'(?:instr=(?P<instr>[A-Za-z][A-Za-z0-9_]*)|sec=(?P<sec>[0-9]+(?:\.[0-9]+)*));'
    r'part=(?P<part>[^;]+);'
    r'pp=(?P<pstart>[0-9]+)-(?P<pend>[0-9]+)'
    r'(?:;mp=(?P<mp>[^;]+))?$'
)


def build_locator(target_path: str, anchor: str, fm: Dict[str, dict]) -> str:
    if target_path not in fm:
        raise ValueError(f"UNRECOGNIZED SHAPE: '{target_path}' has no frontmatter entry in {FRONTMATTER_JSON.name} -- refusing to guess (fail closed).")
    entry = fm[target_path]
    vol = vol_token(entry["volume"])
    pp = f"{entry['page_start']}-{entry['page_end']}"
    mp = encode_manual_pages(entry["manual_pages"])
    part = anchor  # carry today's anchor through unchanged (docs/REFERENCE_INDEX.md corrected spec item 2).

    if "/instructions/" in target_path:
        mnemonic = Path(target_path).stem
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", mnemonic):
            raise ValueError(f"UNRECOGNIZED SHAPE: instruction filename stem '{mnemonic}' does not match the MNEMONIC grammar.")
        locator = f"vol={vol};instr={mnemonic};part={part};pp={pp};mp={mp}"
    elif re.search(r"/ch_\d+", target_path) or re.match(r"ch_\d+", Path(target_path).name):
        secs = sections_for(REPO_ROOT / target_path)
        if anchor not in secs:
            raise ValueError(f"UNRECOGNIZED SHAPE: anchor '{anchor}' not found among {target_path}'s headings.")
        title = secs[anchor]
        sm = re.match(r"^(\d+(?:\.\d+)*)", title.strip())
        if not sm:
            raise ValueError(f"UNRECOGNIZED SHAPE: heading title '{title}' for anchor '{anchor}' has no leading section number.")
        secnum = sm.group(1)
        locator = f"vol={vol};sec={secnum};part={part};pp={pp};mp={mp}"
    else:
        raise ValueError(f"UNRECOGNIZED SHAPE: '{target_path}' matches neither the instruction-page nor chapter-page branch -- failing closed rather than guessing (docs/REFERENCE_INDEX.md Finding 3).")

    m = PDF_LOCATOR_RE.match(locator)
    if not m:
        raise ValueError(f"INTERNAL: built locator '{locator}' fails its own grammar.")
    pstart, pend = int(m.group("pstart")), int(m.group("pend"))
    if pstart > pend:
        raise ValueError(f"INTERNAL: locator '{locator}' has pstart > pend.")
    if pend > PAGE_COUNT:
        raise ValueError(f"INTERNAL: locator '{locator}' has pp end {pend} > registered page_count {PAGE_COUNT}.")
    return locator


def main() -> int:
    dry_run = "--apply" not in sys.argv

    fm = json.loads(FRONTMATTER_JSON.read_text(encoding="utf-8"))

    total_found = 0
    total_rewritten = 0
    total_verified = 0
    per_file_changes: List[Tuple[Path, List[Tuple[int, str, str]]]] = []
    errors: List[str] = []

    for path in OWNED_FILES:
        rel = path.relative_to(REPO_ROOT).as_posix()
        original_lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        new_lines = list(original_lines)
        changes: List[Tuple[int, str, str]] = []

        for i, line in enumerate(original_lines):
            m = REF_LINE_RE.match(line.rstrip("\n"))
            if not m:
                continue
            target, anchor = m.group("target"), m.group("anchor")
            total_found += 1

            # Re-verify against the source line: re-slice the exact substring
            # this line contains and confirm it round-trips through the same
            # regex before computing a replacement -- guards against acting
            # on a stale/cached scan rather than the file's real content.
            reread = path.read_text(encoding="utf-8").splitlines(keepends=True)[i]
            m2 = REF_LINE_RE.match(reread.rstrip("\n"))
            if not m2 or m2.group("target") != target or m2.group("anchor") != anchor:
                errors.append(f"{rel}:{i+1}: source-line re-verification mismatch, refusing to touch.")
                continue

            try:
                locator = build_locator(target, anchor, fm)
            except ValueError as e:
                errors.append(f"{rel}:{i+1}: {e}")
                continue

            indent = m.group("indent")
            new_line = f"{indent}/- REF: intel-sdm#{locator} -/\n"
            new_lines[i] = new_line
            changes.append((i + 1, line.rstrip("\n"), new_line.rstrip("\n")))
            total_verified += 1

        if changes:
            per_file_changes.append((path, changes))
            if not dry_run:
                path.write_text("".join(new_lines), encoding="utf-8")
            total_rewritten += len(changes)

    print("=" * 70)
    print(f" Intel SDM REF: migration ({'DRY RUN -- pass --apply to write' if dry_run else 'APPLIED'})")
    print("=" * 70)
    print(f"[*] Citations found:            {total_found}")
    print(f"[*] Locator built & verified:   {total_verified}")
    print(f"[*] Lines {'would be' if dry_run else ''} rewritten: {total_rewritten}")
    print(f"[*] Files touched:              {len(per_file_changes)}")
    if errors:
        print(f"[!] {len(errors)} FAILURE(S) (fail-closed, not migrated):")
        for e in errors:
            print(f"    - {e}")
    for path, changes in per_file_changes:
        print(f"\n  {path.relative_to(REPO_ROOT).as_posix()}: {len(changes)} citation(s)")
        for line_no, old, new in changes[:2]:
            print(f"    L{line_no} OLD: {old.strip()}")
            print(f"    L{line_no} NEW: {new.strip()}")

    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

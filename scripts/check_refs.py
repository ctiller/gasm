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
scripts/check_refs.py - Citation Validity Checker for gasm (Law 3)

Enforces the citation-VALIDITY half of the gasm Citation Laws (docs/REVIEW.md):
1. Indexes all markdown section headings across docs/ and references/.
2. Scans all `.lean` files for `/- REF: target#anchor -/` annotations.
3. Validates that every citation's target resolves to a real section
   (path targets) or a real registry entry (slug targets) -- failing CI on
   broken references.
4. Reports the backlog of unreferenced design specifications (Law 3's
   "Unimplemented System Backlog").

WHAT THIS SCRIPT DELIBERATELY DOES NOT DO ANY MORE: detect un-cited Lean
declarations (Law 1). That used to live here too, via `LEAN_DECL_REGEX`
matched against raw source text -- a regex that REQUIRES an identifier
immediately after the declaration keyword, so it could never see an
anonymous `instance : Foo X where` (no name token at all), and never even
listed `abbrev`/`initialize` among its keywords. The consequences were worse
than a missed warning: a `REF:` comment sitting directly above one of these
invisible declarations was silently DROPPED before this fix -- not merely
unvalidated, genuinely never even looked at, because the old
`collect_lean_citations` only kept a pending `REF:` around until it either
matched a recognized declaration or a "real code" line came along and
cleared it, and an anonymous `instance` was neither. At least 22 Intel
`#operation` citations landed exactly on this blind spot.

THE FIX splits this script's old job into two INDEPENDENT mechanisms, per
the design each half is now built to:
  (a) THIS SCRIPT, citation validity: needs no Lean parsing whatsoever.
      `collect_ref_citations` below scans every line of every `.lean` file
      for `REF:` matches with a plain regex and validates each target --
      full stop. It is not coupled to "the declaration that follows" in any
      way, so no declaration form, however exotic, can make a citation
      invisible to it ever again.
  (b) `lake exe check_refs_coverage` (Tools/CheckRefsCoverage.lean), Law 1
      declaration coverage: walks the COMPILED ENVIRONMENT (Lean's own
      record of what actually exists after elaboration) rather than source
      text, so it cannot have a blind spot for any declaration FORM either
      -- see that file's own header for the full design and the containment
      -based filtering that keeps it from being spuriously noisy about
      compiler-synthesized scaffolding (`deriving`-generated instances,
      structure field projections, and the like).

Citation shapes (docs/REFERENCE_INDEX.md #6.5, "avoiding a flag day"): a `REF:`
target containing a `/` is a path into docs/ or references/, checked against
that file's on-disk headings as before. A bare target with no `/` is a
`references.json` slug -- checked for EXISTENCE in the registry only. Full
per-media-type anchor checking for slugs (docs/REFERENCE_INDEX.md #2) needs
the gitignored local cache that `scripts/check_references.py --offline`
builds; that tool DOES now exist in this tree (registry + validator landed
separately from this fix), but its cache is not populated in a fresh
checkout and it is not yet wired into scripts/run_gates.py's gate sequence,
so slug anchors are still not mechanically re-verified BY THIS SCRIPT on
every run -- they were verified once, by hand, at the point each slug
citation was authored (see the registering commit's `review_note` per
entry), and remain so until `check_references.py --offline` is wired in.
This is a real, named gap, not a silent downgrade: the summary below says
so explicitly instead of claiming a stronger guarantee than this script
actually provides.
"""

import sys
import re
import json
from pathlib import Path
from typing import Dict, List, Set, Tuple

# Docs contain Unicode (e.g. mathematical quantifiers); never let a legacy console
# codepage turn a report line into a crash.
if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
DOC_DIRS = [REPO_ROOT / "docs", REPO_ROOT / "references"]
REFERENCES_JSON_PATH = REPO_ROOT / "references.json"

# Regex patterns
HEADING_REGEX = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)
REF_REGEX = re.compile(r'/\-\s*REF:\s*([^#\s]+)#([^\s\-]+[^\s]*)\s*\-/', re.MULTILINE)


def slugify_heading(title: str) -> str:
    """Converts a markdown heading title into a GitHub-compatible anchor slug."""
    # Remove markdown links, inline code, bold, italic
    text = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', title)
    text = re.sub(r'[`*_]', '', text)
    # Convert to lowercase
    text = text.lower().strip()
    # Replace non-alphanumeric (except hyphen and space) with empty string
    text = re.sub(r'[^a-z0-9\s\-]', '', text)
    # Replace spaces with hyphens
    text = re.sub(r'\s+', '-', text)
    return text


def collect_markdown_sections() -> Dict[str, Dict[str, str]]:
    """
    Scans all markdown files in docs/ and references/ and returns a mapping:
    rel_path -> { anchor_slug -> heading_title }
    """
    sections = {}
    for doc_dir in DOC_DIRS:
        if not doc_dir.exists():
            continue
        for md_file in sorted(doc_dir.glob("**/*.md")):
            rel_path = md_file.relative_to(REPO_ROOT).as_posix()
            try:
                content = md_file.read_text(encoding="utf-8")
            except Exception as e:
                print(f"[!] Warning: Could not read {rel_path}: {e}")
                continue
            
            file_sections = {}
            heading_counts: Dict[str, int] = {}
            
            for match in HEADING_REGEX.finditer(content):
                title = match.group(2).strip()
                slug = slugify_heading(title)
                
                # Handle duplicate slugs
                if slug in heading_counts:
                    heading_counts[slug] += 1
                    unique_slug = f"{slug}-{heading_counts[slug]}"
                else:
                    heading_counts[slug] = 0
                    unique_slug = slug
                    
                file_sections[unique_slug] = title
                
            sections[rel_path] = file_sections
    return sections


def load_reference_registry() -> Dict[str, dict]:
    """Loads references.json (docs/REFERENCE_INDEX.md #1) into slug -> entry.

    Returns {} if the file does not exist at all (registry migration may not
    have started yet on this branch). A file that DOES exist but fails to
    parse, or contains an entry missing its required 'slug' field, is a hard
    failure -- same "no silently-skipped malformed data" discipline this
    project applies elsewhere (scripts/check_gates.py's allowlist parser).
    """
    if not REFERENCES_JSON_PATH.exists():
        return {}
    try:
        entries = json.loads(REFERENCES_JSON_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        print(f"[!] FATAL: {REFERENCES_JSON_PATH.name} exists but is not valid JSON: {e}")
        sys.exit(1)
    registry: Dict[str, dict] = {}
    for entry in entries:
        slug = entry.get("slug")
        if not slug:
            print(f"[!] FATAL: an entry in {REFERENCES_JSON_PATH.name} is missing its required 'slug' field: {entry}")
            sys.exit(1)
        registry[slug] = entry
    return registry


def collect_ref_citations() -> List[Dict]:
    """
    Scans all .lean files in the repository for `/- REF: target#anchor -/`
    annotations. Returns a flat list of { lean_file, lean_line, target_path,
    target_anchor } -- one entry per citation found.

    Deliberately NOT coupled to whatever declaration (if any) follows a
    citation: every `REF:`-shaped line is captured unconditionally by a
    single regex pass, independent of whether the text after it looks like
    a recognized Lean declaration. This is the fix for the defect this
    script's own module docstring describes -- a citation used to be
    silently dropped whenever the following declaration didn't match
    `LEAN_DECL_REGEX` (anonymous `instance`, `abbrev`, `initialize`, or any
    future keyword this script's author hadn't thought to list). Since
    citation validity never actually depended on parsing a declaration to
    begin with, removing that coupling is strictly more robust, not a
    behavior change for any citation that WAS already being validated.
    """
    citations = []

    lean_files = sorted(REPO_ROOT.glob("**/*.lean"))

    for lean_file in lean_files:
        # Skip build artifacts
        if ".lake" in lean_file.parts or ".system_generated" in lean_file.parts:
            continue

        rel_path = lean_file.relative_to(REPO_ROOT).as_posix()
        try:
            lines = lean_file.read_text(encoding="utf-8").splitlines()
        except Exception:
            continue

        for line_num, line in enumerate(lines, start=1):
            ref_match = REF_REGEX.search(line)
            if ref_match:
                target_path = ref_match.group(1).replace("\\", "/")
                target_anchor = ref_match.group(2)
                citations.append({
                    "lean_file": rel_path,
                    "lean_line": line_num,
                    "target_path": target_path,
                    "target_anchor": target_anchor
                })

    return citations


def main():
    print("=" * 70)
    print(" gasm Citation Validity Verifier (Law 3) -- see also `lake exe check_refs_coverage`")
    print("=" * 70)

    sections = collect_markdown_sections()
    total_sections = sum(len(s) for s in sections.values())
    docs_sections = sum(len(s) for p, s in sections.items() if p.startswith("docs/"))
    refs_sections = sum(len(s) for p, s in sections.items() if p.startswith("references/"))

    print(f"[*] Indexed {len(sections)} Markdown files ({total_sections} total sections):")
    print(f"    - Design Specs (docs/): {docs_sections} sections")
    print(f"    - Reference Manuals (references/): {refs_sections} sections")

    citations = collect_ref_citations()
    print(f"[*] Found {len(citations)} Lean citations across the repository.")

    registry = load_reference_registry()
    if registry:
        print(f"[*] Loaded {len(registry)} registered slug(s) from {REFERENCES_JSON_PATH.name}.")

    # 1. Validate Citations (Check for broken links)
    broken_citations = []
    referenced_sections: Set[Tuple[str, str]] = set()
    slug_citations_checked = 0

    for c in citations:
        doc_path = c["target_path"]
        anchor = c["target_anchor"]

        if "/" not in doc_path:
            # references.json slug citation (docs/REFERENCE_INDEX.md #6.5).
            # Existence-only: this script has no cache to check the anchor
            # against (see module docstring) -- a missing slug is still a
            # hard failure, an existing slug is accepted without an anchor
            # check, not silently treated as fully verified.
            if doc_path not in registry:
                broken_citations.append((c, f"Slug '{doc_path}' not found in {REFERENCES_JSON_PATH.name}"))
            else:
                slug_citations_checked += 1
            continue

        if doc_path not in sections:
            broken_citations.append((c, f"Target file '{doc_path}' not found in docs/ or references/"))
        elif anchor not in sections[doc_path]:
            broken_citations.append((c, f"Anchor '#{anchor}' not found in '{doc_path}'"))
        else:
            referenced_sections.add((doc_path, anchor))
            
    # 2. Report citation validity
    print("\n--- CITATION VALIDITY CHECK (Law 3) ---")
    has_errors = False

    if broken_citations:
        has_errors = True
        print(f"[!] FAILED: Found {len(broken_citations)} broken citation(s):")
        for c, reason in broken_citations:
            print(f"    - {c['lean_file']}:{c['lean_line']} -> {reason}")
    else:
        print("[+] All Lean citation references point to valid specification sections.")
    if slug_citations_checked:
        print(f"    ({slug_citations_checked} of these are references.json slug citations, "
              f"existence-checked only -- anchor-level checking needs scripts/check_references.py's "
              f"cache, not yet present in this tree; see module docstring.)")

    print("\n[i] Un-cited Lean declaration detection (Law 1) is NOT performed by this script --")
    print("    run `lake exe check_refs_coverage` (Tools/CheckRefsCoverage.lean), which walks the")
    print("    COMPILED ENVIRONMENT rather than source text so no declaration form can hide from")
    print("    it. See that tool's own module docstring and docs/REVIEW.md #4.1.2 for why the two")
    print("    checks are independent mechanisms rather than one script doing both jobs.")

    # 3. Report Unreferenced Design Backlog (docs/)
    # docs/adr/ and docs/tasks/ headings stay INDEXED above (citable anchors,
    # broken-ref detection still applies to them) but are excluded from this
    # backlog report/count: they are process records (decision history, task
    # briefs), not unimplemented design specifications (PLAN.md's stated
    # rationale for why they don't belong in the "what's left to build" list).
    print("\n--- UNREFERENCED DESIGN SPECIFICATION BACKLOG (docs/) ---")
    doc_unref_count = 0
    for doc_path, file_sections in sections.items():
        if not doc_path.startswith("docs/"):
            continue
        if doc_path.startswith("docs/adr/") or doc_path.startswith("docs/tasks/"):
            continue
        doc_unref = []
        for anchor, title in file_sections.items():
            if (doc_path, anchor) not in referenced_sections:
                doc_unref.append((anchor, title))
                
        if doc_unref:
            print(f"\n[{doc_path}] ({len(doc_unref)} unreferenced section(s)):")
            for anchor, title in doc_unref:
                doc_unref_count += 1
                print(f"    - #{anchor} ({title})")
                
    # Coverage is a docs/-only metric (see docs_sections above): the numerator
    # must be scoped to docs/-prefixed sections too, or it silently counts
    # references/ citations against a docs/-only denominator (design-review
    # Finding 8 on docs/REFERENCE_INDEX.md — inflated the printed figure by
    # roughly 2x before this fix, and would have looked like a coverage
    # regression once references/ citations stop being indexable local
    # sections at all).
    total_ref = len([p for p in referenced_sections if p[0].startswith("docs/")])
    coverage = (total_ref / docs_sections * 100) if docs_sections > 0 else 0
    print("\n" + "=" * 70)
    print(f" SUMMARY: {total_ref}/{docs_sections} design specification sections referenced ({coverage:.1f}% coverage).")
    print(f" Backlog: {doc_unref_count} design specification section(s) pending formal realization.")
    print("=" * 70)
    
    if has_errors:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()

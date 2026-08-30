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
scripts/check_references.py - Reference Index validator for gasm

Design: docs/REFERENCE_INDEX.md (including the adversarial corrections recorded
there). Validates `REF: <slug>#<anchor>` citations
against `references.json` (the registry, at repository root) and a local,
gitignored cache at `.cache/references/`.

Two modes:

  --offline (default)
      Network-free. For every `REF: <slug>#<anchor>` citation found under the
      Lean tree, checks: (1) `references.json` itself parses and every entry
      passes schema validation; (2) the slug is registered; (3) the cache
      file for that slug is present; (4) the cache file's ACTUAL, freshly
      recomputed SHA-256 matches the `sha256` recorded in `references.json`
      (never a comparison between two recorded numbers -- see docs/
      REFERENCE_INDEX.md for why that distinction matters);
      (5) the anchor is well-formed per its entry's `anchor_mode` grammar,
      and resolves against the cached content where that mode supports a
      resolution check.

  --refresh [--slug S | --corpus C | --all]
      Fetches each targeted entry's `url`, recomputes SHA-256 of exactly
      what was fetched, and compares against the recorded `sha256`. On
      match: promotes the fetched bytes into the cache. On mismatch: STOPS
      and reports -- a hash is never silently rewritten (see --acknowledge-
      drift below). On fetch failure (timeout/DNS/4xx/5xx): hard failure.

  --acknowledge-drift --slug S --reviewer EMAIL --review-note TEXT
      The only way to record a re-pin after --refresh reports drift. Fetches
      `url` again, requires the freshly fetched content to be the one being
      promoted (so acknowledging cannot be used to paper over a *second*,
      unreviewed drift between the --refresh run and this command), writes
      the new sha256/fetched_date into references.json, and stamps
      last_reviewed/reviewer/review_note. Cannot be invoked without
      --reviewer and --review-note: there is no way to bump a hash without
      leaving an attributed trail.

  --self-test
      Network- and cache-free positive/negative controls for durable reviewer
      attribution, including a planted registry entry using a reserved domain.

Exit codes (every distinct failure class gets its own, checked in this
priority order when several apply in one run):

  0   success
  1   references.json missing, fails to parse as JSON, or an entry fails
      schema validation (unknown/missing required field, closed-vocabulary
      violation, empty edition/review_note, etc.) -- checked before any
      citation is examined.
  2   a `REF:` citation names a slug that is not registered in
      references.json.
  3   a cited slug is registered, but `.cache/references/<slug>.<ext>` does
      not exist (cold cache) -- --offline never falls back to fetching.
  4   a cited slug's cache file exists, but its FRESHLY RECOMPUTED SHA-256
      does not match the `sha256` recorded in references.json (corruption,
      truncation, tampering, or a hand-edited references.json entry that no
      longer matches what is actually cached).
  5   a citation's anchor does not parse under its entry's anchor_mode
      grammar (malformed locator).
  6   a citation's anchor parses but fails its mode's existence/range check
      (heading not found, JSON pointer unresolved, RFC section absent,
      C symbol absent, or a pdf-locator's page range fails
      PSTART <= PEND <= page_count).
  7   --refresh: a URL fetch failed (timeout, DNS, non-2xx).
  8   --refresh: SHA-256 drift detected (live content differs from the
      recorded pin) -- a FINDING requiring human review, never auto-applied.
  9   CLI misuse: e.g. --acknowledge-drift without --reviewer/--review-note,
      or an unresolved drift that --acknowledge-drift was asked to clear
      without re-observing that same drift first.

`--offline` never returns 0 while a citation was silently skipped: an
unrecognized citation shape (parses as neither a docs/-relative path nor a
registered slug) is exit 5, not a pass-through. A cold cache is always a
loud failure (exit 3), never a silent fetch-on-demand.
"""

import argparse
import hashlib
import ipaddress
import json
import re
import subprocess
import sys
import tempfile
import unicodedata
import urllib.request
from pathlib import Path
from typing import Dict, List, Optional, Tuple

if sys.stdout.encoding and sys.stdout.encoding.lower() not in ("utf-8", "utf8"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

REPO_ROOT = Path(__file__).resolve().parent.parent
REFERENCES_JSON = REPO_ROOT / "references.json"
CACHE_DIR = REPO_ROOT / ".cache" / "references"


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
              f"nested-worktree phantom-citation bug this enumeration exists to prevent).",
              file=sys.stderr)
        sys.exit(1)
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
        print(f"[!] FATAL: 'git ls-files' exited {proc.returncode}: {stderr}", file=sys.stderr)
        sys.exit(1)
    raw = proc.stdout.decode("utf-8", errors="replace")
    return [p for p in raw.split("\0") if p]

EXIT_OK = 0
EXIT_SCHEMA_ERROR = 1
EXIT_UNREGISTERED_SLUG = 2
EXIT_CACHE_MISSING = 3
EXIT_HASH_MISMATCH = 4
EXIT_MALFORMED_LOCATOR = 5
EXIT_ANCHOR_UNRESOLVED = 6
EXIT_FETCH_FAILED = 7
EXIT_DRIFT_DETECTED = 8
EXIT_BAD_ARGS = 9

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
}

REF_REGEX = re.compile(r'/\-\s*REF:\s*([^#\s]+)#([^\s\-]+[^\s]*)\s*\-/', re.MULTILINE)
HEADING_REGEX = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)

MEDIA_TYPE_EXT = {
    "markdown": ".md",
    "html": ".html",
    "pdf": ".pdf",
    "json": ".json",
    "plain-text": ".txt",
    "c-header": ".h",
    "c-source": ".cpp",
}

REQUIRED_FIELDS = [
    "slug", "corpus", "title", "url", "media_type", "sha256", "fetched_date",
    "edition", "license", "distribution", "anchor_mode", "last_reviewed",
    "reviewer", "review_note",
]

LICENSE_VOCAB = {
    "intel-sdm-unmodified-only": "unmodified-copy-only",
    "khronos-spec-copyright": "unmodified-copy-only",
    "khronos-headers-permissive": "no-restriction",
    "w3c-document-license": "attribution-required",
    "w3c-cla-fsa": "attribution-required",
    "apache-2.0-or-mit": "attribution-required",
    "ietf-rfc-1996-notice": "attribution-required",
    "zlib-license": "attribution-required",
    "mit-or-unlicense": "attribution-required",
    "cc-by-4.0": "attribution-required",
    "ti-unmodified-only": "unmodified-copy-only",
    "arm-unmodified-only": "unmodified-copy-only",
}
DISTRIBUTION_VOCAB = {"unmodified-copy-only", "no-restriction", "attribution-required", "unclear"}
ANCHOR_MODES = {"heading", "pdf-locator", "json-pointer", "rfc-section", "c-symbol"}
RESERVED_REVIEWER_DOMAINS = {"example.com", "example.net", "example.org", "localhost"}
RESERVED_REVIEWER_TLDS = {"example", "invalid", "local", "localhost", "test"}
REVIEWER_LOCAL_ATOM_RE = re.compile(r"[A-Za-z0-9!#$%&'*+/=?^_`{|}~-]+")
REVIEWER_DNS_LABEL_RE = re.compile(r"[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?")
REVIEWER_LEGACY_NUMERIC_TOKEN_RE = re.compile(r"(?:[0-9]+|0x[0-9a-f]*)")


class ValidationFailure(Exception):
    def __init__(self, code: int, message: str):
        super().__init__(message)
        self.code = code
        self.message = message


def _default_ignorable(codepoint: int) -> bool:
    return (codepoint == 0x034F or 0x115F <= codepoint <= 0x1160
            or 0x17B4 <= codepoint <= 0x17B5 or 0x180B <= codepoint <= 0x180F
            or 0x200B <= codepoint <= 0x200F or 0x202A <= codepoint <= 0x202E
            or 0x2060 <= codepoint <= 0x206F or codepoint == 0x3164
            or 0xFE00 <= codepoint <= 0xFE0F or codepoint == 0xFEFF
            or codepoint == 0xFFA0 or 0xFFF0 <= codepoint <= 0xFFF8
            or 0x1BCA0 <= codepoint <= 0x1BCA3 or 0x1D173 <= codepoint <= 0x1D17A
            or 0xE0000 <= codepoint <= 0xE0FFF)


def normalize_reviewer_attribution(reviewer: object) -> Tuple[Optional[str], Optional[str]]:
    """Validates the pinned reviewer-email subset and returns domain-canonicalized attribution."""
    if not isinstance(reviewer, str):
        return None, "must be a string email address"
    if len(reviewer) > 254:
        return None, "exceeds the 254-character accepted limit"
    for character in reviewer:
        codepoint = ord(character)
        if (unicodedata.category(character) in {"Cc", "Cf", "Cs", "Co", "Cn"}
                or _default_ignorable(codepoint)):
            return None, f"contains prohibited control/default-ignorable U+{codepoint:04X}"
    if reviewer.count("@") != 1:
        return None, "must contain exactly one ASCII '@' separator"
    local, domain_input = reviewer.split("@", 1)
    if not local or len(local) > 64:
        return None, "local part must contain 1..64 ASCII characters"
    atoms = local.split(".")
    if any(not atom or REVIEWER_LOCAL_ATOM_RE.fullmatch(atom) is None for atom in atoms):
        return None, "local part must use the unquoted ASCII dot-atom subset"
    if domain_input.startswith("[") or domain_input.endswith("]"):
        return None, "address-literal domains are outside the accepted attribution profile"
    try:
        domain = domain_input.encode("idna").decode("ascii").lower()
    except (UnicodeError, ValueError):
        return None, "domain is not valid under Python 3.12 built-in IDNA normalization"
    if domain.endswith(".."):
        return None, "normalized domain may have at most one trailing root dot"
    domain = domain[:-1] if domain.endswith(".") else domain
    try:
        ipaddress.ip_address(domain)
        return None, "numeric IP domains are outside the accepted attribution profile"
    except ValueError:
        pass
    if "." not in domain:
        return None, f"uses non-public single-label domain '{domain}'"
    if len(domain) > 253:
        return None, "normalized domain exceeds 253 ASCII characters"
    labels = domain.split(".")
    if any(REVIEWER_DNS_LABEL_RE.fullmatch(label) is None for label in labels):
        return None, f"normalized domain '{domain}' has a malformed DNS label"
    if 1 <= len(labels) <= 4 and all(
            REVIEWER_LEGACY_NUMERIC_TOKEN_RE.fullmatch(label) is not None for label in labels):
        return None, "legacy numeric host domains are outside the accepted attribution profile"
    if labels[-1].isdigit():
        return None, "numeric final DNS labels are outside the accepted attribution profile"
    if (any(domain == reserved or domain.endswith("." + reserved)
            for reserved in RESERVED_REVIEWER_DOMAINS)
            or domain.rsplit(".", 1)[-1] in RESERVED_REVIEWER_TLDS):
        return None, f"uses reserved/synthetic domain '{domain}'"
    canonical = f"{local}@{domain}"
    if len(canonical) > 254:
        return None, "canonical email exceeds the 254-character accepted limit"
    return canonical, None


def reviewer_attribution_error(reviewer: object) -> Optional[str]:
    """Returns why a reviewer email is unusable as durable attribution, if anything."""
    _, error = normalize_reviewer_attribution(reviewer)
    return error


# ---------------------------------------------------------------------------
# Schema
# ---------------------------------------------------------------------------

def load_registry() -> Dict[str, dict]:
    if not REFERENCES_JSON.exists():
        raise ValidationFailure(EXIT_SCHEMA_ERROR, f"{REFERENCES_JSON} does not exist.")
    try:
        raw = REFERENCES_JSON.read_text(encoding="utf-8")
        data = json.loads(raw)
    except Exception as e:
        raise ValidationFailure(EXIT_SCHEMA_ERROR, f"{REFERENCES_JSON} failed to parse as JSON: {e}")
    if not isinstance(data, list):
        raise ValidationFailure(EXIT_SCHEMA_ERROR, f"{REFERENCES_JSON} must be a JSON array at the top level.")

    by_slug: Dict[str, dict] = {}
    for i, entry in enumerate(data):
        if not isinstance(entry, dict):
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] is not an object.")
        for field in REQUIRED_FIELDS:
            if field not in entry:
                raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] missing required field '{field}'.")
            val = entry[field]
            if isinstance(val, str) and val.strip() == "":
                raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] field '{field}' is empty (required fields must be non-empty).")
        slug = entry["slug"]
        if slug in by_slug:
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json: duplicate slug '{slug}'.")
        normalized_reviewer, reviewer_error = normalize_reviewer_attribution(entry["reviewer"])
        if reviewer_error:
            raise ValidationFailure(EXIT_SCHEMA_ERROR,
                f"references.json[{i}] ({slug}): reviewer {reviewer_error}.")
        if entry["reviewer"] != normalized_reviewer:
            raise ValidationFailure(EXIT_SCHEMA_ERROR,
                f"references.json[{i}] ({slug}): reviewer must use canonical stored form "
                f"'{normalized_reviewer}'.")
        if entry["media_type"] not in MEDIA_TYPE_EXT:
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): unrecognized media_type '{entry['media_type']}'.")
        if entry["anchor_mode"] not in ANCHOR_MODES:
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): unrecognized anchor_mode '{entry['anchor_mode']}'.")
        if entry["license"] not in LICENSE_VOCAB:
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): unrecognized license token '{entry['license']}' (not in the closed vocabulary -- extend it deliberately, don't freelance a new string).")
        if entry["distribution"] not in DISTRIBUTION_VOCAB:
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): unrecognized distribution '{entry['distribution']}'.")
        expected_dist = LICENSE_VOCAB[entry["license"]]
        if entry["distribution"] != expected_dist and entry["distribution"] != "unclear":
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): distribution '{entry['distribution']}' disagrees with license '{entry['license']}''s expected '{expected_dist}'.")
        sha = entry["sha256"]
        if not re.fullmatch(r"[0-9a-f]{64}", sha):
            raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): sha256 is not 64 lowercase hex characters.")
        # page_count is REQUIRED for pdf-locator entries (Finding 4b) -- this
        # is the mandatory mechanism that catches a repeat of Finding 1 (a
        # locator whose page numbers are in the wrong document's frame).
        if entry["anchor_mode"] == "pdf-locator":
            if "page_count" not in entry:
                raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): anchor_mode is pdf-locator but 'page_count' is missing (required, not optional -- see docs/REFERENCE_INDEX.md Finding 4).")
            if not isinstance(entry["page_count"], int) or entry["page_count"] <= 0:
                raise ValidationFailure(EXIT_SCHEMA_ERROR, f"references.json[{i}] ({slug}): page_count must be a positive integer.")
        by_slug[slug] = entry
    return by_slug


# ---------------------------------------------------------------------------
# Citation collection (mirrors scripts/check_refs.py's Lean scanner)
# ---------------------------------------------------------------------------

def collect_slug_citations() -> List[Dict]:
    """Scans all .lean files; returns citations whose target has no '/' (i.e.
    is a `<slug>#<anchor>` citation, not a docs/-relative path -- see
    docs/REFERENCE_INDEX.md Sec6.5's dual-shape transition rule)."""
    citations = []
    for rel_path in sorted(p for p in git_tracked_files() if p.endswith(".lean")):
        lean_file = REPO_ROOT / rel_path
        if ".lake" in lean_file.parts or ".system_generated" in lean_file.parts:
            continue
        try:
            lines = lean_file.read_text(encoding="utf-8").splitlines()
        except Exception:
            continue
        for line_num, line in enumerate(lines, start=1):
            for m in REF_REGEX.finditer(line):
                target, anchor = m.group(1), m.group(2)
                if "/" in target:
                    continue  # docs/-relative path citation; scripts/check_refs.py's job.
                citations.append({
                    "lean_file": rel_path,
                    "lean_line": line_num,
                    "slug": target,
                    "anchor": anchor,
                })
    return citations


# ---------------------------------------------------------------------------
# pdf-locator grammar: vol=V;(instr=M|sec=S);part=P[;pp=A-B[;mp=ENCODED]]
#
# pp=/mp= are OPTIONAL (2026-08-27, adversarial review of the references/
# migration): the intel-sdm corpus's 267 citations' pp=/mp= values were
# derived from the -092US (Dec 2024) edition's frontmatter, but the only
# live-fetchable copy at the pinned URL is -078US (Dec 2022) -- two years of
# revisions move page numbers by hundreds, so those page ranges are
# systematically wrong against the actually-pinned bytes (see the intel-sdm
# entry's review_note in references.json). The semantic fields (vol=/instr=
# or sec=/part=) still resolve by lookup in any edition, so a citation
# without pp=/mp= is degraded (no page-precision locator) rather than
# unmoored (still names a real, findable section). Stripping the false
# precision rather than documenting it as wrong is the fix: a reader of a
# Lean REF: comment should never see a confident page number with no signal
# that it doesn't match what's actually pinned. The page data itself is not
# lost -- it survives in docs/intel_sdm_frontmatter.json, labelled there as
# -092US-relative.
# ---------------------------------------------------------------------------

PDF_LOCATOR_RE = re.compile(
    r'^vol=(?P<vol>1|2|3|4|index);'
    r'(?:instr=(?P<instr>[A-Za-z][A-Za-z0-9_]*)|sec=(?P<sec>[0-9]+(?:\.[0-9]+)*));'
    r'part=(?P<part>[^;]+)'
    r'(?:;pp=(?P<pstart>[0-9]+)-(?P<pend>[0-9]+)(?:;mp=(?P<mp>[^;]+))?)?$'
)


def check_pdf_locator(anchor: str, entry: dict) -> None:
    m = PDF_LOCATOR_RE.match(anchor)
    if not m:
        raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}' does not match the pdf-locator grammar vol=V;(instr=M|sec=S);part=P[;pp=A-B[;mp=...]]")
    if not m.group("part"):
        raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}': part= is empty.")
    if m.group("pstart") is not None:
        # pp= is present (an entry/citation pair that DOES trust its page
        # numbers against the pinned bytes) -- validate it as before.
        pstart, pend = int(m.group("pstart")), int(m.group("pend"))
        if pstart > pend:
            raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': pp={pstart}-{pend} has pstart > pend.")
        page_count = entry["page_count"]  # required by schema validation above
        if pend > page_count:
            raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': pp end {pend} exceeds registered page_count {page_count} for slug '{entry['slug']}'.")


# ---------------------------------------------------------------------------
# heading grammar (reused algorithm from scripts/check_refs.py)
# ---------------------------------------------------------------------------

def slugify_heading(title: str) -> str:
    text = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', title)
    text = re.sub(r'[`*_]', '', text)
    text = text.lower().strip()
    text = re.sub(r'[^a-z0-9\s\-]', '', text)
    text = re.sub(r'\s+', '-', text)
    return text


def strip_html_tags_for_headings(html: str) -> str:
    """Minimal HTML->heading-text extraction: pulls <h1>-<h6> contents as
    markdown-style '#' lines so slugify_heading can run over them uniformly.
    Not a full HTML->Markdown conversion -- there is no full-body conversion
    path in this project any more (scripts/regenerate_references.py, which
    had one, is deleted along with the vendored references/ tree it wrote
    into -- docs/REFERENCE_INDEX.md #7) -- this only needs to recover
    heading TEXT for anchor checking, which this simpler pass has been
    sufficient for (verified against 12 real fetched WebAssembly spec
    pages, 99/99 citation anchors resolved -- see docs/REFERENCE_INDEX.md)."""
    lines = []
    for m in re.finditer(r'<h([1-6])[^>]*>(.*?)</h\1>', html, re.DOTALL | re.IGNORECASE):
        level, inner = m.group(1), m.group(2)
        text = re.sub(r'<[^>]+>', '', inner)
        text = text.replace('&amp;', '&').replace('&lt;', '<').replace('&gt;', '>').replace('&#39;', "'").replace('&quot;', '"')
        lines.append('#' * int(level) + ' ' + text.strip())
    return "\n\n".join(lines)


def derive_headings(cache_path: Path, media_type: str) -> Dict[str, str]:
    text = cache_path.read_text(encoding="utf-8", errors="replace")
    if media_type == "html":
        text = strip_html_tags_for_headings(text)
    sections: Dict[str, str] = {}
    counts: Dict[str, int] = {}
    for m in HEADING_REGEX.finditer(text):
        title = m.group(2).strip()
        slug = slugify_heading(title)
        if slug in counts:
            counts[slug] += 1
            slug = f"{slug}-{counts[slug]}"
        else:
            counts[slug] = 0
        sections[slug] = title
    return sections


def check_heading(anchor: str, entry: dict, cache_path: Path) -> None:
    if not re.fullmatch(r'[a-z0-9\-]+', anchor):
        raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}' is not a well-formed heading slug.")
    sections = derive_headings(cache_path, entry["media_type"])
    if anchor not in sections:
        raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '#{anchor}' not found among {entry['slug']}'s derived headings.")


# ---------------------------------------------------------------------------
# json-pointer grammar: "<key>/<key>/..." resolved against the cached JSON;
# for a list-of-objects value, a path segment may instead match an object's
# "opname" field (the documented convention for spirv.core.grammar.json-
# shaped corpora, e.g. "instructions/OpNop").
# ---------------------------------------------------------------------------

def check_json_pointer(anchor: str, entry: dict, cache_path: Path) -> None:
    if not anchor or anchor.startswith("/") and anchor == "/":
        raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}' is empty.")
    try:
        data = json.loads(cache_path.read_text(encoding="utf-8"))
    except Exception as e:
        raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"cached JSON for '{entry['slug']}' failed to parse: {e}")
    node = data
    for seg in anchor.strip("/").split("/"):
        if not seg:
            raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}' has an empty path segment.")
        if isinstance(node, dict):
            if seg not in node:
                raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': key '{seg}' not found.")
            node = node[seg]
        elif isinstance(node, list):
            match = next((item for item in node if isinstance(item, dict) and item.get("opname") == seg), None)
            if match is None:
                raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': no list item with opname '{seg}'.")
            node = match
        else:
            raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': cannot descend into '{seg}' (not a dict or opname-keyed list).")


# ---------------------------------------------------------------------------
# rfc-section grammar: sec=<N> or sec=<N.N.N...>
# ---------------------------------------------------------------------------

RFC_SECTION_RE = re.compile(r'^sec=([0-9]+(?:\.[0-9]+)*)$')
RFC_HEADING_LINE_RE = re.compile(r'^\s*(\d+(?:\.\d+)*)\.?\s+[A-Z]')


def check_rfc_section(anchor: str, entry: dict, cache_path: Path) -> None:
    m = RFC_SECTION_RE.match(anchor)
    if not m:
        raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}' does not match rfc-section grammar sec=<N[.N...]>")
    secnum = m.group(1)
    text = cache_path.read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        hm = RFC_HEADING_LINE_RE.match(line)
        if hm and hm.group(1) == secnum:
            return
    raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': no line matching a '{secnum}. ...' section heading found in cached text for '{entry['slug']}'.")


# ---------------------------------------------------------------------------
# c-symbol grammar: sym=<identifier>
# ---------------------------------------------------------------------------

C_SYMBOL_RE = re.compile(r'^sym=([A-Za-z_][A-Za-z0-9_]*)$')


def check_c_symbol(anchor: str, entry: dict, cache_path: Path) -> None:
    m = C_SYMBOL_RE.match(anchor)
    if not m:
        raise ValidationFailure(EXIT_MALFORMED_LOCATOR, f"anchor '{anchor}' does not match c-symbol grammar sym=<identifier>")
    ident = m.group(1)
    text = cache_path.read_text(encoding="utf-8", errors="replace")
    if not re.search(r'\b' + re.escape(ident) + r'\b', text):
        raise ValidationFailure(EXIT_ANCHOR_UNRESOLVED, f"anchor '{anchor}': symbol '{ident}' not found in cached text for '{entry['slug']}' (existence check only -- not a semantic check of what the declaration means).")


ANCHOR_CHECKERS = {
    "pdf-locator": lambda anchor, entry, cache_path: check_pdf_locator(anchor, entry),
    "heading": check_heading,
    "json-pointer": check_json_pointer,
    "rfc-section": check_rfc_section,
    "c-symbol": check_c_symbol,
}


# ---------------------------------------------------------------------------
# --offline
# ---------------------------------------------------------------------------

def cache_path_for(entry: dict) -> Path:
    ext = MEDIA_TYPE_EXT[entry["media_type"]]
    return CACHE_DIR / f"{entry['slug']}{ext}"


def sha256_of_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_cache_integrity(entry: dict) -> Path:
    """Returns the cache path if present and hash-verified; raises otherwise.
    ALWAYS recomputes SHA-256 from the bytes on disk -- never compares one
    recorded number to another (the failure class documented in
    docs/REFERENCE_INDEX.md)."""
    path = cache_path_for(entry)
    if not path.exists():
        raise ValidationFailure(EXIT_CACHE_MISSING, f"slug '{entry['slug']}': cache file {path} does not exist (cold cache). Run --refresh --slug {entry['slug']} deliberately; --offline never fetches.")
    actual = sha256_of_file(path)
    if actual != entry["sha256"]:
        raise ValidationFailure(EXIT_HASH_MISMATCH, f"slug '{entry['slug']}': cache file {path} sha256 is {actual}, but references.json records {entry['sha256']}. The cache and the index disagree -- this is a hard failure, not a warning (corrupted/truncated/tampered cache file, or a hand-edited references.json entry).")
    return path


def run_offline() -> int:
    print("=" * 70)
    print(" gasm Reference Index Verifier (--offline)")
    print("=" * 70)

    try:
        registry = load_registry()
    except ValidationFailure as vf:
        print(f"[!] SCHEMA FAILURE (exit {vf.code}): {vf.message}")
        return vf.code
    print(f"[*] Loaded references.json: {len(registry)} registered slug(s).")

    citations = collect_slug_citations()
    print(f"[*] Found {len(citations)} slug-form REF: citation(s) in the Lean tree.")

    # Priority-ordered failure buckets.
    failures_by_code: Dict[int, List[str]] = {}
    verified_cache: Dict[str, Path] = {}

    def record(code: int, msg: str):
        failures_by_code.setdefault(code, []).append(msg)

    cited_slugs = set()
    for c in citations:
        slug, anchor = c["slug"], c["anchor"]
        loc = f"{c['lean_file']}:{c['lean_line']}"
        cited_slugs.add(slug)
        if slug not in registry:
            record(EXIT_UNREGISTERED_SLUG, f"{loc}: REF: {slug}#{anchor} -- slug '{slug}' is not registered in references.json.")
            continue
        entry = registry[slug]
        try:
            if slug not in verified_cache:
                verified_cache[slug] = verify_cache_integrity(entry)
        except ValidationFailure as vf:
            record(vf.code, f"{loc}: {vf.message}")
            continue
        cache_path = verified_cache[slug]
        checker = ANCHOR_CHECKERS[entry["anchor_mode"]]
        try:
            checker(anchor, entry, cache_path)
        except ValidationFailure as vf:
            record(vf.code, f"{loc}: {vf.message}")

    print(f"[*] {len(cited_slugs)} distinct slug(s) cited.")
    print()

    if not failures_by_code:
        print("[+] All slug-form citations resolve: registered, cache-hash-verified, anchor-checked.")
        print("=" * 70)
        return EXIT_OK

    for code in sorted(failures_by_code):
        msgs = failures_by_code[code]
        print(f"--- exit {code}: {len(msgs)} failure(s) ---")
        for m in msgs:
            print(f"    - {m}")
        print()

    primary = min(failures_by_code)
    print("=" * 70)
    print(f" FAILED. Primary exit code: {primary} (see docs/check_references.py docstring for the exit-code table).")
    print("=" * 70)
    return primary


# ---------------------------------------------------------------------------
# --refresh / --acknowledge-drift
# ---------------------------------------------------------------------------

def fetch_bytes(url: str) -> bytes:
    req = urllib.request.Request(url, headers=HEADERS)
    with urllib.request.urlopen(req, timeout=120) as resp:
        return resp.read()


def run_refresh(args) -> int:
    try:
        registry = load_registry()
    except ValidationFailure as vf:
        print(f"[!] SCHEMA FAILURE (exit {vf.code}): {vf.message}")
        return vf.code

    if args.slug:
        targets = [args.slug] if args.slug in registry else []
        if not targets:
            print(f"[!] Unknown slug '{args.slug}'.")
            return EXIT_UNREGISTERED_SLUG
    elif args.corpus:
        targets = [s for s, e in registry.items() if e["corpus"] == args.corpus]
    elif args.all:
        targets = list(registry.keys())
    else:
        print("[!] --refresh requires --slug, --corpus, or --all.")
        return EXIT_BAD_ARGS

    worst = EXIT_OK
    for slug in targets:
        entry = registry[slug]
        print(f"[*] Fetching {slug} <- {entry['url']}")
        try:
            data = fetch_bytes(entry["url"])
        except Exception as e:
            print(f"[!] exit {EXIT_FETCH_FAILED}: fetch failed for '{slug}': {e}")
            worst = max(worst, EXIT_FETCH_FAILED)
            continue
        actual = hashlib.sha256(data).hexdigest()
        if actual == entry["sha256"]:
            CACHE_DIR.mkdir(parents=True, exist_ok=True)
            cache_path_for(entry).write_bytes(data)
            print(f"[+] {slug}: sha256 matches recorded pin. Cache updated ({len(data)} bytes).")
        else:
            print(f"[!] exit {EXIT_DRIFT_DETECTED}: DRIFT DETECTED for '{slug}'")
            print(f"    recorded sha256: {entry['sha256']}")
            print(f"    live sha256:     {actual}")
            print(f"    url:             {entry['url']}")
            print(f"    references.json NOT modified. Cache NOT updated. See docs/REFERENCE_INDEX.md Sec4.")
            worst = max(worst, EXIT_DRIFT_DETECTED)
    return worst


def _set_repin_metadata(raw: list, slug: str, actual: str, today: str,
                        reviewer: object, review_note: str) -> str:
    """Updates re-pin metadata and returns the canonical reviewer written to the registry."""
    normalized_reviewer, reviewer_error = normalize_reviewer_attribution(reviewer)
    if reviewer_error or normalized_reviewer is None:
        raise ValueError(reviewer_error or "reviewer normalization failed")
    for entry in raw:
        if entry["slug"] == slug:
            entry["sha256"] = actual
            entry["fetched_date"] = today
            entry["last_reviewed"] = today
            entry["reviewer"] = normalized_reviewer
            entry["review_note"] = review_note
    return normalized_reviewer


def run_acknowledge_drift(args) -> int:
    if not args.reviewer or not args.review_note:
        print("[!] --acknowledge-drift requires --reviewer and --review-note.")
        return EXIT_BAD_ARGS
    if not args.slug:
        print("[!] --acknowledge-drift requires --slug.")
        return EXIT_BAD_ARGS
    normalized_reviewer, reviewer_error = normalize_reviewer_attribution(args.reviewer)
    if reviewer_error:
        print(f"[!] --acknowledge-drift reviewer {reviewer_error}.")
        return EXIT_BAD_ARGS
    try:
        registry = load_registry()
    except ValidationFailure as vf:
        print(f"[!] SCHEMA FAILURE (exit {vf.code}): {vf.message}")
        return vf.code
    if args.slug not in registry:
        print(f"[!] Unknown slug '{args.slug}'.")
        return EXIT_UNREGISTERED_SLUG
    entry = registry[args.slug]
    print(f"[*] Re-fetching {args.slug} <- {entry['url']} to acknowledge drift...")
    try:
        data = fetch_bytes(entry["url"])
    except Exception as e:
        print(f"[!] exit {EXIT_FETCH_FAILED}: fetch failed: {e}")
        return EXIT_FETCH_FAILED
    actual = hashlib.sha256(data).hexdigest()
    if actual == entry["sha256"]:
        print("[!] No drift observed on this fetch (live content already matches the recorded pin) -- nothing to acknowledge.")
        return EXIT_BAD_ARGS

    import datetime
    today = datetime.date.today().isoformat()
    raw = json.loads(REFERENCES_JSON.read_text(encoding="utf-8"))
    _set_repin_metadata(raw, args.slug, actual, today, normalized_reviewer, args.review_note)
    REFERENCES_JSON.write_text(json.dumps(raw, indent=2) + "\n", encoding="utf-8")
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cache_path_for(entry).write_bytes(data)
    print(f"[+] Re-pinned '{args.slug}': sha256={actual}, reviewer={normalized_reviewer}. references.json and cache updated.")
    return EXIT_OK


def run_self_test() -> int:
    global REFERENCES_JSON
    idna_expanding_overlong = "a" * 64 + "@" + ".".join(["ü" * 57] * 3)
    positive = {
        "craig.tiller@gmail.com": "craig.tiller@gmail.com",
        "Person+refs@Team.Company.": "Person+refs@team.company",
        "person@bücher.de": "person@xn--bcher-kva.de",
        "person@bücher.de。": "person@xn--bcher-kva.de",
        "person@0x7f.organization.dev": "person@0x7f.organization.dev",
    }
    negative = {
        "codex.graphics@local.invalid": "reserved/synthetic domain",
        "reviewer@project.test": "reserved/synthetic domain",
        "reviewer@example.com": "reserved/synthetic domain",
        "person@sub.example.com": "reserved/synthetic domain",
        "person@ｅｘａｍｐｌｅ.com": "reserved/synthetic domain",
        "person@exam\u200bple.com": "control/default-ignorable",
        "reviewer@machine": "single-label domain",
        "reviewer@workstation.local": "reserved/synthetic domain",
        "person@127.0.0.1": "numeric IP domains",
        "person@127.000.000.001": "legacy numeric host domains",
        "person@foo.123": "numeric final DNS labels",
        "person@0x7f.0.0.1": "legacy numeric host domains",
        "person@0x7f.0.0.01": "legacy numeric host domains",
        "person@0x7f.0.0.0x1": "legacy numeric host domains",
        "person@0x7f.0x0.0x0.0x1": "legacy numeric host domains",
        "person@127.0.0x1": "legacy numeric host domains",
        "person@0x7f.0x1": "legacy numeric host domains",
        "person@0x.0.0.0x1": "legacy numeric host domains",
        "person@0.0.0.0x": "legacy numeric host domains",
        "person@0x.0x.0x.0x": "legacy numeric host domains",
        "person@0x7f.0.0.0x": "legacy numeric host domains",
        "person@[127.0.0.1]": "address-literal domains",
        "person@[::1]": "address-literal domains",
        "person@192.0.2.1": "numeric IP domains",
        "person@-bad.example.dev": "malformed DNS label",
        "person@bad-.example.dev": "malformed DNS label",
        "person@bad..example.dev": "IDNA normalization",
        '"person"@organization.dev': "unquoted ASCII dot-atom",
        "pérson@organization.dev": "unquoted ASCII dot-atom",
        "a..b@organization.dev": "unquoted ASCII dot-atom",
        "not-an-email": "exactly one ASCII '@'",
        17: "string email address",
        idna_expanding_overlong: "canonical email exceeds",
    }
    failures = []
    for reviewer, expected in positive.items():
        normalized, error = normalize_reviewer_attribution(reviewer)
        if error is not None or normalized != expected:
            failures.append(f"positive {reviewer!r}: normalized={normalized!r}, error={error!r}")
    for reviewer, expected_fragment in negative.items():
        error = reviewer_attribution_error(reviewer)
        if error is None or expected_fragment not in error:
            failures.append(f"negative {reviewer!r}: error={error!r}, expected {expected_fragment!r}")
    writer_control = [{"slug": "writer-control", "reviewer": "old@example.dev"}]
    written = _set_repin_metadata(
        writer_control, "writer-control", "a" * 64, "2026-08-30",
        "Person+refs@BÜCHER.DE。", "writer canonicalization control")
    if written != "Person+refs@xn--bcher-kva.de" or writer_control[0]["reviewer"] != written:
        failures.append(
            f"production writer failed to persist canonical reviewer: {writer_control!r}, {written!r}")
    rejected_writer_control = [{"slug": "writer-control", "reviewer": "unchanged@organization.dev"}]
    try:
        _set_repin_metadata(
            rejected_writer_control, "writer-control", "b" * 64, "2026-08-30",
            idna_expanding_overlong, "writer overlength control")
        failures.append("production writer accepted an IDNA-expanded reviewer over 254 characters")
    except ValueError as error:
        if "canonical email exceeds" not in str(error):
            failures.append(f"production writer rejected overlength reviewer for wrong reason: {error}")
        if rejected_writer_control[0]["reviewer"] != "unchanged@organization.dev":
            failures.append("production writer mutated registry before rejecting overlength reviewer")
    original_path = REFERENCES_JSON
    try:
        # Positive integration control: the repository's real registry reaches the new schema check.
        load_registry()
        with tempfile.TemporaryDirectory(prefix="gasm-reference-reviewer-") as directory:
            planted_path = Path(directory) / "references.json"
            planted_controls = list(negative.items())
            for planted_reviewer, expected_fragment in planted_controls:
                planted = json.loads(original_path.read_text(encoding="utf-8"))
                planted[0]["reviewer"] = planted_reviewer
                planted_path.write_text(json.dumps(planted), encoding="utf-8")
                REFERENCES_JSON = planted_path
                try:
                    load_registry()
                    failures.append(f"planted reviewer {planted_reviewer!r} passed full registry validation")
                except ValidationFailure as failure:
                    if failure.code != EXIT_SCHEMA_ERROR or expected_fragment not in failure.message:
                        failures.append(f"planted reviewer failed for wrong reason: {failure.message}")
    except (OSError, ValueError, ValidationFailure) as failure:
        failures.append(f"positive registry control failed: {failure}")
    finally:
        REFERENCES_JSON = original_path
    if failures:
        for failure in failures:
            print(f"[!] reviewer-attribution self-test: {failure}")
        return EXIT_SCHEMA_ERROR
    print("[+] reviewer-attribution self-test: positive and negative controls passed.")
    return EXIT_OK


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--offline", action="store_true", help="Network-free validation against the local cache (default).")
    parser.add_argument("--refresh", action="store_true", help="Fetch and re-verify targeted entries.")
    parser.add_argument("--acknowledge-drift", action="store_true", help="Record a reviewed re-pin after --refresh reported drift.")
    parser.add_argument("--slug", help="Target a single slug (--refresh / --acknowledge-drift).")
    parser.add_argument("--corpus", help="Target all slugs in a corpus (--refresh).")
    parser.add_argument("--all", action="store_true", help="Target every registered slug (--refresh).")
    parser.add_argument("--reviewer", help="Reviewer email (--acknowledge-drift).")
    parser.add_argument("--review-note", help="Free-text review note (--acknowledge-drift).")
    parser.add_argument("--self-test", action="store_true",
                        help="Run positive/negative reviewer-attribution controls without network or cache.")
    args = parser.parse_args()

    if args.self_test:
        return run_self_test()
    if args.acknowledge_drift:
        return run_acknowledge_drift(args)
    if args.refresh:
        return run_refresh(args)
    return run_offline()


if __name__ == "__main__":
    sys.exit(main())

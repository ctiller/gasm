# Reference Index — Replacing Vendored `references/` with `references.json` + Slug Citations

**Status: Law 5 (Stop-and-Design Invariant) design document.** This is a design, not an
implementation — no code in this repository is changed by this document. §8's Law 4/Law 6
amendment text is explicitly **PROPOSED**, pending the owner's ratification; the owner ratifies
laws, this document does not. Everything else here (schema, validator, migration plan) is ready
to execute once reviewed.

**Why this exists.** `gasm` is going open-source under Apache-2.0.
[`docs/THIRD_PARTY_LICENSES.md`](THIRD_PARTY_LICENSES.md) found that `references/intel_sdm/`
(928 files, 89% of the corpus), `references/vulkan/` (72 files), and five `references/spirv/`
prose chapters are **NOT REDISTRIBUTABLE** — their upstream licenses permit an unmodified copy
only, and this repository stores reformatted, table-flattened, per-chapter Markdown derivatives.
267 `REF:` citations depend on `intel_sdm/` alone: the entire `Gasm/Targets/X86_64/**` surface
(encoder, decoder, instruction registry, both fuzzers, the performance model). **The owner has
since ruled more broadly than redistributability alone requires: no third-party documentation
prose ships in the repository at all, for any corpus, regardless of license** — not just the
non-redistributable ones. W3C specs, RFCs, the CC-BY-4.0 Microsoft docs pages, the permissively-
licensed SPIR-V grammar JSON: all of it leaves, on the same uniform terms as the corpora that were
never legally vendorable to begin with. Redistributability is therefore no longer *why* this
migration happens — it is why `intel_sdm`/`vulkan`/`spirv`-prose specifically could never simply
stay — but the design and its end state are identical either way, and are stated below without
depending on that narrower rationale.

**The resolved design, per the owner's ruling:** `references/` is **deleted in its entirety, down
to zero content files, for every corpus, no exceptions and no hybrid retention** — including
material that was always legally clearable to vendor (wasi, zlib, png, the CC-BY-4.0 windows
files, `spirv.core.grammar.json`). **End state:** no `REF:` citation resolves to a path under
`references/`, and the directory does not exist in the tree at the point this repository is
published. This is not a transitional or hybrid arrangement that could later be read as
permanent-by-default — it is the terminal state, and §6.5's migration-window accommodation for
both citation shapes side by side is exactly that: a temporary bridge during the migration itself,
removed in the same commit that removes the directory (§6.5, §6.6). Every external document this
project cites is instead registered exactly once, in one flat index file (`references.json`, at
repository root), by **slug**, **canonical URL**, and **SHA-256 of its exact fetched content**.
`REF:` annotations name a slug and an anchor within that document (`REF: <slug>#<anchor>`); a
validator (`scripts/check_references.py`) checks citations against a local, gitignored cache built
from that index, never against a copy committed to the repository. Nothing copyrighted is
redistributed — the repository ships URLs and hashes, which are facts, not the upstream's
expression.

The owner's ruling settles a question this document originally posed as a tradeoff (hybrid vs.
uniform, §7): **uniform wins**, and it is simpler to specify and implement than hybrid would have
been — one schema, one cache, one drift policy, one validator code path, zero per-corpus
exceptions to keep straight. That simplicity is treated below as a genuine benefit of the
decision, not a consolation for foregoing hybrid. Registration in `references.json` — URLs and
hashes, never prose — is the **sole** mechanism for citing any external document from this point
forward; nothing in this design licenses vendoring text back into the repository under any future
circumstance, including a corpus whose license would clearly permit it (see §8.1).

---

## 1. Schema

### 1.1 File format: JSON, not YAML

The owner's brief proposed `references.yaml`. This design uses **`references.json`** instead,
and the reason is mechanical, not aesthetic: `gasm` has **no YAML dependency anywhere in the
repository**, by deliberate choice — `scripts/task_frontier.py` parses `docs/tasks/*.md`
frontmatter with a hand-rolled, intentionally-limited flat-key parser specifically to avoid
depending on a YAML library (see that file's module docstring: *"a flat YAML subset — no
external `yaml` dependency"*). Adopting `references.yaml` would mean either (a) adding the
project's first external Python dependency, in a repo whose stdlib-only tooling posture is a
running design choice, or (b) hand-rolling a *second*, more capable YAML-subset parser (the
reference index needs nested structure — a list of objects, each with several typed and some
optional fields — which is beyond what the existing flat parser handles; extending it risks
YAML's well-known footguns, e.g. the Norway-country-code problem, unquoted `no`/`off`/`on`
becoming booleans).

JSON needs neither: `json` is Python stdlib, already load-bearing in this exact subsystem
(`references/MANIFEST.provenance.json` today, parsed and written by
`scripts/regenerate_references.py`), and trivially reusable by the Lean-side tooling if it is
ever needed there (Lean's `Lean.Data.Json` is already in the toolchain; there is no equivalent
built-in YAML support). **Decision: `references.json`, one JSON array of entry objects, at
repository root** (replacing both `references/MANIFEST.sha256` and
`references/MANIFEST.provenance.json`, which move to repository root as this single file since
`references/` itself no longer exists — see §7).

### 1.2 Entry fields

```jsonc
{
  "slug": "intel-sdm",
  "corpus": "intel_sdm",
  "title": "Intel® 64 and IA-32 Architectures Software Developer's Manual (combined, Order Number 325462-092US, December 2024)",
  "url": "https://cdrdv2-public.intel.com/<TBD-at-registration>/325462-sdm.pdf",
  "archive_url": null,
  "media_type": "pdf",
  "sha256": "…64 hex chars, of the exact fetched bytes…",
  "fetched_date": "2026-08-27",
  "edition": "325462-092US",
  "page_count": 5363,
  "license": "intel-sdm-unmodified-only",
  "distribution": "unmodified-copy-only",
  "anchor_mode": "pdf-locator",
  "last_reviewed": "2026-08-27",
  "reviewer": "craig.tiller@gmail.com",
  "review_note": "Initial registration at time of references/ migration."
}
```

Illustrative, not actual output — `url` is a placeholder to be confirmed against Intel's real
distribution page at registration time (nothing in this repository has fetched it yet); the other
fields reflect what the committed side-table (`docs/intel_sdm_frontmatter.json`, extracted and
verified by full census — see §2.2) actually establishes. `page_count: 5363` is the highest
`page_end` observed across all 926 indexed files (the Index volume's own frontmatter), stated here
for illustration; the real registration step fixes it against the fetched PDF's own page count.

| Field | Type | Required | Meaning |
|---|---|---|---|
| `slug` | string | yes | Stable identifier, kebab-case, unique across the file. Never reused for a different document once retired (a dead slug is deleted, not repointed — see §4). |
| `corpus` | string | yes | Grouping label, one of the values `check_references.py --report` uses for the per-corpus backlog view (§9): `intel_sdm`, `vulkan`, `spirv`, `wasm`, `wasi`, `zlib`, `png`, `windows`, plus any added later. Purely organizational — the validator does not branch behavior on it. |
| `title` | string | yes | Human-readable document title, for error messages and the generated report. |
| `url` | string | yes | Canonical upstream URL. The thing `--refresh` fetches. |
| `archive_url` | string \| null | no | Optional Wayback Machine (or equivalent) snapshot URL. See §5 — recovery aid only, never an automatic substitute. |
| `media_type` | enum | yes | One of `markdown`, `html`, `pdf`, `json`, `plain-text`, `c-header`. Selects the anchor grammar (§2) and what `--refresh` does to verify an anchor. |
| `sha256` | string | yes | SHA-256, lowercase hex, of the exact bytes at `url` as of `fetched_date`. This is the pin. |
| `fetched_date` | string (ISO-8601 date) | yes | When `sha256` was computed. |
| `edition` | string | yes for `pdf-locator` entries, no otherwise | Free text: order number, revision, commit SHA, RFC number — whatever the upstream uses to distinguish editions. **Machine-checked for `pdf-locator` entries**: the validator hard-fails if empty, and the re-pin workflow (§4) treats any change to this field as *ipso facto* substantive — see §4 and §2.3's revision-policy note. Not machine-checked for other `anchor_mode`s, where content-level checking already exists. |
| `page_count` | integer | **yes for `pdf-locator` entries**, no otherwise | Total page count of the fetched PDF. Makes `PEND <= page_count` a mandatory bound check (§2.3) rather than the merely-optional one an earlier draft of this schema left it as. |
| `size_bytes` | integer | no | Byte length of the exact fetched content, alongside `sha256` as a cheap second pin — also what the drift report in §4 prints. |
| `license` | string | yes | A controlled vocabulary token identifying the upstream license/terms (see §1.3). Free text is not accepted — an unrecognized token is a hard parse failure, the same discipline `scripts/gate_allowlist.txt` and `scripts/license_allowlist.txt` already apply to their own controlled category fields. |
| `distribution` | enum | yes | One of `unmodified-copy-only`, `no-restriction`, `attribution-required`, `unclear`. Derived from `license` at registration time by a human, not inferred by the tool — this is a judgment call the audit already made per corpus in `docs/THIRD_PARTY_LICENSES.md` §1, carried into the schema so it travels with the citation instead of living only in a standalone audit document. `unclear` is a legitimate value (mirrors the audit's own `UNCLEAR` verdicts) and forces manual sign-off before an entry may ship — it is not a default. |
| `anchor_mode` | enum | yes | One of `heading` (markdown/html — GitHub-style anchor, checkable), `pdf-locator` (well-formedness-checkable only, §2.3), `json-pointer` (checkable), `rfc-section` (checkable against cached plain text, §2.5), `c-symbol` (checkable, §2.6). |
| `last_reviewed` | string (ISO-8601 date) | yes | Date a human last confirmed this entry's hash/URL/license fields are correct — set at registration, updated only by the re-pin workflow (§4), never by `--refresh` alone. |
| `reviewer` | string | yes | Who performed the last review (an email, matching the convention already used for `scripts/license_allowlist.txt`'s `<added-by>` field). |
| `review_note` | string | yes | Free text, non-empty. What the last review found (or, at registration, "initial registration"). |

Every field is required except `archive_url` and `size_bytes`, with `edition`/`page_count`
additionally required whenever `anchor_mode` is `pdf-locator` (both are load-bearing for that
grammar specifically — see §2.3, §4). A missing required field, an unrecognized
`media_type`/`distribution`/`anchor_mode` token, or an unrecognized `license` token is a hard
parse failure for the validator — the same "no silently-skipped malformed line" discipline
`scripts/check_gates.py`'s allowlist parser already applies (§4.1.1 of `docs/REVIEW.md`).

### 1.3 License vocabulary

A closed, hand-maintained list (extend it, don't freelance a new string inline), seeded from the
verdicts `docs/THIRD_PARTY_LICENSES.md` already reached:

| Token | Upstream | `distribution` |
|---|---|---|
| `intel-sdm-unmodified-only` | Intel SDM | `unmodified-copy-only` |
| `khronos-spec-copyright` | Vulkan / SPIR-V spec prose | `unmodified-copy-only` |
| `khronos-headers-permissive` | SPIRV-Headers (grammar JSON) | `no-restriction` |
| `w3c-document-license` | WebAssembly Core Spec | `attribution-required` |
| `w3c-cla-fsa` | WASI Specification | `attribution-required` |
| `apache-2.0-or-mit` | wasi-libc | `attribution-required` |
| `ietf-rfc-1996-notice` | RFC 1950/1951/1952/2083 | `attribution-required` |
| `zlib-license` | LodePNG | `attribution-required` |
| `mit-or-unlicense` | stb_image / stb_image_write | `attribution-required` |
| `cc-by-4.0` | MicrosoftDocs/win32 | `attribution-required` |
| `ti-unmodified-only` | TI / National Semiconductor datasheets | `unmodified-copy-only` |
| `arm-unmodified-only` | Arm Architecture Reference Manual, PL011 TRM, Semihosting | `unmodified-copy-only` |

### 1.4 What `anchor_bearing` collapses into

The brief asked for an explicit "is this document anchor-bearing" flag. This design does not add
a separate boolean for that — `anchor_mode` already answers it: every value names a real grammar
(§2), so every entry is anchor-bearing by construction. There is no "no anchor" mode, because a
document with no citable substructure has no reason to be registered at all (see §10 — this is
exactly the property that forces the four remaining hand-authored files to stop existing rather
than be accommodated).

---

## 2. Citation granularity and the per-media-type anchor grammar

**The owner's ruling on this (relayed mid-task) resolves what was posed as the central open
tradeoff: the slug covers the document; `REF:` names slug + anchor within the document,
uniformly, for every media type.** This is *not* a downgrade from today's section-level
citations — it preserves section-level granularity, including across all 267 SDM citations, by
specifying a formal locator grammar for media types (chiefly PDF) that have no native heading
structure a tool can parse. The citation shape is uniform:

```
/- REF: <slug>#<anchor> -/
```

where `<anchor>`'s grammar depends on the target entry's `anchor_mode`. What follows specifies
each grammar precisely and states, for each, exactly which properties the validator can check
mechanically and which it cannot — the brief's explicit ask, and the thing that would otherwise
get discovered by surprise rather than designed for.

### 2.1 `heading` (markdown, and HTML after in-memory conversion)

This is **today's mechanism**, unchanged in substance, but its exact algorithm must be stated
explicitly because it is *not* GitHub's own anchor algorithm and has caused confusion before.
`scripts/check_refs.py`'s `slugify_heading`:

1. Replaces `[text](url)` markdown links with just `text`.
2. **Strips backtick, asterisk, and underscore characters entirely** (not to hyphens — deleted).
   GitHub's own algorithm keeps underscores as literal characters and does not strip inline-code
   backticks/emphasis markers from the *rendered* anchor the same way; a heading like
   `` `read` is the universal binder `` slugifies here to `read-is-the-universal-binder`,
   whereas GitHub's renderer would produce a different string. **This project's anchors are only
   ever checked against this project's own algorithm — they are not required or expected to
   match what GitHub would render for the same heading**, and this document says so explicitly so
   nobody "fixes" a citation to match GitHub and breaks the actual check.
3. Lowercases.
4. Removes every character that isn't `[a-z0-9\s-]`.
5. Collapses whitespace runs to single hyphens.
6. Duplicate slugs within one file get `-1`, `-2`, … suffixes in heading order.

For an HTML upstream (the wasm W3C chapters, the CC-BY-4.0 windows pages), the validator does not
anchor-check against the raw HTML's own `id` attributes. It reuses the exact HTML→Markdown
conversion this project already has (`html_to_clean_markdown` / `sphinx_html_to_markdown` in
`scripts/regenerate_references.py`, surviving into the validator per §7) to produce the same
Markdown headings a contributor would have seen when the citation was first written, then runs
`slugify_heading` over those. This is deliberate continuity, not laziness: existing citations'
anchor spellings were derived from the *converted* Markdown, and re-deriving from raw HTML `id`s
would silently invalidate every existing anchor spelling for no benefit. **Checkable**: full
existence check, exactly as today — `--refresh` (or `--offline` against a warm cache) fails if
the anchor is not among the document's derived headings.

### 2.2 The Intel SDM problem this grammar exists to solve

Intel does not publish per-chapter or per-instruction web pages, and — corrected from an earlier
draft of this design — it does not distribute the SDM as four independently paginated PDFs either.
`docs/intel_sdm_frontmatter.json` (extracted from all 928 vendored files and committed to the
repository specifically so this mapping survives the corpus's deletion — see §6.2) makes this
mechanically checkable rather than assumed: every one of the 926 content files (all except
`INDEX.md`/`README.md`, which carry no frontmatter) shares `order_number: "325462-092US"` and
`date: "December 2024"`, with **zero variance across all 926**. Its `page_start`/`page_end` fields
are contiguous, non-overlapping, and monotone across the four "volumes" when read as one sequence:

| Volume | `page_start`..`page_end` | Files |
|---|---|---:|
| Vol 1: Basic Architecture | 29–614 | 26 |
| Vol 2 (2A–2D): Instruction Set Reference | 615–3201 | 810 |
| Vol 3 (3A–3D): System Programming Guide | 3202–4735 | 87 |
| Vol 4: Model-Specific Registers | 4736–5321 | 2 |
| Index | 5322–5363 | 1 |

That is one order number and one continuous ~5,363-page span, not four. The `pp=` numbers in every
existing citation are absolute offsets into **one combined document** — Order Number
325462-092US — not into four separately-paginated per-volume PDFs. Registering four volume slugs
(as an earlier draft of this design did) would require a `page_offset` per volume to translate
these numbers into each per-volume PDF's own pagination — an offset not derivable from the
vendored frontmatter, since the frontmatter's numbers were already relative to the combined
document to begin with. **This design instead registers a single slug, `intel-sdm`, for the one
combined 325462-092US PDF.** This matches what the data actually says, needs no offset arithmetic,
and avoids the alternative failure mode of registering four PDFs where two (Volumes 3 and 4) would
be presently uncited — a fiction the data does not support, since nothing here shows Intel ever
distributing them separately.

The `vol=` field survives in the locator grammar below (§2.3) as a **cross-checkable label**, not
a slug selector: each citation's declared `vol=N` must match the volume its `pp=` range falls into
per the table above, which is itself a real, mechanical consistency check the single-slug design
gets for free.

### 2.3 `pdf-locator`

A fixed-field, fixed-order, machine-**parseable** (even where not machine-**resolvable**) grammar:

```
locator  := "vol=" VOL ";" ( "sec=" SECNUM | "instr=" MNEMONIC ) ";part=" PART [ ";pp=" PSTART "-" PEND [ ";mp=" MANUALPAGES ] ]
VOL      := "1" | "2" | "3" | "4"
SECNUM   := DIGIT+ ( "." DIGIT+ )*                 ; e.g. "3.2", "22.1.3"
MNEMONIC := UPPER ( ALNUM | "_" )*                 ; e.g. "MOV", "CMOVcc", "Jcc"
PART     := IDENT                                  ; carries today's existing anchor through
                                                     ; unchanged, e.g. "operation", "description"
PSTART   := DIGIT+                                  ; absolute PDF page number into the single
                                                     ; combined 325462-092US manual (§2.2)
PEND     := DIGIT+                                  ; PSTART <= PEND <= the registered entry's
                                                     ; page_count (§1.2), when pp= is present
MANUALPAGES := IDENT                                ; the frontmatter's manual_pages label, verbatim,
                                                     ; with internal whitespace replaced by "_"
                                                     ; (e.g. "Vol.2B_4-28_to_Vol.2B_4-31")
```

**`pp=`/`mp=` are OPTIONAL, not mandatory as originally designed here (changed 2026-08-27,
adversarial review of the references/ migration).** The rest of this section (below) documents
the original design intent and is kept for its rationale, but the grammar box above is the
current, actually-enforced state. What changed: the registered `intel-sdm` entry (§7/`PLAN.md`)
could only be pinned to the live -078US (Dec 2022) edition — the -092US (Dec 2024) edition the
267 citations' `pp=`/`mp=` values were derived from is not fetchable anywhere. Two years of
revisions move page numbers by hundreds, so those `pp=`/`mp=` values are systematically wrong
against the bytes actually pinned, not merely unverified against them. Documenting that as a
caveat (an earlier version of this section, and of the `intel-sdm` entry's `review_note`, did
exactly that) still leaves a reader of the Lean source seeing a confident page number with no
signal it's wrong. The fix applied: `pp=`/`mp=` stripped from all 267 citations, keeping
`vol=`/`instr=`|`sec=`/`part=`, which still resolve by lookup in any edition. The `-092US` page
data itself is not discarded — it survives in `docs/intel_sdm_frontmatter.json`, self-labelled
per entry via its `order_number`/`date` fields (`"325462-092US"`/`"December 2024"`), for whoever
eventually sources the genuine `-092US` PDF or decides to re-derive `pp=` against `-078US`
instead.

**Why `part=` exists.** A census of the current 267 SDM citations found 159 targeting instruction
pages, split almost evenly between two distinct anchors: 81 cite `#operation` (the pseudocode a
semantics proof is actually grounded in), 78 cite `#description` (English prose) — and **23
instruction files are cited at both anchors from different declarations** (`ADD`, `AND`, `CALL`,
`CMOVcc`, `CMP`, `DIV`, `IMUL`, `JMP`, `Jcc`, `LEA`, `MOVZX`, and others). Without `part=`, both
anchors collapse to the identical locator string for the same instruction (same `vol`, same
`instr`, same `pp` range), silently merging 23 pairs of citations that mean different things —
losing exactly the granularity §2's opening claim says this grammar preserves. `part=` is free to
populate: it is today's existing anchor text, carried through the migration script unchanged
(§6.2), not re-derived.

**Why `mp=` exists.** `page_start`/`page_end` are absolute offsets into one specific edition
(325462-092US). A future SDM revision typically renumbers everything after the point it edits,
which is exactly the drift case §4 governs — but the frontmatter's `manual_pages` field (e.g.
`"Vol. 2B 4-28 to Vol. 2B 4-31"`, present and non-empty in all 926 indexed files) is Intel's own
*printed* page label, which survives far more revisions unchanged than an absolute offset does
(inserting a paragraph in chapter 3 shifts every later absolute page number, but leaves an
untouched chapter 4's own printed labels alone). `mp=` costs nothing to populate at migration time
— it is a direct, mechanical copy of the committed side-table's `manual_pages` field — and gives a
second, more drift-resistant coordinate alongside `pp=`. It is optional in the grammar because it
duplicates information `pp=` already carries for a citation created today; it earns its keep at
the next SDM revision, not at registration time.

Examples: `REF: intel-sdm#vol=1;sec=3.2;part=description;pp=67-90`,
`REF: intel-sdm#vol=2;instr=MOV;part=operation;pp=1317-1320;mp=Vol.2B_4-28_to_Vol.2B_4-31`.

**What is checkable:** `VOL` is cross-checked against the volume-page-range table in §2.2 (the
citation's declared `vol=N` must match the volume its `pp=` range actually falls into — a real
consistency check the single combined-document slug gets for free, stronger than the earlier
four-slug draft's "matches the slug's own declared volume" check, which could not have caught a
transposed-volume error the way a range lookup can); `SECNUM`/`MNEMONIC`/`PART` match their
grammar; `PSTART <= PEND`; and `PEND <= page_count` (§1.2 — **mandatory**, since `page_count` is a
required field for every `pdf-locator` entry, not the optional add-on an earlier draft of this
design left it as). This is real value: it catches transposed digits, swapped volumes, and
malformed locators — exactly the class of error a human introduces when hand-writing 267 of these,
and exactly the class of error that let this design's own earlier draft ship a worked example
mislocated by 614 pages (§2.2) undetected, because that check was optional and the wrong number
was still in range.

**What is NOT checkable, stated plainly:** nothing confirms that section 3.2 or the `MOV`
instruction actually appears on pages 67–90 or 1317–1320 of the real PDF, because no tool in this
design parses PDF text layout. This is the loss the owner's brief asked to be named rather than
discovered — a locator is well-formed-checkable, not content-resolvable. It is still strictly
more checkable than "no locator" (today's status quo for any citation this design would otherwise
have had to degrade to document-level), and it is checkable in exactly the way a URL+hash citation
into a PDF can be: syntax and internal consistency, not a truth oracle over the upstream's prose.

**Revision policy.** A `pdf-locator` entry's `edition` field (§1.2) is required and
machine-checked: the validator hard-fails on an empty `edition`, and any change to it — a bumped
order-number/revision suffix — is treated by the re-pin workflow (§4) as *ipso facto* substantive,
skipping straight to "every dependent citation must be re-read" rather than asking a human to
judge cosmetic-vs-substantive first. The recommended policy for an SDM revision is **re-pin in
place**: keep the single `intel-sdm` slug, update `edition`/`sha256`/`page_count` together, and
treat the re-pin as a full 267-citation re-read event, exactly as costly as it sounds. That cost is
the direct, honest price of the SDM having no stable per-section addressing scheme; this design
does not create that cost, it makes it visible, where today (Law 6's current text) it is invisible.

### 2.4 `json-pointer`

For structured-data upstreams (SPIR-V's `spirv.core.grammar.json`, and any future machine-readable
grammar/registry file): anchor is an RFC 6901 JSON Pointer, or — more ergonomically for this
corpus's shape — a documented key-path convention such as `instructions/OpSourceContinued` keyed
on `opname`. **Fully checkable**: the validator loads the cached JSON and confirms the pointer
resolves to a key.

### 2.5 `rfc-section`

For plain-text upstreams (the RFC-editor.org originals, if indexed directly rather than through
this project's own Markdown conversion — see §7): anchor is `sec=<N>` or `sec=<N.N>`, matched by
the validator against the cached raw text using the same numbered-heading-line regex
`rfc_text_to_markdown` already implements (`^(\d+)\.\s+([A-Z].*)$`, etc.) — reused for detection,
not conversion. **Checkable**, and notably *more* checkable than the PDF case: the cache holds
real, greppable plain text, so "does a line matching this section number exist" is a genuine
existence check, not merely a syntax check.

### 2.6 `c-symbol`

For C headers (`wasi-libc`'s `api.h`): anchor is `sym=<identifier>`, matched against the cached
header text via a declaration-shaped regex. **Checkable** (existence of the symbol name in the
cached text; not a semantic check that the declaration means what the citing Lean code assumes).

### 2.7 Summary table

| `anchor_mode` | Existence checkable? | What is NOT checked |
|---|---|---|
| `heading` | Yes, exact | — |
| `json-pointer` | Yes, exact | — |
| `rfc-section` | Yes (regex line match) | Whether the cited prose actually says what the citation claims |
| `c-symbol` | Yes (regex declaration match) | Semantic meaning of the declaration |
| `pdf-locator` | Well-formedness + internal consistency (incl. `part=` disambiguation, §2.3) | Whether the section/instruction genuinely appears at the stated page range |

---

## 3. Validator design

### 3.1 Two modes

- **`python scripts/check_references.py --offline`** — the default for local dev and ordinary CI.
  Validates every `REF: <slug>#<anchor>` citation in the tree against the **local cache** only.
  Zero network access. For every slug actually cited (not the whole cache — see §3.2), it
  **recomputes SHA-256 of the cached bytes and compares against `references.json`'s recorded
  `sha256`**, in addition to the anchor/locator checks below. A cited slug absent from the cache,
  a cached file whose recomputed hash disagrees with the index, an anchor that fails its mode's
  existence check, or a malformed locator is a **hard failure** (nonzero exit) — never a skip,
  never a warning-only print. This mirrors Law 13(4)'s "an oracle that cannot run must fail the
  run" applied to the new failure mode this design introduces (a cold, incomplete, or corrupted
  cache) — corrupted deliberately included: a cache that merely *exists* under the right filename
  is not evidence it holds what `references.json` claims (this is the same failure class `TCB.md`
  T8 documents as already demonstrated in this repository — manifest-membership is not disk-content
  verification, and a naive presence check "passes on a corpus truncated to one byte per file").
- **`python scripts/check_references.py --refresh [--slug <slug> | --corpus <corpus> | --all]`**
  — run deliberately, never as part of the default gate. Fetches each targeted entry's `url`,
  recomputes SHA-256, and compares against the recorded `sha256`. On match: updates the cache,
  leaves `references.json` untouched. On mismatch: **stops and reports** — see §4, it never
  auto-writes a new hash. On a fetch failure: **hard failure** — see §5.

The rationale for two modes, not one, is explicit in the brief and worth restating here because
it drives the CI design in §3.3: a network-dependent gate that fails on flaky wifi trains
reviewers and contributors to ignore red CI, which is worse than not having the gate. `--offline`
gives a fast, deterministic, network-free default; `--refresh` is the only place non-determinism
(the live internet) is allowed to enter, and it is opt-in.

### 3.2 Cache

- **Location**: `.cache/references/` at repository root, **gitignored** (added to `.gitignore`
  alongside the existing `.tmp_*`/`*.tmp` entries).
- **Layout**: one file per slug, `.cache/references/<slug>.<ext>` (extension derived from
  `media_type`: `.md`/`.html`/`.pdf`/`.json`/`.txt`/`.h`). **No sidecar metadata file.** An earlier
  draft of this design proposed a `<slug>.meta.json` sidecar recording the SHA-256 "actually
  observed" at fetch time, and had `--offline` compare that recorded number to `references.json`'s
  recorded number — a comparison of two recorded values, which proves nothing about what bytes are
  actually sitting on disk right now (a truncated, corrupted, or hand-substituted cache file would
  pass it cleanly, sidecar and index simply agreeing about a number neither one re-derives). §3.1's
  recompute-on-every-`--offline`-run makes the sidecar both unnecessary and actively worse than
  nothing — a second stale copy of a fact the cache file itself can always answer directly — so it
  is dropped, not merely left optional.
- **Population**: only `--refresh` writes into the cache. `--offline` only reads it (and hashes
  it — §3.1).

### 3.3 How CI seeds the cache

Ordinary PR CI runs `--offline` against a **restored** cache, never a freshly fetched one — this
is what keeps PR CI network-free and fast. Two seeding paths, not mutually exclusive:

1. **CI cache persistence** (e.g. GitHub Actions `actions/cache`, keyed on the hash of
   `references.json` itself): the cache is fetched once (by a scheduled job, or the first PR
   after a `references.json` change) and reused by every subsequent PR run until the index
   changes again.
2. **A deliberate, human-triggered `--refresh --all` run** (local, or a manually-dispatched CI
   job) whenever a new entry is registered or an existing one is re-pinned (§4) — this is the
   same "someone must intentionally run this" posture `scripts/regenerate_references.py
   --update-manifest` already has today for its own manifest-changed-since-last-run diff.

Either way, **`--offline` failing because the cache is cold is a correct, loud failure** — it
means CI's cache-seeding step did not run or did not complete, which is itself worth knowing, not
something to paper over with a silent fetch-on-demand fallback (that would reintroduce the
flaky-network dependency into the default gate this design exists to remove).

### 3.4 Exit-code semantics

| Condition | Mode | Result |
|---|---|---|
| All cited slugs present in cache, recomputed hash matches, all anchors resolve | `--offline` | exit 0 |
| A cited slug is absent from the cache | `--offline` | exit 1 (hard failure, not a skip) |
| A cited slug's cached file's recomputed SHA-256 disagrees with `references.json` | `--offline` | exit 1 — the cache and the index must agree, or the run does not silently trust either one (§3.1/§3.2) |
| An anchor fails its mode's existence/well-formedness check | either | exit 1 |
| `references.json` fails to parse, or an entry fails schema validation (§1) | either | exit 1, before any citation is even checked |
| SHA-256 matches upstream | `--refresh` | exit 0, cache updated |
| SHA-256 mismatch | `--refresh` | exit 1 — a FINDING, see §4. Cache is **not** silently updated to the new content; the drift is surfaced and the run fails so it cannot be missed. |
| URL fetch fails (timeout, 404, DNS) | `--refresh` | exit 1 — see §5 |

---

## 4. Drift policy

**A SHA-256 mismatch under `--refresh` is a FINDING requiring human review of whether the
upstream specification changed substantively — it is never auto-applied.** This mirrors Law 14's
prohibition on hand-editing calibration data, applied to the analogous hazard here: a validator
that quietly re-pins on drift is indistinguishable, in effect, from one that never checked at
all, because nothing then guarantees the citations that depend on the (silently changed) document
still say true things about it.

**What the validator prints on a mismatch — illustrative, not actual output** (this is a design
document; no such run has happened, and the specific numbers below are invented for exposition,
not measured):
```
[!] DRIFT DETECTED: intel-sdm
    recorded sha256:  a1b2c3...  (fetched_date: 2026-08-27, edition: 325462-092US)
    live sha256:       f9e8d7...  (fetched now)
    recorded size_bytes: 41,932,110
    live size:            41,933,884  (+1,774 bytes)
    url:                https://cdrdv2-public.intel.com/<...>/325462-sdm.pdf
    This entry is cited by 267 REF: annotations across 33 file(s). Re-pinning requires
    re-reading every one of them (see docs/REFERENCE_INDEX.md §4).
    Exit code 1. references.json NOT modified. Cache NOT updated.
```

**What the reviewer must do**, before a re-pin is recorded:
1. Fetch both the old and new content (the old one is still in `.cache/references/`; the new one
   was just fetched by `--refresh` into a scratch location, not yet promoted into the cache) and
   diff them — for a PDF this may mean a page-by-page visual diff or `pdftotext` comparison; for
   text-shaped media types a plain diff suffices.
2. Establish, in writing, whether the change is **substantive** (renumbered sections, changed
   opcodes/encodings, a genuine spec revision) or **cosmetic** (a reflowed PDF with identical
   content, a metadata-only re-serve, a URL that now redirects to an edition-bumped file with no
   semantic change) — **except when `edition` itself changed** (§2.3's revision policy): a bumped
   order-number/revision suffix is *ipso facto* substantive for `pdf-locator` entries, skipping
   this judgment call entirely, because a new SDM edition means repagination, full stop, and
   nothing here can tell whether any given `pp=`/`sec=` value still resolves correctly.
3. If substantive: **every citation whose locator depends on the changed document must be
   re-read**, not just re-hashed — a `pdf-locator`'s `pp=` range or `sec=` number may no longer be
   correct in the new edition, and nothing mechanical can tell whether it still is (§2.3's stated
   limit). This is the direct cost of a substantive SDM revision, and it is the same cost the
   project would face today if it noticed the vendored files were stale — this design does not
   make that cost appear, it makes it *visible*, where today it is invisible (Law 6's own current
   text admits `--verify` has "zero network dependency" and makes no live-upstream claim at all).
4. Only after that review does a re-pin get recorded: the reviewer runs `--refresh --slug
   <slug> --acknowledge-drift`, which promotes the newly-fetched content into the cache, updates
   `sha256`/`fetched_date` in `references.json`, and requires `--reviewer`/`--review-note`
   arguments that get written into the entry's `last_reviewed`/`reviewer`/`review_note` fields —
   there is no way to bump the hash without leaving a reviewed, attributed trail, mirroring the
   `<added-by>`/justification discipline `scripts/license_allowlist.txt` already enforces.
5. If the citing Lean files needed locator updates from step 3, those land in the same commit as
   the re-pin — a re-pin without a corresponding review of its dependent citations is incomplete,
   not merely undocumented.

---

## 5. Link-rot policy

**A dead URL under `--refresh` is a hard failure demanding a re-pin with documented content
review — never a silent skip.** Intel is known to reshuffle SDM download URLs across revisions;
a validator that treats "404" as "nothing to check, move on" would let the corpus silently stop
being verifiable while `--offline` kept passing forever against a stale cache.

**Does `archive_url` belong in the schema?** Yes, as an optional field (§1.2) — but as a
**recovery aid for the human doing the re-pin, not an automatic fallback the validator trusts**.
Concretely: on a dead `url`, `--refresh` reports the failure and, if `archive_url` is set, prints
it as a starting point for the reviewer to locate a replacement canonical URL or confirm the
content is unchanged — it does **not** silently fetch `archive_url` in place of `url` and treat
that as success. Reasons this stance is deliberate, not merely cautious:

- A Wayback (or similar) snapshot carries no cryptographic chain back to the publisher — it is
  one third party's claim about what another third party once served, and the SHA-256 this
  project actually trusts is only as good as a human confirming that claim, the same review §4
  already requires for ordinary drift.
- Archived snapshots can themselves be altered, excluded retroactively (origin-site removal
  requests), or simply be of a different edition than the one this project meant to pin.
- Treating an archive mirror as *equivalent* to the live canonical source would quietly weaken
  the provenance guarantee this whole design exists to make honest (Law 6's current text already
  names "does not validate against live upstream sources" as a named gap this design is supposed
  to close, not relocate onto a less-accountable proxy).

So: legitimate as a **pointer for recovery**, illegitimate as a **trust source**. If a URL is
permanently gone and the reviewer, using the archive (or any other means), locates and confirms a
correct replacement, that replacement becomes the new `url` through the same re-pin workflow as
§4 — `archive_url` never silently becomes the new canonical `url` either; a human promotes it
explicitly, if they choose to, as part of the reviewed re-pin.

---

## 6. Migration plan

### 6.1 Scope, precisely counted

A fresh repo-wide count of `REF:` citations into `references/**`, measured directly against this
document's own base commit (not copied from an earlier snapshot), finds **416** total, not only
the 267 SDM ones the initiating brief named — the owner's ruling correctly widened scope to all of
them, since `references/` is deleted wholesale:

| Corpus | Citations | Files citing | Migration class |
|---|---:|---:|---|
| `intel_sdm/` | 267 | 33 | Mechanical (§6.2) — **159 exact, 108 coarse-but-valid** |
| `wasm/` genuine (`syntax/binary/text/exec/valid/`) | 99 | — | Mechanical |
| `wasm/` hand-authored (`structure.md`, `text.md`) | 13 | 3 | **Blocked** — no URL, cannot be indexed (§10). `binary.md`/`execution.md` already fully re-pointed and carry **zero** citations — deletable today, not blocked (§6.4). |
| `windows/` genuine (CC-BY-4.0) | 23 | 3 | Mechanical |
| `windows/` hand-authored (`readfile.md`, `winsock2.md`) | 14 | 2 | **Blocked** — same class as wasm's, no assigned fix yet |
| `wasi/`, `zlib/`, `png/`, `spirv/`, `vulkan/` | 0 | 0 | No citations exist; **registration in `references.json` (metadata only) is mandatory before deletion where the corpus is worth keeping as ground truth — see §6.3. No corpus is exempt from deletion itself; the only choice per corpus is whether it is also registered.** |
| **Total** | **416** | | **389 mechanically migratable now; 27 blocked pending re-grounding** |

This corrects two things an earlier draft of this design got wrong, not merely updates stale
counts: the SDM split was **159/108, not 212/55** — 53 of the 267 SDM citations target
`vol_2_instruction_set_reference/ch_02_instruction_format.md`, a chapter file that matched no
branch of the originally-described migration script at all (§6.2 fixes this); and the blocked
total is **27, not 104** — the sibling Wasm re-pointing effort named in §6.4 has already landed (it
is an ancestor of this document's own base commit, not concurrent work), moving 90 of 93 original
Wasm citations off the four hand-authored files onto the real W3C spec chapters. wasm genuine
citations have grown further since (80 → 99) as unrelated TC20 work added new, properly-grounded
Wasm citations in the same window — evidence the corpus is healthy, not evidence of drift in this
count.

(Earlier per-corpus snapshots in `docs/THIRD_PARTY_LICENSES.md` and `TCB.md` T8 recorded still
different counts — reflecting ordinary code churn between audit dates, not a disagreement in
method. Whoever implements this migration should re-run the count at execution time rather than
treat any number in this document, including the one above, as frozen.)

### 6.2 Why the SDM rewrite is mechanical, not a week of manual reading

This is the effort estimate the owner's ruling specifically asked for. Every one of the 928
vendored `intel_sdm/` files carried machine-readable frontmatter, confirmed by full census, not a
sample — see §2.2's table and the discussion below. **That extraction has already happened**:
`docs/intel_sdm_frontmatter.json` is committed to the repository, keyed by repo-relative path,
covering all 926 content files (`INDEX.md`/`README.md` carry no frontmatter and need none). The
migration script consumes this file directly; it does not need to re-derive anything from the
doomed corpus, because the corpus is no longer the source of truth for this metadata — the
side-table is. A representative entry (`MOV.md`):

```yaml
title: "MOV—Move"
volume: "Volume 2 (2A, 2B, 2C, & 2D): Instruction Set Reference, A-Z"
page_start: 1317
page_end: 1320
manual_pages: "Vol. 2B 4-28 to Vol. 2B 4-31"
order_number: "325462-092US"
date: "December 2024"
```

The migration script's job, per citation, is entirely lookup-and-substitute:

1. Parse the existing `REF: references/intel_sdm/<path>#<anchor>` line.
2. Look up `<path>` in `docs/intel_sdm_frontmatter.json` (volume, page_start/page_end,
   manual_pages) — no file access to the doomed corpus required.
3. Recover the anchor's heading title from `check_refs.py`'s own section index (already computed
   today for anchor validation) to get the human-readable section/instruction name, and carry the
   anchor itself through verbatim into the new locator's `part=` field (§2.3) — `operation` and
   `description` are the two anchors actually in use today, and nothing about them needs
   reinterpreting, only relocating.
4. Branch on file shape — generalized to **`vol_*/ch_*.md`** for chapter files (not
   `vol_1_basic_architecture/ch_*.md` specifically, which was too narrow: it silently excluded the
   53 citations into `vol_2_instruction_set_reference/ch_02_instruction_format.md`, a chapter file
   under `vol_2`, not `vol_1`):
   - **Instruction pages** (`vol_*/instructions/*.md` and `vol_*/sgx_instructions/*.md` /
     `vol_*/vmx_instructions/*.md` where cited — 159 of 267 citations): the file's own
     `page_start`/`page_end` **is** that instruction's exact page range. Emit
     `instr=<MNEMONIC>;part=<anchor>;pp=<page_start>-<page_end>;mp=<manual_pages, §2.3>` — fully
     mechanical, and exact, not coarse. (Instruction files are **not** one-heading-per-file, unlike
     an earlier draft of this design assumed — 798 of 803 have more than one heading, a mean of
     roughly 8 — which is exactly why `part=` is required, not optional: without it, an
     instruction's `#operation` and `#description` citations collapse to the identical locator.)
   - **Chapter pages** (`vol_*/ch_*.md`, many headings per file — 108 of 267 citations: 55 in
     `vol_1_basic_architecture`, 53 in `vol_2_instruction_set_reference/ch_02_instruction_format.md`
     alone): the file's frontmatter only gives the *chapter's* page range, not the specific
     subsection's. Emit `sec=<number extracted from the heading text itself, e.g. "3.2">;
     part=<anchor>;pp=<chapter's page_start>-<page_end>;mp=<manual_pages>`. The **section number**
     is exact and mechanically recovered (it is literally in the heading text, e.g. `## 3.2
     OVERVIEW OF THE BASIC EXECUTION ENVIRONMENT`); only the **page range** is chapter-grain rather
     than subsection-grain. This is not a regression relative to today's status quo (one file, many
     headings, one frontmatter page range already resolves to chapter grain in practice) — but note
     that `ch_02_instruction_format.md` specifically spans 617–686 (70 pages, 51 headings), the
     coarsest file in the corpus; pinpointing exact subsection pages there by reading the real PDF
     is worthwhile optional follow-up polish, not a blocker to migration.
   - **Any other file shape** (none exist in the current 267 citations — 159 + 108 accounts for
     all of them) is a **hard failure for the migration script, not a silent fall-through to a
     default branch.** An earlier draft of this design had no such branch at all for the 53
     `ch_02_instruction_format.md` citations, which would have fallen through unrecognized; the
     fix generalizes the pattern match, but the deeper fix is refusing to guess if a fifth shape
     ever appears (an appendix, an `sgx_instructions`/`vmx_instructions` file gaining a citation
     later) rather than mis-migrating it under an assumption that happened to work for today's
     data.
5. Emit the single registered slug (`intel-sdm`, §2.2 — no volume-numbered slug variants, and no
   "registered but presently uncited" volumes, since one slug covers the whole combined document
   regardless of which volume any given citation's `vol=` field names) and rewrite the `REF:` line.

**Estimate: this is a day of scripting, not a week of manual reading.** 100% of the
volume/section-identity extraction is mechanical (the committed side-table + heading text already
say everything needed); the only optional manual step is subsection-precise page refinement for
the 108 chapter-grain citations (most valuably for the 53 in `ch_02_instruction_format.md`, the
coarsest bucket), which can be deferred as a follow-up without blocking the migration.

### 6.3 Windows and zero-citation corpora

- `windows/` genuine (23 citations, 3 files, CC-BY-4.0): same mechanical shape as SDM instruction
  pages — `exitprocess.md`, `getstdhandle.md`, and `writefile.md` each have a recorded `source_url`
  in their own frontmatter already (from `html_to_clean_markdown`'s header), so registration is
  direct, and re-anchoring reuses §2.1's conversion-then-slugify path unchanged. `pe_format.md` (0
  citations today, present in the corpus as ground truth) does **not** carry its own `source_url` —
  the only place that URL is recorded is `references/MANIFEST.provenance.json`
  (`https://raw.githubusercontent.com/MicrosoftDocs/win32/docs/desktop-src/Debug/pe-format.md`),
  which is itself scheduled for deletion alongside `references/` (§7). Registering `pe_format.md`
  must pull its URL from that manifest before the manifest is deleted, the same "extract before the
  source disappears" discipline as the SDM side-table (§6.2), just smaller in scope: one URL.
- `wasi/`, `zlib/`, `png/`, `spirv/` grammar JSON, `vulkan/`, `spirv/` prose: zero citations exist
  into any of them today, but **deletion of the vendored files is mandatory regardless — the owner's
  ruling (§0) leaves no corpus exempt, licensed-for-vendoring or not.** The only per-corpus choice
  is whether the document is *also* registered in `references.json` (metadata only: URL, hash,
  license — never the prose itself) before its vendored copy is deleted, not whether the copy stays.
  `wasi`/`zlib`/`png`/`spirv`-grammar should be registered — their content is genuinely useful
  ground truth even though nothing cites it yet, `references/MANIFEST.provenance.json` already
  records a URL (and, where resolvable, a commit-SHA pin) for every file in these four corpora
  today, so registration is a direct carry-forward, not new research. `vulkan/` and `spirv/` prose
  should likewise be registered if future SPIR-V/Vulkan work (per `docs/tasks/G5-*.md`) is expected
  soon — and here the corpus-level manifest is not enough on its own: per-chapter granularity (each
  of vulkan's 70 chapters, each of spirv's 4 prose chapters, carries its own URL fragment in its
  own frontmatter — e.g. `.../vkspec.html#spirvenv` — not recorded anywhere else) has already been
  extracted to `docs/references_corpus_metadata.json` ahead of deletion, mirroring the SDM
  side-table, so that choice remains available even after the vendored files are gone. If no
  near-term work depends on a corpus, omitting it from `references.json` for now and registering it
  later (from the same committed side-table) is also fine — what is not available is leaving the
  vendored copy in place as a third option.

### 6.4 The Wasm re-pointing has already landed

An earlier draft of this design described a *concurrent* sibling effort moving ~59–90 Wasm
citations off the four hand-authored files (`binary.md`, `execution.md`, `structure.md`,
`text.md`) onto the genuine W3C chapter files (`syntax/`, `binary/`, `text/`, `exec/`, `valid/`),
and proposed sequencing options for landing this migration's tooling before or after that work
completed. **That work is no longer concurrent — it has already merged** (commits `06c2e2f` /
`2fc3c3d`, both ancestors of this document's own base commit), so the sequencing question it
raised is moot; stating it as still-pending would be exactly the present-tense-about-unbuilt-work
error this project has been repeatedly burned by (§11).

What actually happened: 90 of 93 original Wasm `REF:` citations were re-pointed from the four
self-authored summary files onto the real, previously-uncited W3C spec chapters sitting one
directory over — moving the genuine-citation ratio from 3/93 to 80/93 (now 99, per §6.1, as
unrelated work has added further genuine citations since). `binary.md` and `execution.md` had zero
citations left afterward and **were already deleted**. `structure.md` and `text.md` were **not**
deleted — each still carries a handful of citations for declarations that are genuinely
project-internal (differential-fuzzing harness plumbing in `structure.md`; a non-spec-mandated
pretty-printing convention in `text.md`) with no W3C counterpart to cite, and were reduced to a
single honestly-labeled stub stating plainly that they are not vendored specification text, rather
than inventing a spec correspondence that does not exist. These are exactly the 13 remaining
blocked Wasm citations in §6.1's table, across `Gasm/Targets/Wasm/{HostOracle,SemanticsFuzzer,
Text}.lean`.

This migration's script runs over the 99 genuine Wasm citations exactly like any other
mechanically-migratable corpus (§6.3's `windows/` genuine citations are the closest analog — a
recorded `source_url`, direct registration, §2.1's conversion-then-slugify path unchanged). It does
**not** touch `structure.md`/`text.md`'s remaining 13 citations, for the same reason stated in §10:
a hand-authored file with no recorded source URL cannot become a `references.json` entry at all,
so "migrating" such a citation would mean silently pointing it at a slug for content that will not
exist once `references/` is deleted. Those 13 are correctly left as blocked pending §10's
disposition, not mechanically migrated under an assumption the data no longer supports.

### 6.5 Avoiding a flag day

`check_refs.py`'s `REF_REGEX` currently matches `path#anchor` shapes generically (it does not
require a `.md` extension or a `/`). During the migration window — and **only** during the
migration window; this is a temporary bridge to the end state stated in §0, not a permanent
dual-mode design — extend citation validation to recognize **both** shapes side by side:
- If the citation's target contains a `/` and a file extension recognizable under `docs/` (or, for
  the duration of the migration only, still present under `references/`), validate it the old way
  (on-disk file + heading).
- If the citation's target has no `/` and no file extension, treat it as `<slug>#<anchor>` and
  validate against `references.json` + cache.
- **A target that matches neither shape is a hard parse failure, not a silent fall-through to
  either branch.** An ambiguous or malformed target (a typo that happens to omit the expected `/`,
  a slug that collides with a directory name) must not be guessed at — it must be rejected the same
  way an unrecognized `media_type`/`license`/`anchor_mode` token already is (§1.2).

This lets corpora migrate one at a time — cheapest first (the corpora with zero citations to
rewrite), then Windows, then SDM, then Wasm's genuine citations — without any commit needing to
migrate all 416 citations atomically. Once every migratable corpus has moved and `references/` is
deleted (§0's end state), the old-style branch is deleted from `check_refs.py` (or the tool that
absorbs its function, see §9) in the same commit that removes the directory — at which point only
the `<slug>#<anchor>` shape is recognized, permanently.

### 6.6 The flatten, not a history scrub — a pre-flatten checklist replaces the scrub machinery

**Superseded.** An earlier draft of this section specified a *surgical* history rewrite —
`git filter-repo` or BFG, purging `references/intel_sdm/`, `references/vulkan/`, and the
non-redistributable `references/spirv/` paths from every historical commit while preserving the
rest of the repository's commit-by-commit history. **The owner has since ruled the repository will
instead be FLATTENED: git history is dropped entirely, not surgically rewritten** (`PLAN.md` D23,
which supersedes D22's surgical-rewrite decision). This makes the entire scrub apparatus this
section previously specified moot — there is no path-glob surgery to design, no tool choice
between `filter-repo` and BFG to make, and no question of purging specific corpora from historical
commits, because **no historical commits survive at all**. Only the final working tree, as a
single new initial commit, is published.

That is *cheaper* in exactly the way it sounds: `references/intel_sdm/` and every other corpus
this design deletes from the working tree (§0) simply ceases to exist once the flatten happens,
with no separate purge step required for any of it. But it is **more dangerous** in a way that is
easy to underweight: **every defect present in the tree at flatten time becomes permanent public
record**, and — the specific hazard this section now exists to manage — **anything recorded only
in a commit message is destroyed**. Commit messages stop being a durable record the moment the
flatten happens. `PLAN.md`, `docs/adr/`, and `docs/tasks/` are the sole surviving decision history
after that point; anything load-bearing that lives only in prose written into a `git commit -m`
body must be copied into one of those before the flatten, or it is gone as completely as if it had
never been written.

**What this design found living only in commit messages, concretely — not hypothetically.**
Auditing this document's own base-commit lineage for exactly this risk turned up two real
instances, neither yet recorded in any tracked file:

- Commit `c2f5bae` ("re-derive manifest hashes lost to an auto-merged hash file") documents a
  genuine hazard: *"a checksum manifest can merge cleanly and still be wrong"* — two branches each
  modified `references/MANIFEST.sha256` in ways that were individually correct and merged without
  conflict markers, producing a manifest that was textually clean and semantically wrong (recording
  hashes for files whose content the merge had changed). This is exactly the shape of finding Law
  13 requires to terminate in a mechanical prevention, and no such prevention exists yet — the
  lesson currently lives only in this one commit's message body.
- Commit `2fc3c3d` (the Wasm re-pointing merge, §6.4) records the precise before/after of that
  effort — 90 of 93 citations moved, the 3→80 (now 99) genuine-citation ratio, which two files were
  deleted outright and why the other two were kept as stubs. This document's §6.1/§6.4 now restate
  the load-bearing parts of that record directly, which is itself the mitigation for this specific
  instance — but it demonstrates the pattern was already live, not merely theoretical, before this
  audit went looking for it.

Neither example is fixed by this document alone (the manifest-merge hazard in particular wants a
mechanical gate, not a paragraph, per Law 13 — flagged separately, see the accompanying commit for
this change). The general practice this finding argues for is a **pre-flatten checklist**, not a
one-time audit: `docs/PRE_FLATTEN_CHECKLIST.md` (named in `PLAN.md` D23, not yet authored) should
include, at minimum:

1. **Commit-message-only content audit.** Walk commit messages since the last such audit for
   load-bearing findings, hazards, or numeric results not duplicated into `PLAN.md`/`docs/adr/`
   /`docs/tasks/`, and transcribe anything load-bearing into the tree before the flatten. The two
   instances above are worked examples of what this step looks for.
2. **Secrets.** No credential, API key, or token appears in any tracked file at flatten time (the
   flatten is not a filter step — a secret present in the final tree is published exactly as
   written).
3. **Machine-local paths.** No absolute path specific to a contributor's machine (a Windows user
   profile path, a local worktree location) survives in a tracked file where it would leak environment details
   pointlessly into public history's single remaining commit.
4. **Redistributability of every retained corpus.** Confirmed zero content files remain under
   `references/` (§0's end state) — this document's own migration (§6) is the mechanism that makes
   this checklist item true, not a separate manual pass.
5. **License/attribution completeness.** Every first-party file carries its required header
   (`scripts/check_licenses.py`, §4.1 item 5 of `docs/REVIEW.md`), and every `references.json`
   entry carries a real `license`/`distribution` token (§1.2) — nothing is shipped with an
   `unclear` distribution status unresolved.

**Sequencing**: this migration (§6.1–§6.5) still lands *before* the flatten, for the same reason
the old scrub-sequencing argument held even though the mechanism it argued for is gone — a flatten
against a tree that still references `references/**` paths would publish a final commit containing
exactly the content the owner ruled must not ship. The difference is that there is no longer a
second, separate history-rewrite step to sequence after the migration: once `references/` is
deleted from the working tree and the pre-flatten checklist above is clean, the flatten itself
*is* the terminal step, run once, with nothing after it.

---

## 7. What replaces what

Per the owner's ruling, this is now a clean, uniform answer with no hybrid carve-out to reason
about — itself a benefit of the uniform design, not merely a simplification of the writing here.

**Deleted entirely:**
- `references/` — the whole directory, all corpora, no exceptions. This includes the genuinely
  redistributable material (wasi, zlib, png, the CC-BY-4.0 windows files, the permissively
  licensed `spirv.core.grammar.json`) that an earlier draft of this design considered keeping
  vendored under a hybrid model. The owner's ruling rejects that: everything is indexed the same
  way, vendored or not.
- `references/MANIFEST.sha256` — superseded by `references.json`'s `sha256` field plus the
  gitignored cache's own recorded hashes.
- `references/MANIFEST.provenance.json` — superseded by `references.json`'s
  `license`/`distribution`/`edition`/`last_reviewed`/`reviewer`/`review_note` fields, which carry
  strictly more information per entry (today's provenance file records reproducibility at
  corpus grain; the new schema records it, plus license/review trail, at document grain). Its
  content must be carried forward, not merely dropped: it is currently the **only** recorded
  source for `pe_format.md`'s URL (§6.3) and for wasi/zlib/png/wasm's per-file URLs and
  commit-SHA pins. `docs/intel_sdm_frontmatter.json` and `docs/references_corpus_metadata.json`
  (both committed ahead of this deletion, extracted from the vendored files' own frontmatter
  where the manifest didn't already cover it — §2.2, §6.3) exist for exactly this reason: nothing
  this manifest or the vendored corpora themselves record is allowed to be lost purely because the
  file that recorded it was deleted before `references.json` registration caught up to it.
- Most of `scripts/regenerate_references.py`: the `CORPUS_PROVENANCE` dict, `MANIFEST` dict, and
  every per-corpus `regenerate_*()` fetch/write function (`regenerate_windows`, `regenerate_spirv`,
  `regenerate_vulkan`, `regenerate_wasm`, `regenerate_wasi`, `regenerate_intel_sdm`,
  `regenerate_zlib`, `regenerate_png`) are deleted — there is nothing left for them to regenerate
  once nothing is vendored. `write_manifest()` and `verify_references()` are deleted; their
  responsibilities move to `scripts/check_references.py`'s `--refresh`/`--offline` respectively.

**Survives, and where it moves** (into `scripts/check_references.py`, the new validator) —
**note (2026-08-27): as actually built, `check_references.py` did not literally port these
functions; it re-implements the same jobs more minimally** (`fetch_bytes` is a plain
`urllib.request` read with no strict-UTF-8 decode step of its own — hashing operates on raw
bytes and only `derive_headings`'s later `.read_text(..., errors="replace")` decodes; heading
extraction is `strip_html_tags_for_headings`, a single regex pass over `<h1>`–`<h6>` tags, not
the fuller `html_to_clean_markdown`/`sphinx_html_to_markdown`/`convert_html_tables` pipeline).
This was verified sufficient for the wasm migration (`PLAN.md`): 99/99 citations' anchors
resolved correctly against real fetched HTML using exactly this simpler path. The paragraph
below describes this section's original design intent, kept for its rationale, not as a
description of what shipped:
- `decode_reference_bytes` (strict-UTF-8, no silent `U+FFFD` substitution) — reused verbatim for
  every `--refresh` fetch.
- `html_to_clean_markdown`, `sphinx_html_to_markdown`, `convert_html_tables` — reused for
  in-memory anchor derivation on `html`-media-type entries (§2.1); the *output* of this
  conversion is no longer written to a committed file, only held in the cache/memory long enough
  to compute headings.
- `rfc_text_to_markdown`'s section-detection regex — reused (detection only, not full conversion)
  for `rfc-section` anchor checking (§2.5).
- `github_commit_sha` / `resolve_pinned_url` — reused as-is: `references.json`'s `edition` field
  plays the same role the old provenance file's commit-SHA pin did, and re-fetching at a pinned
  commit during `--refresh` is exactly the same mechanism.
- `sha256_file` (renamed `sha256_bytes` — hashing fetched bytes directly rather than an on-disk
  file, since there is no on-disk vendored copy to hash anymore).

**New:** `references.json` at repository root; `scripts/check_references.py`
(`--offline`/`--refresh`); `.cache/references/` (gitignored).

**Interaction with `scripts/check_licenses.py`:** that tool's `references/**` exclusion
(`count_excluded_references()`, §4.1 item 5 of `docs/REVIEW.md`) becomes vacuous once
`references/` no longer exists — it will simply report 0 excluded files forever, which is correct
and requires no code change (the exclusion clause can be deleted as later cleanup, but leaving it
harmlessly inert is not incorrect).

---

## 8. Proposed Law 4 and Law 6 amendment text

**Marked PROPOSED. The owner ratifies laws; this document only drafts text for that ratification,
and does not itself edit `docs/REVIEW.md`.**

### 8.1 Law 4 (PROPOSED amendment)

Current text binds "vendored directly into the repository" as the *only* way to satisfy citing
genuine ground truth. This design deliberately stops vendoring **any** third-party documentation
prose — not only the non-redistributable corpora, per the owner's ruling (§0) — so the law's
letter must change; its intent — never cite a self-authored approximation standing in for someone
else's spec — must not.

**A SHOULD-vendor clause was deliberately removed from this amendment.** A draft of this section
previously read: *"Where the upstream's license permits redistribution, the authoritative text
SHOULD be vendored into the repository as before."* That directly contradicts §0's uniform-deletion
end state — registering it as ratified law text would leave the law book itself licensing a future
re-vendoring of wasi/zlib/png/the CC-BY windows files "as the law prefers," on the same day the
tree that housed them is emptied. Registration in `references.json` is the **sole** mechanism for
satisfying this law, for every corpus, regardless of what its license would have permitted; nothing
below leaves that door open.

> ### Law 4: External Reference Ingestion Law (No Self-Authored Standards) — PROPOSED AMENDMENT
> **Every formal model MUST cite genuine, authoritative upstream ground truth — never a
> self-authored approximation. The authoritative source MUST be registered in `references.json` by
> stable slug, canonical URL, and content hash (`docs/REFERENCE_INDEX.md`), and cited by slug —
> this is the sole mechanism, regardless of what the upstream's license would otherwise permit; no
> third-party documentation prose is vendored into the repository, for any corpus, under any
> circumstance. A hand-authored summary presented as if it were indexed specification text is
> strictly prohibited: every citation must resolve, via the index, to text the issuing authority
> actually published. A document with no recorded, verifiable source URL cannot be registered and
> cannot be cited as ground truth at all — it must be sourced properly or removed.**
>
> - We do NOT author or synthesize ad-hoc approximations of hardware manuals or external OS
>   specifications; that remains an absolute prohibition, unchanged by this amendment.
> - Indexing by slug, URL, and hash is the only acceptable mechanism; what is never acceptable —
>   under any future license, redistribution right, or convenience argument — is either a citation
>   whose target is this project's own prose about someone else's specification, or a copy of the
>   upstream's own prose committed into this repository.

### 8.2 Law 6 (PROPOSED amendment)

Current text binds reproducibility of `references/` specifically, via
`scripts/regenerate_references.py --verify`, and is explicit about what that tool does and does
not prove — it proves local-snapshot integrity; it does **not** validate against live upstream
sources, and says so plainly ("a named, explicitly unmet obligation, not a silently-assumed one").

**An earlier draft of this amendment retired that caveat outright, on the grounds that `--refresh`
closes the gap. It does not, and the caveat is kept.** `--refresh` is opt-in with **no mandated
cadence** (design-review question 3, below, is still open on exactly this point) — an opt-in check
nobody is obliged to run does not close the live-upstream gap, it relocates it from "no mechanism
exists" to "a mechanism exists with no trigger." The default gate, `--offline`, makes zero
live-upstream claim regardless of what `--refresh` can do when someone chooses to run it. Retiring
the caveat here would make this law *less* honest than its current text, on the very document meant
to close a gap in the *previous* honesty failure — exactly the regression Law 13 exists to prevent,
and exactly the kind of present-indicative claim about a live-upstream guarantee this repository
does not actually make that has caused trouble in this project before (§11). The caveat is
therefore **kept**, and the live-upstream claim is stated as conditional on `--refresh` actually
running, not as an ambient property of the system.

> ### Law 6: Reference Reproducibility & Verifiable Provenance Mandate — PROPOSED AMENDMENT
> **Every external document cited anywhere in the repository — registered in `references.json`,
> never vendored (§8.1) — MUST carry machine-checkable provenance: a recorded canonical URL, a
> SHA-256 of its exact fetched content, a fetch date, and a declared license/distribution status.
> `scripts/check_references.py --offline` (the default for development and CI) validates every
> `REF:` citation against a local cache and hard-fails on any cited slug the cache does not hold,
> any cached file whose recomputed hash disagrees with the index, or any anchor that is not
> well-formed/resolvable per its media type's grammar (`docs/REFERENCE_INDEX.md` §2). `--refresh`
> (run deliberately, not on every CI invocation) re-fetches, re-verifies, and reports drift; a
> SHA-256 mismatch is never auto-applied — it is a FINDING requiring human review per the workflow
> in `docs/REFERENCE_INDEX.md` §4, mirroring Law 14's prohibition on hand-editing calibration
> data. A dead URL is a hard failure demanding a documented re-pin, never a silent skip (§5).
> Ad-hoc, unindexed, or hand-authored files masquerading as reference material remain strictly
> prohibited; a document with no recorded URL cannot be registered at all.**
>
> - **What this law does NOT prove by default**: `--offline` (the default gate) validates that the
>   local cache and `references.json` mutually agree — it makes **no live-upstream claim**.
>   Live-upstream agreement is established only when `--refresh` is actually run, and this law does
>   not currently mandate a cadence for that (see `docs/REFERENCE_INDEX.md`, design-review question
>   3). Until a mandated cadence exists, treat live-upstream agreement as **checked only as of the
>   last human-triggered `--refresh`**, not as a standing guarantee.
> - **Status (updated 2026-08-27): LANDED.** `scripts/check_references.py`, `references.json`, and
>   `references/`'s deletion (§6/§7) are built, not just designed — the vendored tree, its
>   manifests, and `scripts/regenerate_references.py` are gone; `docs/REVIEW.md` Law 6 is rewritten
>   to this contract shape. `--offline`'s live-upstream caveat above still applies in full: no CI
>   step yet runs `--refresh` (`docs/CI.md` #7's named, still-open gap), so `--offline` currently
>   fails on a cold cache in a fresh checkout. That is an operational gap in *keeping the gate green
>   automatically*, not evidence the mechanism itself is undesigned — every entry in `references.json`
>   today was independently fetched and hash-verified at registration time (see each entry's
>   `review_note`).

### 8.3 Two more ratified obligations this deletion silently invalidates

Laws 4 and 6 are the two obligations this design set out to amend, but deleting `references/`
falsifies two more ratified statements that neither amendment above touches. Both need the same
PROPOSED-amendment treatment when this document is ratified, and are named here so they are not
missed a second time:

- **`docs/REVIEW.md` §4.1 Pillar 1, item 3 — fixed 2026-08-27.** Re-pointed at
  `python scripts/check_references.py --offline` (plus `python scripts/check_publishable.py`,
  the companion gate this design also specifies), no longer naming the deleted
  `verify_references()`.
- **Law 3, item 1** (`scripts/check_refs.py`'s own docstring, and `docs/REVIEW.md`'s Law 3 prose):
  still describes indexing `docs/` and `references/` — harmless rather than false now, since
  `collect_markdown_sections()` (§9 below) already guards each `DOC_DIRS` entry with
  `if not doc_dir.exists(): continue`, so a deleted `references/` yields 0 sections from that
  root rather than an error. Worth tightening to say "docs/, and `references.json`'s registered
  slugs" per §9's redefinition, but not load-bearing the way item 3 was — left as tracked
  follow-up, not fixed in this pass.

---

## 9. How `check_refs.py`'s three jobs survive

`check_refs.py` (or its successor — the natural home is to extend it in place, since its Lean-side
scanning logic is unaffected) has three responsibilities per Law 3. Each survives, with one
redefinition:

1. **Broken-citation detection.** Unchanged in spirit: extend `REF_REGEX`'s validation branch so
   a citation target is checked against `references.json` + cache when it has no `/`-and-extension
   shape (§6.5), and against `docs/`'s on-disk headings otherwise (docs/ is unaffected by this
   design — it isn't third-party material and keeps vendoring itself, being first-party).
2. **Un-cited-declaration detection.** Entirely unaffected — this check is orthogonal to what a
   citation's *target* looks like; it only asks whether a Lean declaration has *any* `REF:` above
   it at all.
3. **The Law 3 unreferenced-backlog report.** This is where "unreferenced" needs an honest
   redefinition once the index is the unit, because a `pdf-locator` entry has no enumerable
   heading set the way a Markdown file does. Two backlog shapes now coexist, reported separately
   rather than conflated:
   - **Section-level backlog** (unchanged): for entries whose `anchor_mode` supports full
     existence-checking (`heading`, `json-pointer`, `rfc-section` where headings/keys/sections can
     be enumerated from the cache), report unreferenced headings/keys/sections exactly as today.
   - **Document-level backlog** (new, coarser, and named as such): for `pdf-locator` entries,
     report which *registered slugs* have zero citations at all — a real, useful signal ("this
     document is registered but nothing cites it yet"), but explicitly a different granularity
     than the section-level report, never silently merged into the same count. The report prints
     both lists under separate headings so a reader cannot mistake "0 unreferenced sections in
     `intel-sdm`" for "every fact in the manual has a citation" — it can only ever mean "every
     *registered locator instance* line in the index for this slug is either cited or the slug
     itself has no enumerable sub-index," which for a PDF is closer to "this document is at least
     used somewhere" than a genuine section-coverage claim.

**A pre-existing bug in the coverage metric, fixed in the same change as this document.**
`check_refs.py`'s summary line (`SUMMARY: {total_ref}/{docs_sections} … coverage`) computed its
numerator over **all** referenced sections — both `docs/` and `references/` — while dividing by a
denominator scoped to `docs/` only. That inflated the printed coverage figure, and was going to
look like a **coverage regression** the moment `references/` citations stop being enumerable local
sections at all (§0), even though nothing about actual `docs/` coverage would have changed. Fixed
(`scripts/check_refs.py`, same commit as this document): the numerator is now scoped to `docs/`
only, matching the denominator it is already divided by. Measured directly, not estimated:
**179 → 96** (17.5% → 9.4% coverage), both under `docs_sections = 1022`, both exit code 0. The drop
is the fix taking effect immediately — it is not caused by, and does not wait for, the
`references/` migration itself; anyone seeing 96 (or a nearby number) after this change should not
read it as new backlog appearing, only as the metric finally measuring what its own denominator
already claimed to measure.

---

## 10. The four remaining hand-authored files cannot be indexed, by design

An earlier draft of this design named six hand-authored files as this section's subject. Two of
them — `references/wasm/binary.md` and `references/wasm/execution.md` — have already been fully
re-pointed by the (now-landed, §6.4) Wasm re-pointing effort and carry **zero** citations today;
they are deletable immediately, with no disposition decision needed, and are no longer part of
this section's subject. What remains is **four** files, carrying the **27** blocked citations
counted in §6.1: `references/windows/{readfile.md, winsock2.md}` (14 citations, 2 files) and
`references/wasm/{structure.md, text.md}` (13 citations, 2 files).

All four have **no source URL recorded anywhere** — confirmed on disk (each opens with *"Not
fetched by this script... NOT the official [spec]... no source URL is recorded anywhere"*) and in
`references/MANIFEST.provenance.json` today. `references.json`'s `url` field is required (§1.2);
there is no way to register a document that does not have one.

**This is the intended enforcement, not a gap to patch around.** The index correctly refuses to
provide *any* path — indexed or otherwise — for a document nobody can point at an upstream (and,
per §0's broadened ruling, "vendored" is no longer available as an alternative path for *any*
document regardless of license, so this was never a live option for these four either). This
forces the disposition `TCB.md` T8 already calls for as unresolved Law-4 backlog, for each of the
four independently: either (a) the citations get re-grounded in real indexed material — as already
happened for `binary.md`/`execution.md`, and as remains open for the other four — or (b) the
prose, where the owner wants to keep it as legitimate project-authored design commentary, moves to
`docs/` as an ordinary design document, cited honestly as "our own analysis," never presented as
if it were indexed specification text.

**Recommendation, not left as an open question this time**: for the remaining 27 citations across
4 files, prefer **(b)** as the near-term unblocker, not a deliberately-failing placeholder gate and
not blocking `references/`'s deletion on all four being re-grounded in genuine upstream material
first. `structure.md`'s and `text.md`'s remaining citations are already, by their own stub text,
project-internal (differential-fuzzing harness plumbing; a non-spec pretty-printing convention)
with no W3C counterpart to cite honestly under (a) — moving them to `docs/` is not a downgrade, it
is the accurate disposition. The Windows pair is genuinely open Law-4 backlog (real Win32 API
ground truth research, not yet assigned to anyone) and should stay tracked as such under `TCB.md`
T8 rather than be forced into (b) by default — but neither pair should block deleting
`references/` and shipping the rest of this migration; open-sourcing does not need to wait on
unassigned Win32 research (design-review question 5, below, restates this as an explicit ask).
Either path is a correct use of Law 4; remaining in `references/` pretending to be ground truth is
not, and after this migration there is no third option — the schema does not accommodate one.

---

## Design-review questions

Questions 1 and 6 from an earlier draft of this document are now resolved rather than open — the
owner's rulings settled both directly — and are recorded below as decisions with their rationale,
not left in question form a second time. Questions 2–5 remain genuinely open.

1. ~~SDM slug granularity~~ — **resolved: one slug (`intel-sdm`), not four.** An earlier draft
   asked whether the owner wanted four volume-numbered slugs or finer per-sub-volume ones. Neither
   is correct: the vendored frontmatter's `page_start`/`page_end` are absolute offsets into a
   single combined 325462-092US document (§2.2), so a four-slug scheme would have required a
   `page_offset` per volume that the data does not supply, and a worked example built on that
   assumption was itself wrong by roughly 614 pages before this fix. §2.2/§2.3 register one slug;
   `vol=` survives as a cross-checked label, not a slug selector.
2. **Is the `pp=` field in `pdf-locator` required to be subsection-precise, ever?** §6.2 accepts
   chapter-grain page ranges for the corrected **108** non-instruction SDM citations (55 in
   `vol_1_basic_architecture`, 53 in `vol_2_instruction_set_reference/ch_02_instruction_format.md`
   — not "55" as an earlier draft had it, see §6.1) as good enough long-term for the 55, but the 53
   sit inside a single 70-page, 51-heading chapter file — coarse enough that "good enough
   long-term" is a weaker claim there. Confirm chapter-grain is acceptable for the vol-1 citations,
   and separately decide whether the vol-2 `ch_02` citations warrant a follow-up task to walk the
   real PDF and tighten them specifically (the `mp=` field, §2.3, mitigates this somewhat at zero
   extra cost regardless of the answer).
3. **`--refresh` cadence.** Should it run on a schedule (e.g. weekly CI job, opening a tracked
   drift-review item automatically on mismatch) or purely on-demand by a human who suspects drift?
   This is no longer purely a link-rot question (§5) — §8.2's Law 6 amendment keeps a caveat that
   `--offline` makes no live-upstream claim specifically *because* this question is still open; an
   answer here (especially a mandated cadence) would let a future revision of that amendment
   tighten the caveat rather than merely preserve it.
4. **Archive-mirror promotion.** §5 proposes `archive_url` as a recovery aid a human may act on,
   never an automatic substitute. Confirm that stance, or specify a controlled policy (e.g.
   "after N days of confirmed dead URL plus documented content review, `archive_url` may be
   promoted to `url`") if the owner wants a narrower automatic path.
5. **Windows hand-authored citations (§10, 14 citations, 2 files — `readfile.md`/`winsock2.md`).**
   The Wasm hand-authored group has already been substantially resolved (§6.4 — 90 of 93 citations
   re-pointed, 2 of 4 files deleted outright, the remaining 2 reduced to honest stubs); the Windows
   pair has no assigned effort yet. Should this migration spin out a dedicated follow-up task for
   it now (mirroring the Wasm re-pointing), or leave it as unscheduled backlog alongside the rest of
   `TCB.md` T8? Either answer is compatible with §10's recommendation that this pair not block
   `references/`'s deletion or open-sourcing.
6. ~~History-scrub tooling and timing~~ — **resolved: no scrub; the repository is flattened
   instead (`PLAN.md` D23), and history is dropped entirely rather than surgically rewritten.**
   §6.6 restates the design's sequencing around a pre-flatten checklist (`docs/
   PRE_FLATTEN_CHECKLIST.md`) in place of the tool-choice/timing question this document previously
   posed. The one part of the old question that still has real content — must the working tree be
   fully clean of `references/` *before* the flatten, or can that trail briefly under time
   pressure — is answered by §6.6 as: it must be clean first; the flatten publishes only the tree
   at flatten time, so anything not yet deleted is no longer trailing, it is permanent.

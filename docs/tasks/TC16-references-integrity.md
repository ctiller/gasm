---
id: TC16
title: References pipeline integrity (SHA-256 manifest, honest verify)
status: done
blocked_on: ""
after: []
related: [G5]
bar: ""
track: trust-core
priority: 8.3
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# TC16: References pipeline integrity (SHA-256 manifest, honest verify)

## Context

Sourced from `TCB.md` **T8 — References pipeline — Law 4's ground truth passes through regex**,
tied for TCB's #2 rank. Law 4 requires authoritative external references (Intel/AMD ISA manuals,
Win32 API contracts, etc.) be vendored as genuine ground truth, and `docs/REVIEW.md` §4.1 item 3
already declares `python scripts/regenerate_references.py --verify` a Pillar-1 mechanical gate.
TCB's finding is that this declared gate is currently a facade: `verify_references()` "checks
directory-exists + file_count≠0 — **passes on a corpus truncated to one byte per file**." There is
no hashing, no manifest, no recorded fetch date. Worse, the regex-based markdown conversion
"strips all tags (**silently flattening every table** — how SDM opcode tables arrive)" — the exact
data shape most load-bearing for instruction semantics — plus a five-entity HTML-decode chain, an
`errors="replace"` policy that substitutes U+FFFD instead of failing on bad encoding, and a
`<main>`-tag extractor that silently falls back to the whole document when the tag is absent.

The severity gradient TCB flags: six of eight vendored corpora track moving upstream references
(so "reproducible" is aspirational without pinning), and **`intel_sdm` alone is 89% of the corpus
by file count, has no recorded URL, and is unreproducible as vendored today** — this is the single
largest specification input in the entire repository and it currently has the weakest integrity
story. The missing-corpus failure path is "a print, not a raise" — an absent reference corpus is
reported, not enforced.

This is mechanical work (a hashing/manifest layer around an existing pipeline, not a new model or
contract), hence empty `design` until an inline `## Design` section covers it.

## Deliverables & acceptance criteria

- A per-file SHA-256 manifest for every vendored reference corpus, checked into the repo alongside
  (or referenced by) `scripts/regenerate_references.py`.
- `--verify` changed to fail with a **non-zero exit** on any hash mismatch, any file below a
  reasonable size floor (closing the "one byte per file passes" hole), and any corpus directory
  that is missing entirely (replacing the current print-only path with a hard failure).
- Commit-SHA (or equivalent) pinning recorded for every corpus whose upstream is a moving
  reference, so "regenerate" is reproducible against a stated point in time rather than
  whatever the source currently serves.
- A **converter fixture suite**: known-input-to-known-output test cases for the HTML→markdown
  conversion step, covering at minimum the exact failure classes TCB names — a table (must survive
  structurally, not flatten), an entity-encoded character (must decode correctly through all five
  stages), a deliberately malformed-encoding byte sequence (must fail loudly, not silently become
  U+FFFD), and a document with no `<main>` tag (must fail or explicitly flag fallback, not
  silently extract the whole document as if that were equivalent).
- An explicit, honest resolution for `intel_sdm` specifically: either a genuine reproducible
  ingestion path (a recorded source URL + pin), or — if that's not achievable this cycle — a
  documented declaration that it is a vendored blob without a reproducible ingestion path, so the
  gap is stated rather than silently passed by a weak verify check. Do not let this task close
  with `intel_sdm` still silently claiming a reproducibility it doesn't have.
- Completion report: manifest coverage (corpora × files hashed), the fixture suite's pass/fail
  results including the negative cases (malformed encoding, missing `<main>`) demonstrated to fail
  correctly, and the `intel_sdm` resolution chosen.

## Pointers

- `scripts/regenerate_references.py` — `verify_references()` (the facade this task hardens) and
  the HTML→markdown conversion path (table-stripping regex, entity-decode chain, `errors="replace"`,
  `<main>` extractor — grep for each to locate current line numbers).
- `references/` — the eight vendored corpora; `references/intel_sdm/` specifically, given its 89%
  share of the corpus and its recorded lack of a source URL.
- `TCB.md` §T8 in full.
- `docs/REVIEW.md` Law 4 (external reference ingestion), Law 6 (reference reproducibility mandate
  — this task is the direct mechanical fix for Law 6's current non-compliance), §4.1 item 3 (the
  Pillar-1 gate this task makes honest).

## Notes

- 2026-08-27: priority 8.3 — TCB ranked-top-8 #3 (T8 — the references-verify gate is a facade that only counts files; 89% of the corpus, intel_sdm, is unreproducible).
- 2026-08-27: related: [G5] — TC16's references-integrity fix (TCB T8) is the general case of the exact gap G5 will hit concretely: `spirv.core.grammar.json` is named in the ingestion manifest and cited as ingested, but does not exist on disk (references/spirv/ holds only four prose chapters). A fresh agent starting G5 should read TC16 first.
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): status corrected `implementing` → `done`. `scripts/check_references.py` (the file this task's pointers name as `regenerate_references.py`, since renamed) contains 21 occurrences of `sha256` and an explicit `intel_sdm` disposition comment; matches this task's manifest/honest-declaration acceptance criteria. Frontmatter had not been updated; corrected on inspection.

_(none yet — first entries append here as work begins; mechanical task, consolidate into an
inline `## Design` section before implementation, `design_review: waived-mechanical` unless the
`intel_sdm` resolution turns out to need a real design decision, in which case escalate that one
sub-question to a design doc rather than waiving review on it.)_

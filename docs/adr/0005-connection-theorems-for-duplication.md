# 0005. Connection Theorems for Duplication

## Status

Accepted, 2026-08-27. (PLAN.md D4.)

## Context

The deep review's findings ledger catalogued live unlinked duplication of model-level
facts: RFC1951 length/distance logic encoded three separate ways (tables in
`Deflate.lean`, a closed-form `encodeLength`/`encodeDistance`, and asm branch trees in
`Zlib/Windows.lean`), `compress` vs. `compressFixed`, gzip magic bytes duplicated across
three files, duplicated xorshift RNGs, and a 19-way `clenOrder` branch chain shadowing a
table. None of these pairs carry any proof that the copies agree — each is a silent
liability: a fix to one copy silently desyncs the others.

## Decision

Adopt [Law 12](../REVIEW.md#law-12-connection-theorem-mandate-no-unlinked-twins) in full:
two encodings of the same model-level fact may coexist only when linked by a
kernel-checked connection theorem proving their equivalence over the shared domain,
preferring a single source of truth wherever re-encoding isn't genuinely required.
Additionally — beyond the mechanical linter — a review-protocol audit layer sits on top:
Pillar 3's Factoring & DRY axis explicitly hunts for semantic duplication a literal-match
linter cannot see, with embedding-similarity triage over declaration bodies as an
anticipated deterministic-prioritization extension to that audit.

## Consequences

The known twins in the findings ledger become a tracked backlog (Phase 5 / TASKS.md
TC12): each needs either a connection theorem or collapsing onto one source of truth. The
twin-detection linter (`scripts/`, sibling of `check_refs.py`) becomes required tooling,
wired to whatever gate runner ([`0009`](0009-findings-become-gates.md)) executes CI-shaped
checks. This ADR directory is itself governed by the same law applied to documentation —
see [`docs/adr/README.md`](README.md).

## Provenance

Mixed. The goal is owner-stated, from the founding vision message: "then figure out how
to broadly detect unintended duplication growing (at least at the model level)." The
specific mechanism — Law 12, kernel-checked connection theorems, and the review-protocol
audit layer with embedding-similarity triage — is the coordinator's design for satisfying
that goal, not owner-specified.

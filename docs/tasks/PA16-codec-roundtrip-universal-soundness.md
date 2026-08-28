---
id: PA16
title: Zlib/PNG/Gzip codec universal roundtrip soundness — design + structural proof
status: ready
blocked_on: ""
after: []
related: [PA10, F6, PA1]
bar: ""
track: proof-arch
priority: 8.5
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA16: Zlib/PNG/Gzip codec universal roundtrip soundness — design + structural proof

## Context

Sourced from `docs/ORACLE_DEBT.md`'s coverage-matrix audit of `scripts/gate_allowlist.txt`'s 37
`grandfathered` entries. Twelve of them share one shape — a full-codec compress-then-decompress (or
decompress-then-recompress-then-decompress) claim, checked by `native_decide` on exactly one or two
concrete `ByteArray`/`String` literals — and **no existing task covers any of them**:

- `Stdlib/Zlib/Equivalence.lean`: `deflate_roundtrip_empty_inst`, `deflate_roundtrip_soundness_inst`,
  `deflate_roundtrip_repetitive_inst`, `zlib_roundtrip_soundness_inst`, `gzip_roundtrip_soundness_inst`,
  `deflate_idempotent_canonical_roundtrip_inst`, `zlib_idempotent_canonical_roundtrip_inst`,
  `gzip_idempotent_canonical_roundtrip_inst` (8 entries).
- `Stdlib/Png/Equivalence.lean`: `png_roundtrip_soundness_inst`, `png_idempotent_canonical_roundtrip_inst`
  (2 entries — the whole-image roundtrip, distinct from the five per-filter-step entries PA10 covers).
- `Spikes/Spike5Gzip/Equivalence.lean`: `gzip_roundtrip_soundness_inst`,
  `gzip_idempotent_canonical_roundtrip_inst` (2 entries — near-duplicates of the Stdlib pair, scoped
  to the spike's own `canonicalSampleData`; `docs/tasks/TC12-connection-theorem-linter.md` should be
  told about this duplication if not already in its known-twins list).

`docs/tasks/PA8-law9-migration.md`'s Spike5 fix targets the `GzipOp`/`GunzipOp` single-constructor
*environment* domain-shrinking (the `VerifiedProgram`/`traceEquivalence` half of Spike5's verification)
and does **not** touch these two direct functional roundtrip checks, which take no environment
argument at all. `docs/tasks/F6-zlib-to-infinity.md` requires every *optimized variant* to match the
existing spec under a universal contract, but does not itself commit to proving the existing baseline
`decompress (compress data) = data` universally — it assumes that baseline correctness is already
established. It is not. This task is that missing baseline.

**This is, honestly, the largest and least certain item in the closure plan.** Proving `∀ (data :
ByteArray), decompress (compress data) = Except.ok data` for a real DEFLATE implementation (LZ77
match/copy plus canonical Huffman coding, dynamic and fixed blocks, block-boundary bit alignment) is
a substantial formal-methods undertaking — comparable in scope to prior from-scratch DEFLATE/zlib
correctness formalizations elsewhere (a multi-lemma, likely multi-week effort, not a single theorem).
It should not be attempted as one monolithic proof.

## Deliverables & acceptance criteria

- **Phase 1 (design, Law-5-class — required before any proof code):** a `docs/` design doc
  decomposing the roundtrip claim into independently provable sub-lemmas, at minimum: (a) Huffman
  code assignment is prefix-free and uniquely decodable for any symbol-frequency distribution the
  encoder can produce; (b) LZ77 match/copy emission and its inverse agree on any input (the
  window-bounded back-reference is always resolvable against already-decoded output); (c) block
  framing (stored/fixed/dynamic block headers, final-block bit, byte-alignment on stored blocks) is
  self-delimiting and round-trips; (d) container-level composition (zlib's Adler-32 trailer, gzip's
  CRC-32 + ISIZE trailer) is a straightforward wrapper once (a)-(c) hold. State realistically, in the
  design doc, which of these four is likely hardest and why (this task's authors' best guess is (b),
  since it is the one place decoder state depends on unbounded history) and propose a landing order.
  Fresh-agent design review required before implementation — do not waive review on this task.
- **Phase 2:** structural (induction/case-analysis) proofs for as many of the decomposed sub-lemmas
  as this task's effort budget allows, composed into the top-level roundtrip theorems for at least
  `deflate_roundtrip_soundness_inst`'s general form (`∀ data, ...`) — treat the full closure of all
  12 entries as the target, but a partial landing (some sub-lemmas proven generally, others still
  gated behind the pointwise check while flagged as remaining work) is an acceptable, honestly-reported
  intermediate state; state explicitly which entries are fully closed vs. still open at completion.
- Every entry actually closed is removed from `scripts/gate_allowlist.txt`; entries not yet closed
  stay, with their allowlist justification updated to reference this task's design doc rather than
  the bare "migration backlog" text (so a future reader can find the decomposition).
- Zero `sorry`, zero unauthorized axioms for whatever lands; `native_decide`/`decide` never substituted
  for the general `∀ data` claim (Law 10) — a sub-lemma proven only for a finite sampled set of inputs
  does not count as closing that sub-lemma.
- `scripts/check_refs.py` clean; cite `docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems`,
  `#63-canonical-15-roundtrip-soundness-theorems`, `docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem`.
- Completion report must state plainly, per `docs/ORACLE_DEBT.md` Part 4's framing: what fraction of
  the 12 entries this pass actually closed, realistic effort remaining for the rest, and whether the
  Phase 1 decomposition held up in practice or needed revision once Phase 2 started.

## Pointers

- `Stdlib/Zlib/Equivalence.lean:58-137` (the 8 Zlib roundtrip theorems).
- `Stdlib/Png/Equivalence.lean:99-117` (the 2 PNG whole-image roundtrip theorems — depends on
  `Stdlib/Zlib`'s DEFLATE/zlib codec for IDAT compression; sequence this task's PNG closure after its
  own Zlib closure, not in parallel, since PNG's roundtrip is not independently provable without it).
- `Spikes/Spike5Gzip/Equivalence.lean:74-92` (the 2 Spike5 duplicates).
- `Stdlib/Zlib/Deflate.lean`, `Stdlib/Zlib/Gzip.lean`, `Stdlib/Zlib/Spec.lean` — the actual
  compress/decompress implementations this task's proofs are stated against.
- `docs/tasks/PA1-crc32-pathfinder.md` — the closest existing precedent for a structural,
  induction-based proof over this codebase's DEFLATE-adjacent machinery (buffer-length induction,
  fold-normalization); reuse its technique and lessons rather than starting from zero.
- `docs/tasks/F6-zlib-to-infinity.md` — the downstream consumer that currently *assumes* this task's
  baseline; F6's "optimize against zlib-ng/libdeflate" premise is stronger once this task's universal
  correctness baseline actually exists rather than being a pointwise check.
- `docs/tasks/TC12-connection-theorem-linter.md` — flag the Spike5/Stdlib gzip-roundtrip duplication
  to whoever picks that task up, if not already in its known-twins list.
- `docs/ORACLE_DEBT.md` Part 4 — this task's honest difficulty classification (large but plausibly
  tractable with sustained effort, distinct from PA14's new-mathematics-risk classification).

## Notes

- 2026-08-27: priority 8.5 — part of the top-priority oracle-debt epic; ranked below the ready-now
  mechanical closures (PA10-PA13, PA15, PA18) because this is explicitly the largest item in the plan
  and forcing it to the very top would starve cheaper, faster wins of attention. Its Phase 1 design
  doc should start promptly given its size, even though full closure will take longer than the rest
  of the plan combined.

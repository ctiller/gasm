---
id: TC20
title: Wasm emission roundtrip (LEB128 decoder + validator differential)
status: implementing
blocked_on: ""
after: []
related: []
bar: ""
track: trust-core
priority: 6.0
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# TC20: Wasm emission roundtrip (LEB128 decoder + validator differential)

## Context

Sourced from `TCB.md` **T7 — Wasm binary emission** (TCB priority 5). `Wasm/Linker.lean` (already
flagged elsewhere in PLAN.md's findings ledger as misnamed — it's a module emitter, not a linker)
and `LEB128.lean` are both unproven. TCB's central finding: **no LEB128 decoder exists in the
tree**, so a roundtrip theorem (`decode (encode n) = n`) is currently unstatable, not merely
unproven — there is nothing to state it against. Separately, `encodeI64SLEB128 := encodeI32SLEB128`
has **no width bound** — a 64-bit signed value that doesn't fit in the 32-bit encoder's assumed
range will silently misencode. Section ordering in the emitted module is enforced only by source
comments, not by any type or check. `findTypeIdx` returns `0` on a not-found lookup rather than
failing, meaning a genuine type-index mismatch silently encodes as a reference to type `0` instead
of erroring.

The validation gap this compounds: the V8 differential oracle (built by TC2's Wasm fuzzing work)
validates only fuzzer-synthesized modules — **it has never validated a single spike-emitted Wasm
module**. This is the Wasm-target sibling of TC14's finding that Spike 4/5's Windows PEs are never
executed: the emission path that actually produces the artifacts this project claims to verify is
the least-validated part of the whole pipeline, on both targets.

TCB frames the fix as completing a Law-12 connection theorem that is currently missing its other
half: an encoder without a decoder cannot have a roundtrip proof, because there's nothing on the
right-hand side of the equation.

## Deliverables & acceptance criteria

- A LEB128 decoder (both unsigned and signed variants) written in Lean, sufficient to invert the
  existing encoders.
- A kernel-checked roundtrip theorem (`decode (encode n) = n`, quantified over the relevant integer
  domain per Law 9 — no pinned sample values) for both unsigned and signed LEB128.
- `encodeI64SLEB128`'s width-bound gap fixed — either a genuine 64-bit-aware encoder or an explicit,
  proof-visible precondition restricting it to the 32-bit-safe subrange, whichever is actually
  correct for how it's called; silent truncation is not acceptable either way.
- `findTypeIdx`'s not-found case changed from `0` (silent misencoding) to an explicit failure the
  caller must handle.
- Section-order enforcement moved from a comment convention to something checked (a build-time
  assertion at minimum; a type-level guarantee if cheap).
- Every spike-emitted Wasm module actually run through a validator — `wasm-tools validate` or the
  in-browser/Node `WebAssembly.validate`, whichever this repo's existing Node harness plumbing
  (from the Wasm control-flow fuzzer) makes cheaper to wire in — with a byte-flip negative control
  demonstrating the validator actually rejects a corrupted module (Law 13(4)).
- Completion report: roundtrip theorem statement and proof status (zero sorry), the
  `encodeI64SLEB128`/`findTypeIdx` fixes, and validator results for every spike Wasm module
  (Spike1–5's Wasm emissions) including the negative-control demonstration.

## Pointers

- `Gasm/Targets/Wasm/Linker.lean` — the module emitter (misnamed; consider whether renaming falls
  in scope here or is a separate small cleanup — PLAN.md's findings ledger already flags the name
  independently).
- `Gasm/Targets/Wasm/LEB128.lean` — grep for `encodeI32SLEB128`/`encodeI64SLEB128`/`findTypeIdx` to
  confirm current signatures and line numbers before starting (TCB's citations are from
  2026-08-27 @ `1cf58d5`).
- The Wasm control-flow fuzzer's Node-based host-oracle plumbing (from TC2's work) — the natural
  place to hang a `WebAssembly.validate` call for this task's validator differential, if reuse is
  cheaper than a fresh `wasm-tools` invocation.
- `TCB.md` §T7 in full.
- `docs/REVIEW.md` Law 9 (universal quantification — the roundtrip theorem's domain), Law 12
  (connection theorem — this task supplies the missing decoder half of an encode/decode pair),
  Law 13(4) (the byte-flip negative control).

## Notes

- 2026-08-27: priority 6.0 — TCB T7 (Wasm binary emission/LEB128) — priority 5 in TCB's own per-item numbering, below the ranked top-8 cutoff.

_(none yet — first entries append here as work begins; mechanical/proof-completion task,
consolidate into an inline `## Design` section before implementation, `design_review:
waived-mechanical`.)_

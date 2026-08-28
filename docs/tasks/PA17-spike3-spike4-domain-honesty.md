---
id: PA17
title: Spike3-Windows and Spike4 route/session domain honesty — beyond Tier-3 "legit" classification
status: ready
blocked_on: ""
after: [PA7, PA8]
related: [PA6, PA9, N8]
bar: ""
track: proof-arch
priority: 8.3
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA17: Spike3-Windows and Spike4 route/session domain honesty — beyond Tier-3 "legit" classification

## Context

Sourced from `docs/ORACLE_DEBT.md`. PLAN.md's Law-9 mock-verification census (the direct input to
`docs/tasks/PA8-law9-migration.md`) classified two groups of grandfathered entries as **Tier 3 —
"legit pattern"** and left them out of PA8's migration scope: Spike3-Windows' `Bool`-indexed
`traceEquivalence` (`cases b; exact spike3_empty_..._inst | exact spike3_canonical_..._inst`) and
Spike4's 3-constructor `HttpRoute`-indexed `traceEquivalence` (`cases r; exact
spike4_{windows,wasm}_{root,status,404}_..._inst` for each target). The census's reasoning was that
these are genuine finite-∀ compositions over a small, exhaustive enum, unlike Spike5's Tier-2
single-constructor evasion.

**This task's premise is that the Tier-3 classification, while correct about the *composition*
being legitimate `∀`-over-an-enum, does not make the *underlying claims per case* universal.** Each
of `spike3_canonical_effect_trace_equivalence_inst`, `spike3_empty_effect_trace_equivalence_inst`,
and all six `spike4_{windows,wasm}_{root,status,404}_trace_equivalence` theorems is still a
`native_decide` check against exactly **one** concrete stdin/HTTP-request byte string per case — not
"any stdin content that would route the same way," but the one literal test vector `defaultSampleInput`
/ `"GET / HTTP/1.1\r\nHost: localhost\r\n\r\n"` etc. `Bool`/`HttpRoute` genuinely has only finitely
many cases, but "which of 3 route classes" is not the actual domain a real HTTP server's correctness
claim needs to range over — the real domain is "any byte string a client could send," and the current
proof says nothing about request-line whitespace variation, header ordering, partial/chunked delivery,
or malformed input within a route class.

**Independent corroboration this gap is not academic**: `docs/tasks/N8-spike4-stack-buffer-overflow.md`
found a real stack buffer overflow, an uninitialized-memory read, and a route-prefix truncation bug
in Spike4's Windows assembly, all invisible to `spike4_windows_*_trace_equivalence` precisely because
each theorem only ever exercises the one hand-picked request string per route. N8's fix is a
regression/negative-control test (variable-size inputs) — appropriate for that task's bug-fix scope,
but it does not and was not meant to make the underlying equivalence claim universal. This task is
what would have caught N8's bugs by construction, not by hand-picked negative testing.

## Deliverables & acceptance criteria

- A design doc (Law-5-class; fresh-agent design review required) specifying, for Spike3-Windows and
  Spike4, what the *real* `∀`-quantified domain should be per route/session class — i.e. `∀ (stdin :
  ByteArray)` for Spike3 (not just `Bool` selecting between two literals) and `∀ (request : ByteArray)`
  constrained to "parses as an HTTP/1.1 request line matching route R" for Spike4 per route — built
  against PA6's read-binder contract shape (any content/length/partial/EOF) and, for Spike4
  specifically, PA7's `VerifiedReactiveProgram` inner/outer contract (Spike4 is a reactive server; its
  per-request equivalence is the *inner* obligation, not a standalone flat trace-equality claim).
- Structural proofs (induction over the byte-string/request-parsing structure, not enumeration) that
  each route/session's handler produces the modeled trace for *any* member of its real domain, not
  just the one literal vector — reusing PA1's/PA15's induction-over-assembly/interpreter-execution
  pattern where applicable.
- `spike3_canonical_effect_trace_equivalence_inst`, `spike3_empty_effect_trace_equivalence_inst`, and
  all six `spike4_{windows,wasm}_{root,status,404}_trace_equivalence` theorems removed from
  `scripts/gate_allowlist.txt`'s `grandfathered` category, superseded by the general theorems above
  (their downstream `axiom-only` consumers — `spike3VerifiedProgram`, `spike4_{windows,wasm}
  _route_equivalence`, `spike4{Windows,Wasm}VerifiedProgram` — are re-checked to confirm they now
  cite the general theorems and carry no residual pointwise-check axiom).
- Explicitly re-examine, in the design doc, whether N8's three fixed bugs are now *provably absent*
  under the new universal proof (not just absent from the regression suite N8 added) — this is the
  task's real validation that the migration achieved something N8's pointwise fix could not.
- Zero `sorry`, zero unauthorized axioms for whatever lands; `lake exe check_gates_axioms` clean.
- `scripts/check_refs.py` clean; cite `docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence`
  and `docs/REVIEW.md` Law 9.
- Completion report states explicitly whether this task's finding (Tier 3 "legit" is legit about the
  outer composition but not the inner pointwise checks) should be fed back into PLAN.md's census
  language, since a future spike author reading only "Tier 3 = legit pattern, no action needed" would
  reasonably conclude no further work was required here.

## Pointers

- `Spikes/Spike3SortLines/Windows/Equivalence.lean:59-87` (the `Bool`-cased composition and its two
  grandfathered constituents).
- `Spikes/Spike4HttpServer/Equivalence.lean:93-202` (all six per-route theorems, the `HttpRoute`
  composition, and the two `VerifiedProgram`/`VerifiedWasmProgram` instances built on them).
- `docs/tasks/N8-spike4-stack-buffer-overflow.md` — the concrete evidence this gap is live, not
  theoretical; read in full, including its "why this evaded detection" section, which names the exact
  pointwise-proof mechanism this task closes.
- `docs/tasks/PA8-law9-migration.md` — the census this task's premise directly engages with; read its
  Tier 1/2/3 framing before starting, and coordinate rather than duplicate PA8's own Spike4 slice
  (PA8's acceptance criteria already commits to "Spike4's Tier-3 HttpRoute verification re-expressed
  as a VerifiedReactiveProgram inner/outer pair once PA7 lands" — this task's job is the domain
  widening underneath that re-expression, not the re-expression itself; sequence after or alongside
  PA8's Spike4 slice, not instead of it).
- `docs/tasks/PA6-read-binder-contract.md`, `docs/tasks/PA7-verified-reactive-program.md`,
  `docs/tasks/PA9-verified-program-derived.md` — the contract-shape prerequisites this task's
  universal proofs are stated against.
- `docs/ORACLE_DEBT.md` — originating audit; Part 4 classifies this as reachable but gated on the
  PA5→PA6/PA7 architecture chain landing first, not on any new mathematics.

## Notes

- 2026-08-27: priority 8.3 — part of the top-priority oracle-debt epic; sequenced `after: [PA7, PA8]`
  because Spike4's reactive contract type and PA8's Environment-quantification mechanism are genuine
  prerequisites, not bureaucratic ordering — attempting this task's Spike4 slice before PA7 lands
  would mean re-doing the outer-contract re-framing PA8 already commits to.

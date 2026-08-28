---
id: PA15
title: Fibonacci soundness by loop-invariant induction — replace 91-case native_decide enumeration
status: ready
blocked_on: ""
after: []
related: [PA1, B7]
bar: ""
track: proof-arch
priority: 9.2
priority_set: 2026-08-28T02:00:00Z
design: "inline"
design_review: "waived-mechanical"
date: 2026-08-27
---

# PA15: Fibonacci soundness by loop-invariant induction — replace 91-case native_decide enumeration

## Context

Sourced from `docs/ORACLE_DEBT.md`. `fib_iter_asm_soundness` (`Spikes/Spike2Fibonacci/Windows/
Equivalence.lean`) and `fib_iter_wasm_soundness` (`Spikes/Spike2Fibonacci/Wasm/Equivalence.lean`)
are both `finite-forall`-allowlisted: `(List.range 91).all (fun n => runFibIterAsm n == (fibIter
n).toUInt64) = true`, discharged by `native_decide` — i.e. the assembly/Wasm routine is *executed* by
the in-Lean simulator for each of 91 concrete inputs and the result compared against the spec. This
is a real universal statement over a genuinely finite, well-motivated domain (`UInt64` overflow bounds
the meaningful range to `n ≤ 93`, per the allowlist's own note), so it is not pointwise-fraudulent the
way the 37 `grandfathered` entries are — but it is still an oracle-backed axiom (`native_decide`),
and the domain was chosen partly *because* exhaustive simulation is the easiest way to check it, not
because a general proof was attempted and found infeasible.

The routine is a straightforward iterative loop (`fibIterInstructions`/its Wasm equivalent): each
iteration computes the next Fibonacci pair from the previous one. This is exactly the loop-invariant
induction shape `docs/tasks/PA1-crc32-pathfinder.md` demonstrated is tractable for assembly loops
(`crc32InternalFold`'s `List.foldl` connection theorem, proven by induction on prefix length via
`updateCrc32_eq_fold`) — the same technique applies directly here: state the loop invariant
("after `k` iterations, the two live registers hold `(fibIter k, fibIter (k+1))`"), prove it by
induction on `k` against the loop body's `step` semantics, and conclude the `n = 91` (or wider)
case as a corollary rather than as 91 separately-simulated instances.

## Deliverables & acceptance criteria

- A loop-invariant theorem for the assembly routine (`Spike2Fibonacci/Windows`): `∀ k, <machine state
  after k loop iterations of fibIterInstructions matches the pair (fibIter k, fibIter (k+1))
  in the designated registers>`, proven by induction on `k`, following PA1's connection-theorem
  pattern (per-instruction step lemmas at the loop body, chained by induction rather than unrolled by
  simulation).
- The equivalent for the Wasm routine (`Spike2Fibonacci/Wasm`), against the Wasm interpreter's
  `step`/fold semantics.
- `fib_iter_asm_soundness`/`fib_iter_wasm_soundness` restated as corollaries of the general
  loop-invariant theorem at the specific bound the `UInt64`-overflow domain actually supports (the
  allowlist's own note says the true bound is `n = 0..93`, one wider than today's `0..90` claim —
  fix the off-by-a-few bound as part of this task, per the allowlist comment's own "should be widened
  ... tracked as a separate follow-up" — this task is that follow-up), discharged by the induction,
  not `native_decide`.
- Both entries removed from `scripts/gate_allowlist.txt`'s `finite-forall` category (a structural
  induction needs no Law 10 allowance).
- Zero `sorry`; `lake exe check_gates_axioms` clean; `#print axioms` confirms neither theorem carries
  a `_native.*` axiom.
- The Wasm-target proof is stated against the current `Gasm/Targets/Wasm/Semantics.lean`; since
  `docs/tasks/B7-wasm-oob-trap-and-limits.md` is concurrently changing that file's trap-handling
  paths, confirm the Fibonacci routine never performs a memory access near a bound affected by B7's
  change (expected: it doesn't, this is a pure-arithmetic loop with no memory access) and note this
  explicitly in the completion report so a reader doesn't have to re-derive it.
- `scripts/check_refs.py` clean; cite `docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence`.

## Pointers

- `Spikes/Spike2Fibonacci/Windows/Equivalence.lean:42-49` (`runFibIterAsm`, `fib_iter_asm_soundness`).
- `Spikes/Spike2Fibonacci/Wasm/Equivalence.lean:39-49` (`runFibIterWasm`, `fib_iter_wasm_soundness`).
- `docs/tasks/PA1-crc32-pathfinder.md` and `Stdlib/Zlib/CRC32Equivalence.lean:134-166`
  (`crc32InternalFold`, `updateCrc32_eq_fold`) — the induction-over-a-loop pattern to reuse directly.
- `scripts/gate_allowlist.txt:79,81` — the two allowlist entries and their own note on the true
  `UInt64`-safe domain being `0..93`, not `0..90`.
- `docs/tasks/B7-wasm-oob-trap-and-limits.md` — concurrent Wasm-semantics work; confirm no
  interaction (expected none, per above).
- `docs/ORACLE_DEBT.md` — originating audit.

## Notes

- 2026-08-27: priority 9.2 — no architectural prerequisite; PA1 already demonstrated the exact
  technique this task reuses. Also closes a known, already-flagged off-by-a-few domain bound
  (`0..90` vs the true `0..93`) as a side effect.

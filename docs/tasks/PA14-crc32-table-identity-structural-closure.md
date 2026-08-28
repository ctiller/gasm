---
id: PA14
title: G8bf_table structural closure — CRC table/bit-loop identity without a SAT certificate
status: ready
blocked_on: ""
after: []
related: [PA1, PA13]
bar: ""
track: proof-arch
priority: 7.5
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA14: G8bf_table structural closure — CRC table/bit-loop identity without a SAT certificate

## Context

Sourced from `docs/ORACLE_DEBT.md`, the hard remainder of PA13's `bv_decide` triage. `G8bf_table
(poly x : UInt32) : Gbf8 poly x = (x >>> 8) ^^^ Gbf8 poly (x &&& 0xFF)` (`Stdlib/Zlib/
CRC32Equivalence.lean:229-233`) is the design's primary Law-12 connection identity (per
`docs/PATHFINDER_CRC32.md` §3.6): applying the 8-step per-bit CRC update to a full 32-bit value
equals shifting it down by 8 and XORing in the 8-step map applied to just its low byte — i.e. exactly
what a byte-indexed CRC table precomputes. It is discharged today by a single `bv_decide` SAT
certificate over the complete `UInt32 × UInt32` domain (`2^32` pairs), ~1.8s wall time.

Per `TCB.md` T14, this axiom is in the same trust class as `native_decide` — not kernel-checked. Per
the owner's zero-axiom target this is a genuine gap, but per the same finding, **this is the one
entry in the whole 80-item ledger most likely to require either new mathematics or new tooling, not
just more proof-engineering time**:

- A **from-scratch structural proof** would need to peel `Gbf`'s bit-level update eight times and
  show the resulting 32-bit expression is definitionally/propositionally equal to the shift-and-XOR
  form — this is, in substance, re-deriving the standard "CRC table = repeated polynomial-division
  step" identity by hand, over `BitVec 32` arithmetic with no first-class GF(2)-polynomial-ring
  library in this project or (to this task's knowledge) in Lean's standard library. It is a bounded,
  finite fact (decidable in principle, which is exactly why `bv_decide` can certify it), but "bounded
  and finite" does not mean "cheap to hand-prove" — the natural proof shape is either (a) an
  8-fold unfolding with `omega`/`BitVec` bit-extensionality at each step (mechanical but likely very
  long and fragile to write by hand), or (b) building enough GF(2) polynomial algebra from scratch to
  state and use the standard division-remainder argument (a genuine mathematical-library-building
  project, not a single lemma).
- The **upstream alternative** — Lean core adding a kernel-replay path for LRAT certificates (so
  `bv_decide` becomes actually kernel-checked instead of native-eval-trusted) — is outside this
  project's control and has no announced timeline; `TCB.md` T14 confirms no `checkProofs`-style
  option exists in the pinned toolchain (v4.33.1) for `bv_decide` today.

This task exists so the attempt is tracked and scoped honestly, not so its success is assumed. Per
`docs/ORACLE_DEBT.md` Part 4, this is one of two entries in the ledger classified as **not confidently
reaching zero on a bounded timeline** (the other being PA16's codec-roundtrip proofs, for a
different reason — sheer size, not new-mathematics risk).

## Deliverables & acceptance criteria

- A design note (this task's own `## Design` section, or a short `docs/` note if it grows) surveying
  the two approaches above and picking one to attempt first, with a stated abandonment criterion
  (e.g. "if the 8-fold unfolding proof exceeds N lines / M hours without closing, stop and report
  status rather than continuing indefinitely") — this is explicitly permitted: a well-scoped, honest
  "attempted, did not close, here is exactly where it got stuck" report is an acceptable outcome for
  this task, per `docs/ORACLE_DEBT.md` Part 4's framing that forcing a false "done" here would be
  worse than an honest partial result.
- If a structural proof succeeds: `G8bf_table` re-proven without `bv_decide`; removed from
  `scripts/gate_allowlist.txt`'s `finite-forall` category; `#print axioms` confirms no `_native.*`/
  `bv_decide.ax_*` axiom on it or on its downstream consumer `crc32ByteStep_eq_G8`.
- If a structural proof does not succeed in this pass: the current `bv_decide` proof is retained
  (this is strictly better than a pointwise `native_decide` check on a single input — the owner's
  prior approval of `bv_decide` as an interim posture stands per `docs/ORACLE_DEBT.md` Part 4), and
  the completion report states precisely what was tried, how far it got, and what a future attempt
  would need (a partial GF(2) algebra library outline, or a specific upstream Lean feature request,
  whichever the investigation points to). This is a legitimate, bounded-effort outcome for this task —
  do not treat "did not reach zero" as task failure if the investigation and partial-progress record
  are genuine.
- Either way: `lake build` + `lake exe check_gates_axioms` clean, no regression to PA1's existing
  proof state.

## Pointers

- `Stdlib/Zlib/CRC32Equivalence.lean:207-233` (`G8`, `Gbf8`, `G8bf_table`) and `:260-271`
  (`crc32ByteStep_eq_G8`, the downstream connection theorem that consumes `G8bf_table`).
- `TCB.md` §T14 in full — the `bv_decide`-not-kernel-checked finding and its note that no
  `checkProofs`-style kernel-replay option exists in this toolchain.
- `docs/PATHFINDER_CRC32.md` §3.6 — the design's own framing of this identity as "the connection
  theorem... on a branch-free normal form."
- `docs/tasks/PA13-crc32-bittrick-lemmas-without-sat.md` — the sibling task for the three smaller
  `bv_decide` lemmas this task's identity depends on (`and_one_cases`, `G_eq_Gbf`, via `Gbf8`'s
  definition) — coordinate rather than duplicate; PA13's lemmas, once migrated, do not by themselves
  close this task's identity, which needs its own separate argument.
- `docs/ORACLE_DEBT.md` Part 4 — the honest not-reachable-to-zero classification this task is one
  instance of.

## Notes

- 2026-08-27: priority 7.5 — part of the top-priority oracle-debt epic in spirit, but deliberately
  ranked below the ready-now mechanical closures (PA10-PA13, PA15, PA18) because this is the one item
  in the ledger most likely to need either new mathematics or new Lean tooling rather than more
  engineering hours; starving the cheap wins to chase this first would be the wrong sequencing.

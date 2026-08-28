---
id: MT4
title: "Emitted-binary litmus battery: SB / MP / SB+MFENCE, reusing XM2's definitions"
status: blocked
blocked_on: "XM2 (litmus encodings + model outcome enumeration + host silicon harness, filed with docs/X86_MEMORY_MODEL.md §10) — this task consumes XM2's test definitions and enumerated outcome sets rather than re-transcribing them (Law 12); convert to an after: [XM2] entry once XM2's task file is stably in-tree"
after: [MT1, MT2, MT3]
related: [TC17, F2]
bar: ""
track: concurrency
priority: 6.5
priority_set: 2026-08-28T00:00:00Z
design: "docs/SPIKES/SPIKE8_MULTITHREADING.md"
design_review: ""
date: 2026-08-28
---

# MT4: Emitted-binary litmus battery — SB / MP / SB+MFENCE, reusing XM2's definitions

## Context

Implements `docs/SPIKES/SPIKE8_MULTITHREADING.md` §2, §4, §7. Division of labor with
XM2 (`docs/X86_MEMORY_MODEL.md` §7, §10): XM2 owns the litmus test *definitions*, the
mechanical enumeration of the model's allowed-outcome sets (the full battery: SB, MP,
LB, 2+2W, IRIW, fenced/locked variants), the host-side multi-threaded silicon harness,
and the Law 14 calibration-artifact regime for its results. This task embeds the
**SB / MP / SB+MFENCE subset** in Spike 8's *emitted, proof-carrying binaries* — the
end-to-end check that the code gasm emits (not just host threads exercising silicon)
exhibits exactly the model's outcome sets on all spike targets. One source for test
bodies and expected sets: XM2's encodings, consumed, never duplicated.

A forbidden outcome observed falsifies the model or the emission (exit 1); an SB
witness that never appears means the race was not exercised and the run validated
nothing (exit 2, honest-runner convention, TC17's vacuity principle — the same
negative-control discipline XM2's harness carries).

## Deliverables & acceptance criteria

- Emitted litmus programs for SB, MP, SB+MFENCE whose bodies and expected outcome
  sets are derived from XM2's definitions; the spike-side statements of
  `sb_outcome_set` / `mp_outcome_set` / `sb_mfence_outcome_set` reference XM2's
  enumeration, not hand-written tables.
- Harness shape per the spike design §2.4: two persistent worker threads,
  per-iteration handshake, randomized stagger (0–63), distinct cache lines,
  K=100,000 iterations per test (env-overridable), histograms to stderr,
  deterministic verdict lines to stdout per §2.5.
- Exit-code semantics wired: 0 = pass including SB witness floor; 1 = forbidden
  outcome or wrong verdict (stderr histogram + PRNG seed as reproduction artifact);
  2 = witness absent (race not exercised — single-CPU host, TCG) reported honestly.
- CI wiring: battery runs on every spike execution; a larger-budget stress lane off
  the critical path.

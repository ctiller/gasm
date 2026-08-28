---
id: MT3
title: "Causal traces for threads: stampMultiThreaded, sync edges, causal-order equivalence"
status: ready
blocked_on: ""
after: [PA5]
related: [G2, PA7, MT2]
bar: ""
track: concurrency
priority: 6.5
priority_set: 2026-08-28T00:00:00Z
design: "docs/SPIKES/SPIKE8_MULTITHREADING.md"
design_review: ""
date: 2026-08-28
---

# MT3: Causal traces for threads — stampMultiThreaded, sync edges, causal-order equivalence

## Context

Implements `docs/SPIKES/SPIKE8_MULTITHREADING.md` §5.4. The ratified groundwork is
already in tree and this task makes it load-bearing: `VectorClock` /
`happensBefore` / `join` / `tick` (`Gasm/Core/Types.lean`), `CausalEvent` and
`stampSingleThreaded` (`Gasm/Effects/CanonicalizeTrace.lean`), the synchronizes-with
edge design (`docs/OBLIGATIONS_AND_CAUSALITY.md` §3.1), and PLAN.md Phase-4 items
(d)/(e): canonical form is a causally-ordered event set; equivalence is equality of
causal orders, linearization-insensitive; a multi-threaded trace is stated as
per-thread traces plus happens-before — never a distinguished interleaving.

Coordination duty: G2 (GPU synchronization DSL) builds synchronizes-with edges into
the same causal layer for Vulkan. Whichever of MT3/G2 lands second consumes the
first's edge vocabulary; forking `VectorClock` machinery is a design failure.

## Deliverables & acceptance criteria

- `stampMultiThreaded` generalizing `stampSingleThreaded`: per-thread clock ticks;
  cross-thread joins at exactly three edge kinds — spawn (parent→child), join
  (child→parent), lock release→acquire (the acquire that reads a given release store
  joins the releaser's clock). Per `docs/X86_MEMORY_MODEL.md` §3 item 1 (which
  explicitly assigns these obligations to the threaded-spike design): the
  synchronizes-with edges are taken **as input from the machine model** — the memory
  model generates happens-before edges, the trace layer projects them; no second
  happens-before vocabulary.
- **Trace-order soundness** (`docs/X86_MEMORY_MODEL.md` §3 item 2, accepted here):
  the connection theorem that a causal edge asserted in the canonical trace is backed
  by machine happens-before — same-thread program order, or a chain through sw edges.
  The trace layer may never claim causality the machine does not enforce.
- `stampSingleThreaded` proven to be the one-thread specialization (existing
  single-threaded canonicalization theorems preserved, not re-proven).
- Causal-order equivalence: equality of happens-before structures over canonicalized
  event sets; coalescing only across causally-consecutive writes (SYSTEM_EFFECTS §6.4
  barrier discipline unchanged).
- The schedule-as-universal-binder contract shape: theorem statements quantify over
  the scheduler oracle; pinning one interleaving is unrepresentable (Law 9, the
  read-binder principle extended to concurrency).
- Per-loop inner/outer obligations generalized to multiple loops per program (PLAN.md
  item (d)): contract-level slots for per-loop pairs plus composition obligations
  (deadlock-freedom at declared sync points, explicit named fairness hypotheses) —
  consumed by MT5's spin-loop proofs and, later, PA7-per-Spike-4.

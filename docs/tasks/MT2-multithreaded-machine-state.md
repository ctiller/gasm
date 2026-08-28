---
id: MT2
title: "Thread lifecycle and per-thread execution state over XM1's TSO machine"
status: blocked
blocked_on: "XM1 (docs/X86_MEMORY_MODEL.md §2.3) — the two-level TSO state (shared memory + per-thread store buffers), TsoStep/drain, and the single-thread degeneration theorem are XM1's deliverables that this task builds on; convert to after: [XM1] once XM1's task file is stably in-tree"
after: [MH1]
related: [MT1, PA2]
bar: ""
track: concurrency
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: "docs/SPIKES/SPIKE8_MULTITHREADING.md"
design_review: ""
date: 2026-08-28
---

# MT2: Thread lifecycle and per-thread execution state over XM1's TSO machine

## Context

D30/ADR-0039 ruled machine state grows on spike demand; Spike 8 is that demand
(`docs/SPIKES/SPIKE8_MULTITHREADING.md` §5.3). The memory half is XM1's: per-thread
FIFO store buffers over the shared sealed `X86_64Memory`, the `TsoStep`/`drain`
relation, and the degeneration theorem linking the one-thread case to today's
sequential interpreter (`docs/X86_MEMORY_MODEL.md` §2.3). This task builds the
execution layer above it: per-thread register/flags/RIP state indexed by the existing
`ThreadId` (`Gasm/Core/Types.lean`), the multi-thread scheduling step, and the thread
lifecycle. Not demanded and not in scope: XMM, MXCSR, fault taxonomy, interrupt state
(same Law 5 logic that declined P1 in D30).

## Deliverables & acceptance criteria

- A multi-threaded machine state whose **one-thread specialization is the existing
  `X86_64MachineState`** in the sense that all ~88 instruction step functions and
  their step lemmas keep elaborating against a per-thread view (that thread's
  registers + the shared memory hook) **without per-instruction rewrites**. A
  migration that touches instruction semantics files beyond imports/plumbing fails
  this task's bar. (This composes with, and does not re-prove, XM1's degeneration
  theorem: XM1 links the memory semantics; this task links the execution state.)
- The multi-thread step relation: "pick a runnable thread (or take an XM1
  model-internal action such as a store-buffer drain), step its view." Scheduling
  nondeterminism lives here — never inside an instruction.
- Spawn/terminate/join transitions sufficient for Spike 8's thread lifecycle, emitting
  the causal edges MT3 consumes.
- Single-threaded regression: all existing spike proofs and gates green with the
  specialization in place.
- Negative control (Law 13): demonstrate, then revert, that a direct raw-memory access
  from a second thread bypassing the MH1 hook fails to elaborate.

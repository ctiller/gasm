---
id: MT5
title: "Spike 8 Phases A+B: Windows CreateThread + Linux clone spinlock counter, verified"
status: ready
blocked_on: ""
after: [MT4, PA7]
related: [N1, B2]
bar: ""
track: concurrency
priority: 6.5
priority_set: 2026-08-28T00:00:00Z
design: "docs/SPIKES/SPIKE8_MULTITHREADING.md"
design_review: ""
date: 2026-08-28
---

# MT5: Spike 8 Phases A+B — Windows + Linux spinlock counter, verified

## Context

Implements `docs/SPIKES/SPIKE8_MULTITHREADING.md` §3, §6.1–6.2, §7.1. The verified
computation: two threads, each 100,000 increments of a shared counter under an
XCHG-based test-and-set spinlock, unlock by plain `MOV` (correct only under TSO — the
proof of that line is the memory model earning its keep), assertion `count = 200,000`
at join. The spin loop is the tree's first liveness-bearing loop and instantiates the
inner/outer reactive pair (hence `after: PA7`): inner = deterministic critical-section
equality per acquisition; outer = progress under an explicit named fairness
hypothesis.

Target mechanisms: Windows extends the `Gasm/Targets/Windows/Win32API.lean`
import/hook pattern with `CreateThread` / `WaitForSingleObject` / `ExitThread`;
Linux uses raw `SYS_clone` (56, `CLONE_VM|CLONE_FS|CLONE_FILES|CLONE_SIGHAND|
CLONE_THREAD`) with an `mmap`'d child stack and join-by-spin on a done flag —
deliberately no `futex` in v1 (recorded debt; grows when a spike demands blocking
waits).

## Deliverables & acceptance criteria

- Spike trio (`Spec`/`Program`/`Equivalence`) under `Spikes/Spike8Multithreading/`,
  Windows + Linux targets, lake exes and test runners per the established
  `spikeN_*`/`test_spikeN_*` naming.
- Theorems: `spinlock_mutual_exclusion` (∀ schedules), `spike8_counter_correct`
  (∀ schedules, joined count = 2*M), `spike8_progress` (fairness-hypothesized), and
  per-target trace refinement + liveness per `docs/EQUIVALENCE_PROOFS.md` §1.1's
  nondeterministic-spec direction. No pointwise/pinned-schedule equivalences (Law 9).
- Win32 additions follow the existing descriptor + hook shape; hook semantics route
  through MT2's scheduler layer (spawn/join causal edges emitted for MT3 stamping).
- `SYS_clone` flag semantics cited (man-page/kernel reference ingestion per Law 4 —
  the reference corpus entry is part of this task).
- Hardware runs on both OS targets execute the MT4 battery AND the counter; exit
  codes per the honest-runner convention.
- Deferred debts recorded in the spike doc on landing: futex, `CMPXCHG`-based locks,
  thread-count generalization beyond 2.

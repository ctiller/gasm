---
id: BR3
title: "Cross-thread capability partition and the no-unsynchronized-race theorem"
status: blocked
blocked_on: "MT2's multi-threaded machine does not exist (itself blocked on XM1), and cross-thread capability transfer — spawn hands regions to a child, join returns them, a lock acquire grants dynamically — has no design or task anywhere; this task cannot start until there is a machine with more than one thread to state the theorem against"
after: [BR1, MT2]
related: [MT1, MT3, MT4, MH3]
bar: ""
track: concurrency
priority: 6.6
priority_set: 2026-08-28T00:00:00Z
design: "docs/BORROW_MODEL.md"
design_review: ""
date: 2026-08-28
---

# BR3: Cross-thread capability partition and the no-unsynchronized-race theorem

## Context

Implements `docs/BORROW_MODEL.md` §8. The owner's demand names multithreading and
borrowing together (`docs/BORROW_MODEL.md` §10.1), and this is the task where they meet:
if shared-XOR-mutable excludes conflicting concurrent plain accesses, then the borrow
model and the memory model discharge one obligation between them — the borrow model
establishes that authored programs are data-race-free on plain accesses, and the memory
model then only has to state *ordering* for the synchronized ones. That is the difference
between x86-TSO mattering for safety and mattering only for ordering.

**Deliberately partial, and that is the correct scope.** The theorem excludes conflicting
plain accesses. It does not, and must not, exclude conflicting accesses to regions whose
safety rests on atomicity rather than exclusion — a borrow model that excluded all races
would exclude spinlocks, and Spike 8's verified computation is a spinlock
(`docs/SPIKES/SPIKE8_MULTITHREADING.md` §3).

## Deliverables & acceptance criteria

- The cross-thread well-formedness invariant of `docs/BORROW_MODEL.md` §8: a partition of
  authority across threads, lifting the existing single-context disjointness invariant
  (`Gasm/Core/Permissions.lean:58-62`) to a family of contexts.
- The no-unsynchronized-race theorem in the shape `docs/BORROW_MODEL.md` §8 states, over
  MT2's machine, universally quantified over threads, accesses and states (Law 9 — no
  pointwise instance, no purpose-built stand-in domain).
- The synchronized-access predicate that the theorem excludes by hypothesis, defined by
  the *obligation* an access owes rather than by x86's mechanism for discharging it —
  `docs/BORROW_MODEL.md` §9 records why: AArch64's exclusive monitor is a load/store pair
  that can fail and retry, so a definition phrased as "one indivisible access" is an x86
  assumption an ARM implementor cannot satisfy.
- Cross-thread capability transfer, which does not exist and must be designed before it is
  built (Law 5, stop-and-design): what spawn hands to a child, what join returns, and what
  a lock acquire grants. **If this task is picked up before that design exists, it must
  stop and produce the design first.**
- **Honesty bar**: the theorem's premise is an invariant over concrete addresses, so it
  inherits the aliasing gap in full (`docs/BORROW_MODEL.md` §11 item 1). If two threads'
  regions alias without the model knowing, the premise is false and the theorem says
  nothing. This must be stated where the theorem is stated, not only here.

## Pointers

- `docs/BORROW_MODEL.md` §8 (the theorem shape and its two caveats), §2.2 (the third
  authority mode this theorem excludes), §9 (architecture neutrality), §11 (limits).
- `docs/X86_MEMORY_MODEL.md` §2.3 (the machine this is stated against), §3 (composition
  with trace-level causality).
- `docs/SPIKES/SPIKE8_MULTITHREADING.md` §3, §5.2.
- `docs/tasks/MT2-multithreaded-machine-state.md` — the blocking dependency.

## Notes

_(none yet)_

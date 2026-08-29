# Obligations and Causality

**Status (2026-08-28): current-code inventory plus design boundary.** The generic obligation
records and vector-clock operations described below exist. Typed lock/join obligations,
multi-thread execution, architecture memory models, and concurrent trace projection do not. Their
canonical design and implementation sequence are `docs/MEMORY_MODEL.md` §§6–14.

This file is an orientation note. It must not be used as evidence that a protocol is implemented.

---

## 1. The Linear Obligation Ledger

`Gasm/Core/Obligations.lean` defines a generic, value-level `ObligationToken` containing a string
kind, numeric resource identifier, and `droppableOnExit` flag. `ComposedState` stores a list of
those tokens, and helper functions add, remove, and test them. This is useful bookkeeping, but it is
not yet a typed linear resource system:

- tags and identifiers can be forged or confused;
- the token type is `Inhabited` and ordinary values are duplicable;
- no acquisition generation prevents address reuse/ABA confusion;
- `BlockM.set` can replace the obligation list through a general state transition;
- no existing token constructor encodes `MustRelease`, `MustJoin`, or a live lock guard.

`Gasm/Core/Types.lean` defines `ThreadId`, `VectorClock.happensBefore`, `join`, and `tick`.
`ComposedState` has one clock. There is no scheduler-owned table of independently executing thread
states, so current vector-clock use is the one-thread-degenerate case.

The following names appeared in an older version of this document but do **not** exist in Lean:
`ObligationType`, `MustUnlockMutex`, and `MutexState.lastReleaseClock`.

### 1.1 Multiset Obligation Subtraction (`List.eraseAll`)

`List.eraseAll` removes one matching element per requested discharge. `eraseAllChecked` additionally
fails when a requested token is absent. These are current list operations, not proof that token
values are linear or that their string kinds implement a protocol.

---

## 2. Obligation Preservation across Control Flow Transitions

### 2.1 Function Returns (`CpuTerminator.ret`)

The current ledger predicate `ObligationLedger.isValidAtReturn` requires an empty token list, but
`CpuTerminator.ret` does not use it: it can export any caller-selected list equal to the current
ledger. Return/CFG code therefore carries selected value-level conditions, not the typed, closed
transition or sealed postcondition required below.

### 2.2 Unconditional Exits (`CpuTerminator.sysExit`)

`ObligationLedger.isValidAtExit` accepts only tokens marked `isDroppableOnExit`. That Boolean is a
current process-scope convention, not authority for thread exit to discard locks, join rights, or
arbitrary resources.

### 2.3 Required obligation model

Checked assembly needs typed, generational resources in an indexed authoring context, including:

- `MustRelease lockInstance acquisitionGeneration owner protectedRegion`;
- `MustReturnLoan loan issuer holder region`;
- `MustJoin child joinRight` or an explicit detach transition;
- `MustCloseHandle handle` and other OS-resource obligations;
- allocation and typed-view destruction obligations.

The matching capability, guard, and obligation are separate resources. An operation such as
successful acquire updates them atomically; failed acquire changes none of them. Release requires
and consumes the generation-matched guard, protected authority, and must-release obligation.

Ordinary return exports exactly the postcondition promised by its callable contract. Thread exit
seals a terminal bundle accounting for every authority, loan, grant, guard, and obligation; an
obligation-free capability cannot be stranded in a dead thread. Detach is legal only for an empty
join-owned bundle or an explicit process-owned sink. Process exit is a separate transition, checks
all thread contexts and terminal bundles, and may discard only resources explicitly declared
process-scoped. Scheduler-owned wait registrations
are not author-visible obligations: the scheduler removes them on wake, timeout, supported
interruption/cancellation, or exit.

The checked surface must close over safe constructors. A public operation that can arbitrarily
replace `ComposedState.perms` or `.obligations` is outside that surface. See
`docs/MEMORY_MODEL.md` §§6.2, 7.3, and stages M1/M4/M5-S.

---

## 3. Monotonic Causality & Vector Clocks

### 3.1 Four different ordering relations

Keeping these relations distinct prevents circular or architecture-unsound proofs:

1. **ISA execution consistency** says which memory executions are permitted. x86-64 WB/TSO and
   AArch64 weak memory use different predicates over program order, reads-from, coherence,
   dependencies, atomics, and barriers.
2. **Program happens-before** is created by same-thread order and proved synchronization such as
   spawn, successful join, or a release/acquire pair connected to the relevant write.
3. **Scheduler control causality** records events such as a wake causing a blocked thread to become
   runnable. It does not imply that ordinary memory is visible.
4. **Observable causal order** projects the labelled program and scheduler relations onto external
   effect events.

The labelled edge graph is authoritative. Vector clocks are only relation-aware reachability caches
after source edges have been proved; one clock over the union cannot recover or invent whether an
edge came from program synchronization, scheduler control, or both. They do not define the x86 or
AArch64 memory model and cannot turn a plain read into synchronization.

In particular:

- a successful acquire synchronizes with the particular release whose value/publication it
  observes under the target architecture's rules;
- a failed CAS or AArch64 store-exclusive transfers no authority and creates no acquire handoff;
- `FUTEX_WAKE` and Windows address wake create wake-to-resume scheduler causality, not a release
  fence or memory synchronizes-with edge;
- successful logical join creates a lifecycle edge only through the platform's proved visibility
  refinement and returns only the child's declared sealed bundle.

---

## 4. Concurrent Trace Requirement

Concurrent canonical traces compare labelled partial orders, not arbitrary interleaving lists or
raw vector-clock values. A total, non-inventing quotient maps every raw observable to exactly one
canonical node and coalesces only under named per-effect rules. Between distinct quotient nodes,
projection must be faithful in both directions:

```text
trace edge exists  iff  the corresponding labelled program/scheduler causal edge exists
```

Equality is modulo schedule-independent event-key renaming and partial-order isomorphism. Edge
labels preserve the distinction between memory/lifecycle happens-before and scheduler causality.
This is the M8 exit criterion in `docs/MEMORY_MODEL.md` §14.

---

## 5. Completion Checklist

This note can be promoted from design boundary to implemented contract only when:

- typed obligations and closed indexed transitions replace stringly value-level protocol tokens;
- the process machine has separate per-thread states and true thread exit/join;
- x86 and AArch64 synchronization edges are derived from their respective memory models;
- futex/parking transitions preserve their non-fence semantics;
- trace projection satisfies the bidirectional fidelity theorem; and
- negative controls demonstrate that failed acquire, missing release, wake-only publication, and
  dropped causal edges are rejected.

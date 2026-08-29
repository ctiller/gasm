# Spike 8: Cross-Architecture Multithreading and Synchronization

**Status:** design-stage validation vehicle; not implemented. The canonical semantics,
ownership rules, dependency sequence, and proof requirements are in
`docs/MEMORY_MODEL.md`. This document defines the end-to-end programs that force that model to
be real.

Spike 8 is a family of equivalent validation programs, not one architecture-specific instruction
stream. It validates:

- x86-64 TSO on Windows, Linux, and x86 bare metal;
- AArch64 weak memory on Linux and AArch64 bare metal;
- cross-thread capability partition and lock-protected ownership transfer;
- Linux process-private futex wait/wake on both hosted architectures;
- Windows thread creation and joining, with a Windows parking adapter selected by the canonical
  design’s stop-and-design gate;
- x86 and AArch64 bare-metal SMP through separate bring-up mechanisms.

No part of this spike may introduce a local memory model, borrow model, lock invariant, or causal
relation. It consumes the corresponding stage of `docs/MEMORY_MODEL.md` and provides its
validation demand.

---

## 1. Why Spawn-and-Join Is Not Enough

A program that creates two threads, joins them, and prints a result proves only that a lifecycle
adapter ran. Spike 8 therefore contains three complementary workloads:

1. **Architecture-specific litmus suites** distinguish allowed and forbidden memory outcomes.
2. **A capability-verified shared counter** forces atomicity, visibility, mutual exclusion, and
   ownership transfer to compose.
3. **A contended blocking-lock run** forces the scheduler and Linux futex or platform parking
   adapter to compose with the same lock proof.

The lifecycle-only smoke test still exists, but it is a prerequisite rather than the acceptance
bar.

---

## 2. Litmus Suites

Litmus definitions live in one declarative schema describing threads, initial memory, instructions,
observed registers, and target profile. Expected outcome sets are derived mechanically from the
selected architecture model; emitted programs consume them rather than transcribing tables.

### 2.1 x86-64 Profile

The first x86 suite includes:

- Store Buffering (SB), with `(0,0)` allowed under TSO;
- Message Passing (MP), excluding the outcome that observes the flag without prior data;
- Load Buffering (LB), same-location coherence (`CoRR`/`CoRW`/`CoWW` as applicable), and
  two-writer order tests;
- IRIW/2+2W-style observation tests that exercise x86 global store order and multi-copy atomicity;
- SB with `MFENCE`, excluding `(0,0)`;
- locked-RMW total-order, fence-placement, and release/acquire handoff variants;
- negative controls that remove a fence or atomic operation and change the model outcome set.

The model side uses the WB/TSO profile in `docs/MEMORY_MODEL.md` §5.1. Device/MMIO operations
are not mixed into RAM litmus tests.

### 2.2 AArch64 Profile

The first AArch64 suite includes:

- SB and MP using plain weakly ordered `LDR`/`STR` (not relaxed atomics);
- MP using release/acquire operations;
- address-, data-, and control-dependency families appropriate to the pinned profile;
- WRC, RWC, IRIW, and other observation/cumulativity families from the pinned official suite;
- barrier variants that distinguish the selected `DMB` access classes and shareability scopes;
- exclusive-monitor success, failure, retry, and interference tests;
- negative controls that weaken release/acquire or remove a required barrier.

The suite does not reuse x86 expected outcomes. The selected pinned official Arm formal profile is
the expected-set oracle required by `docs/MEMORY_MODEL.md` §5.2. Native observations must be a
subset of that set; absence of an allowed outcome on finite hardware does not forbid it.

### 2.3 Harness Protocol

Two persistent workers execute each test for a configurable iteration budget. The harness design is
itself verified or independently validated and specifies:

- generation-counted start and completion barriers;
- exact reset and result-publication ordering;
- separate cache lines for test locations, control words, and result slots;
- randomized bounded staggering without assuming a particular schedule;
- an external timeout that reports a hang distinctly from a forbidden outcome;
- histogram, seed, architecture profile, CPU/backend, and iteration metadata.

The harness must not assume that a broken synchronization primitive can only hang or produce a
forbidden outcome. Negative controls cover stale-result reuse, accidental worker serialization, and
lost wakeups.

---

## 3. Verified Lock Counter

Two threads each perform a fixed number of increments of a shared counter. The counter and any
ordinary protected state are accessed only through the exclusive capability carried by a successful
lock guard. The portable lock/parking state is a naturally aligned, stable-lifetime 32-bit atomic
word so the same abstract protocol refines to Linux futexes on both architectures.

The architecture-neutral proof establishes:

- at most one live guard owns the protected region;
- failed try-acquire returns no guard and no protected capability;
- successful acquire creates a typed must-release obligation;
- release returns the protected capability to the lock invariant and consumes the obligation;
- after successful joins, the parent reacquires the lock, reads the final count under its guard,
  proves it is the sum of the two thread contributions, and releases the guard;
- the quiescent parent destroys the mutex, revokes every atomic grant, and recovers raw authority
  for the lock word and protected region with no live protocol obligation;
- safety holds for every schedule; progress is a separate theorem under named fairness assumptions.

Target implementations differ:

- **x86-64:** locked exchange or compare/exchange acquisition and a TSO-proven release store;
- **AArch64:** an exclusive-monitor acquisition loop with acquire semantics, and release through
  `STLR` or another sequence proved by the AArch64 model. LSE is outside the v1 profile.

The critical section remains a plain load/add/store sequence so broken exclusion is observable. It
is not replaced by an atomic increment, because that would stop testing capability transfer and
mutual exclusion.

---

## 4. Blocking and Futex Workload

Every hosted mutex variant adds deliberate contention so at least one worker takes the parking slow
path. Linux uses the process-private futex profile in `docs/MEMORY_MODEL.md` §9:

1. user-space atomic state determines whether acquisition can proceed;
2. the waiter calls wait only after observing the contended state;
3. compare-and-enqueue is modeled atomically, preventing a lost wakeup;
4. release publishes protected writes through the architecture-specific atomic protocol;
5. wake makes an eligible waiter runnable but creates no memory-order edge by itself;
6. the waiter loops and rechecks the user-space state after every return.

Before emission, the design gate selects the exact 32-bit mutex values and transitions, waiter
marking, wait expected value, unlock value, wake policy, and retry behavior. The target proof also
orders the release publication before the wake/notification side effect; this prevents a waiter
from re-enqueuing after the only wake without pretending the wake is a memory fence.

Linux acceptance requires evidence that the futex wait and wake paths both executed; a run that
never blocks is a lifecycle/lock test but not a futex validation.

The v1 emitted program uses no timeout and no signal handling. Unsupported futex operations return
an explicit unsupported result rather than receiving invented success semantics.

Windows refines the same scheduler-level parking contract through
`WaitOnAddress`/`WakeByAddress*`, and independently requires evidence that both paths ran under
contention. Both Linux `FUTEX_WAIT` and Windows `WaitOnAddress` comparisons are modeled as
platform-authorized atomic loads of the registered, stable, aligned 32-bit word, with target
single-copy-atomicity evidence; comparison and wake remain non-synchronizing by themselves. Bare
metal uses a proved spin/park adapter and does not pretend to provide futexes.

---

## 5. Target Lifecycle Adapters

### 5.1 Windows x86-64

The Windows implementation models `CreateThread`, thread termination, and
`WaitForSingleObject(INFINITE)` on a thread handle. The model includes runnable/blocked states,
return from the thread start routine, handle lifetime, join result, and per-thread state. A blocking
wait is a scheduler transition, not a synchronous function over one CPU state.

Mutex contention is a separate live-thread workload using `WaitOnAddress` and
`WakeByAddressSingle`/`WakeByAddressAll` over the selected 32-bit parked-mutex state machine. It
must demonstrate both wait and wake paths and recheck the atomic state after every return; a
thread-handle join does not count as mutex parking. Explicit start/terminal release-acquire words
provide lifecycle visibility unless a later pinned Windows profile proves an equivalent API edge.

### 5.2 Linux x86-64 and AArch64

The Linux implementation models raw thread creation, per-thread stacks, thread-local syscall state,
thread exit distinct from process exit, and a real join using child-TID clear-and-wake lifecycle
semantics. The stable, naturally aligned 32-bit child-TID word remains registered atomic through
join; every concurrent kernel set/clear is a platform-authorized atomic store with x86-64 or
AArch64 single-copy-atomicity evidence, and parent polling uses approved atomic loads. Explicit
target release/acquire start and terminal publication words provide memory visibility; child-TID
lifecycle establishes actual termination and safe stack reclamation. A user-space done flag alone
is neither half of that full join contract.

Linux futex constants and syscall ABIs are architecture-specific while wait-queue behavior is shared.

### 5.3 x86-64 Bare Metal

The x86 path performs AP startup, per-CPU stack setup, rendezvous, and generic scheduler entry. The
design gate decides the real/protected/long-mode trampoline, LAPIC interface, UC/device ordering, and
APIC-ID mapping before implementation. INIT/SIPI creates lifecycle state; work and authority are
published through a separate TSO-proved boot-mailbox rendezvous.

### 5.4 AArch64 Bare Metal

The AArch64 path starts secondary PEs through the selected PSCI/spin-table platform contract,
allocates per-PE stacks, maps `MPIDR_EL1` identities to `ThreadId`, establishes coherent shareable
memory, and enters the same generic scheduler. GIC, `WFE`/`SEV`, and Device-memory ordering are
designed explicitly when required. PSCI/spin-table release and `SEV` are lifecycle/notification,
not RAM synchronization; the boot mailbox uses a proved AArch64 release/acquire handoff.

The two bare-metal paths share lifecycle and lock specifications, not boot mechanisms.

---

## 6. Causal Trace Contract

The concurrent trace is a labelled partial order over stable origin-local event identities. It
projects program happens-before generated by:

- same-thread program order;
- parent-to-child spawn;
- child-to-parent successful join;
- release-to-acquire when the acquire observes the relevant release through the architecture model.

It also retains scheduler-causality edges such as wake-to-resume under a different label. Plain
reads-from and futex wake are not automatically memory synchronizes-with. ISA execution consistency
remains richer than the observable trace order and is validated by the litmus model rather than
encoded as vector-clock edges.

Equivalence is independent of arbitrary scheduler linearization. An explicit quotient maps every
raw observable to exactly one canonical node, invents none, and merges nodes only under the named
per-effect coalescing rules while preserving stream, label, payload fold, and barriers. Between
distinct quotient nodes, an observable labelled edge appears if and only if it is in the projected
program/scheduler causal order, modulo event-key renaming and partial-order isomorphism.

---

## 7. Output and Verdict Protocol

Stdout contains deterministic, quantized verdicts; nondeterministic histograms and environment
metadata go to stderr or a structured artifact. The precise target set is encoded in the runner, but
the logical shape is:

```text
SPIKE8 <arch> LITMUS forbidden=0 validation=<validated|not-validated>
SPIKE8 <arch> LOCKCOUNT value=<actual> expected=<expected>
SPIKE8 <platform> PARK wait=<observed> wake=<observed>
SPIKE8 <target> PASS
```

Exit status classes distinguish:

- pass with all required validation controls;
- semantic failure: forbidden outcome, wrong counter, invalid lifecycle, or proof mismatch;
- environment could not validate a required weak-memory witness;
- timeout/deadlock;
- unsupported requested profile.

A per-commit run is not required to witness every rare allowed outcome. Witness floors belong in a
scheduled stress lane with recorded hardware eligibility; per-commit CI still rejects every observed
forbidden outcome.

---

## 8. Acceptance Criteria

Spike 8 is complete only when:

1. the common event vocabulary and both architecture models are connected to instruction semantics,
   and emitted program bytes decode back to those instructions with relocation/layout fidelity;
2. x86 and AArch64 model-derived litmus theorems pass;
3. native hosted runs observe only model-allowed outcomes;
4. the lock invariant, capability transfer, must-release obligation, and final counter theorem are
   proved once at the common contract and discharged by both architectures;
5. Linux x86-64 and AArch64 execute and validate the futex slow path;
6. Windows validates its lifecycle and parking refinement;
7. x86 and AArch64 bare-metal targets start at least two CPUs/PEs, prove the boot-mailbox handoff,
   run the lock counter, refine their selected wait strategy, and validate one device
   order/completion protocol with a barrier/attribute negative control;
8. the causal trace node quotient is total/non-inventing and its labelled edge order is connected in
   both directions to projected program and scheduler causality;
9. negative controls fail for missing barriers, broken atomicity, unauthorized access, stale harness
   results, lost wakeups, omitted obligation discharge, and lock destruction with a stale atomic
   grant or waiter;
10. every run records enough environment information to distinguish silicon validation from emulator
    execution.

The implementation order is `docs/MEMORY_MODEL.md` §14. This spike does not maintain a parallel task
DAG.

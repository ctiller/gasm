# Memory, Concurrency, Ownership, and Synchronization Model

**Status:** canonical cross-architecture design and implementation roadmap. The repository
currently implements only the single-threaded pieces identified in §2. Everything else is a
requirement, not a claim about existing Lean declarations.

This document supersedes the retired x86-only memory-model and borrowing plans and owns the
architecture shared by Spike 8. Target documents own
instruction encodings and platform details; this document owns how their memory, concurrency,
ownership, and synchronization semantics fit together.

The design has one central rule:

> Ownership transfer and synchronization have one architecture-neutral contract, but each ISA
> and execution environment must separately prove that its instructions and services implement
> that contract.

Consequently, x86 TSO is not the generic memory model, AArch64 is not implemented as “TSO plus
more fences,” Linux futexes are not treated as memory barriers, and bare-metal SMP is not treated
as an operating-system thread API.

---

## 1. Goals, Guarantees, and Scope

The completed system must provide all of the following:

1. **Architecture-correct concurrent execution:** x86-64 TSO and AArch64 weak-memory behavior,
   including the atomic and barrier instructions used by real synchronization code.
2. **Capability-enforced memory safety:** every dynamic access is covered by a provenanced,
   in-bounds authority; conflicting ordinary accesses cannot be authorized concurrently.
3. **Cross-thread ownership transfer:** spawn, join, successful lock acquisition, and lock release
   move capabilities rather than copying them.
4. **Lock invariants and linear cleanup:** a lock word can guard a different region; successful
   acquisition creates a guard and a must-release obligation, and release consumes both.
5. **Blocking synchronization:** Linux futex wait/wake, Windows waiting, and bare-metal parking
   refine a common scheduler-level parking contract without pretending they have identical APIs.
6. **Two bare-metal SMP stories:** x86 application-processor bring-up and AArch64 processing-
   element bring-up satisfy one lifecycle contract through architecture-specific mechanisms.
7. **Honest causal traces:** effect traces faithfully project labelled program happens-before and
   scheduler causality without conflating them; vector clocks do not stand in for an ISA
   memory-consistency model.
8. **Differential validation:** bounded model outcomes, emitted binaries, native silicon, and
   architecture-appropriate negative controls remain linked.

The first supported concurrent profile is deliberately bounded:

- naturally aligned 32-bit and 64-bit shared words;
- cacheable normal memory (x86 WB; AArch64 Normal, coherent, shareable memory);
- no mixed-size atomic overlap, self-modifying code, persistent memory, or non-temporal access;
- explicit Device/MMIO operations, kept out of ordinary RAM reasoning;
- process-private futex wait/wake first, with other futex operations deferred explicitly;
- two-thread litmus and lock programs first, with the model itself parameterized by thread count.

These restrictions are acceptance boundaries, not silent assumptions. Widening any one requires a
new validation demand and an update here before implementation.

---

## 2. Verified Current Baseline

As of 2026-08-28, the tree has the following relevant machinery:

| Area | Present | Missing |
|---|---|---|
| x86-64 memory | Sealed byte memory, width-indexed access API, mandatory per-instruction `memAccesses`, frame lemmas | Atomic memory forms, fences, store buffers, concurrent machine |
| AArch64 memory | Sealed byte memory and an `AArch64MemAccessSpec` vocabulary | The descriptor is not a field of `AArch64Instruction`; no atomic order, barriers, exclusives, or concurrent machine |
| Capabilities | `PermissionShare`, `MemoryPerm`, `MemoryPermissions` | Enforcement at instruction construction, provenanced pointer authoring, temporal loans, cross-thread transfer |
| Obligations | Generic `ObligationToken` list and return/exit predicates | Typed lock/join/wait obligations and an index that prevents forged ledger replacement |
| Indexed programs | `BlockM Arch S₁ S₂ α` with indexed bind | A borrow/obligation index used by assembly programs; safe constructors that prevent arbitrary state replacement |
| Causality | `ThreadId`, vector clocks, `CausalEvent`, single-thread stamping | Concurrent execution graph, correct synchronizes-with generation, multi-thread trace projection |
| OS threads | Single-state Win32 and Linux hooks | Runnable/blocked thread state, clone/CreateThread lifecycle, joins, futexes, wait queues |
| Bare metal | Single-CPU x86 and AArch64 execution paths | SMP bring-up, coherent shared-memory assumptions, interrupt/wakeup model, per-CPU/PE state |

No concurrency theorem may be presented as implemented until it is stated against a machine with
at least two threads or processing elements. A single-thread ordering theorem cannot validate a
concurrent memory model.

---

## 3. Layering and Ownership of Semantics

The implementation is divided into linked semantic surfaces:

```mermaid
flowchart TD
    A[Provenance and authority<br/>regions, bounds, borrows] --> E[Dynamic memory events<br/>access, order, domain, identity]
    I[Instruction semantics<br/>x86-64 or AArch64] --> E
    E --> M[ISA consistency model<br/>x86 TSO or AArch64]
    T[Thread and scheduler machine<br/>run, block, wake, spawn, join] --> M
    A --> S[Synchronization contracts<br/>atomics, locks, guards, obligations]
    M --> S
    T --> S
    S --> P[Platform refinements<br/>Windows, Linux futex, bare metal]
    M --> C[Causal trace projection<br/>labelled program and scheduler causality]
    S --> C
```

The connection theorems between layers are mandatory:

- every program-origin memory event comes from an instruction descriptor and actual instruction
  step; initial, platform, and device events come from their corresponding initialization or
  transition rule and cannot masquerade as program instructions;
- every program event is covered by the executing thread's current authority; platform and device
  events use explicitly scoped environment/device authority, while initial events satisfy the
  initialization invariant;
- every architecture-specific execution admitted by the interpreter satisfies that ISA’s
  consistency predicate;
- every emitted synchronization instruction decodes to the modeled instruction, and program
  emission preserves relocation targets, layout, and the instruction stream used by the proof;
- the remaining model-to-hardware semantics boundary is recorded as a cited TCB assumption and
  challenged by architecture-appropriate differential tests;
- every claimed synchronizes-with edge is backed by the atomic read-from or lifecycle event that
  creates it;
- every observable causal edge is backed by the corresponding labelled program-happens-before or
  scheduler-causality edge, and every projected source edge is retained;
- every platform wait/wake operation refines the scheduler parking contract.

Without these the layers are parallel descriptions, not a verified system.

---

## 4. Common Dynamic Memory-Event Vocabulary

Static instruction descriptors remain target-specific where addressing demands it: x86 SIB
operands and AArch64 pre/post-indexed operands should not be forced into one operand type. They
must, however, instantiate one dynamic event vocabulary after effective addresses are known.

An implementation should carry information equivalent to:

```lean
inductive AccessRole where
  | read
  | write
  | readWrite

inductive AccessClass where
  | plain
  | atomicLoad
  | atomicStore
  | atomicRmw      (succeeded : Option Bool) -- none for an unconditional RMW
  | exclusiveRead  (reservation : ReservationId)
  | exclusiveWrite (reservation : ReservationId) (succeeded : Bool)

inductive MemoryOrder where
  | relaxed
  | acquire
  | release
  | acquireRelease
  | seqCst

inductive MemoryDomain where
  | normal
  | device
  | portIO

inductive EventKey where
  | thread   (thread : ThreadId) (sequence : LocalSequence)
  | platform (instance : PlatformInstanceId) (sequence : LocalSequence)
  | device   (instance : DeviceInstanceId) (sequence : LocalSequence)
  | initial  (range : AddressRange)

inductive EventOrigin where
  | instruction (descriptor : StaticAccessId)
  | platform    (transition : PlatformTransitionId)
  | device      (transition : DeviceTransitionId)
  | initial

structure MemoryEvent where
  key           : EventKey
  origin        : EventOrigin
  range         : AddressRange
  role          : AccessRole
  accessClass   : AccessClass
  explicitOrder : Option MemoryOrder
  domain        : MemoryDomain
  targetAttrs   : TargetMemoryAttributes
  readValue     : Option ByteVector
  writeValue    : Option ByteVector
```

Only well-formed events enter a graph. `MemoryEvent.WellFormed` or indexed constructors enforce at
least: role/value presence and absence; value width equals range width; failed
`atomicRmw (some false)` and failed exclusive stores have no write value, while unconditional or
successful RMW/store-exclusive actions do; order is valid for the access class (for example no release-only load or
acquire-only store); target width/alignment and single-copy-atomicity premises hold; the domain
agrees with the target memory attributes; and origin agrees with the key form. Target projections
prove their additional constraints.
The orthogonal fields are an interchange vocabulary, not permission to construct malformed
combinations.

`explicitOrder = none` means an ordinary ISA access, not a relaxed atomic. A protocol proof may show
that an ordinary x86 store implements the release half of a particular lock; that derived
synchronization role does not relabel every ordinary store as an ISA release operation. Value fields
are width-indexed byte strings (or an equivalent representation) so value consistency, CAS results,
exclusive-store success, forwarding, and litmus final states are expressible.

The concrete spelling is an implementation decision; the information content is not. Barrier
events are separate from accesses because a barrier orders events but does not access a fake empty
range. A normalized barrier records its target kind, before/after access classes, memory domain,
shareability/scope, whether it imposes ordering or completion, and whether it synchronizes the
instruction stream. Architecture-specific semantics interpret those fields; they are not collapsed
into one architecture-neutral notion of “full fence.”

Protocol synchronization is a proof-produced layer over concrete event keys, not another ISA order
tag. A `SyncWitness` (or equivalent) names the protocol/lock instance and generation, the release
key, the acquire-observation key, any distinct success-linearization key (for example AArch64's
load-exclusive plus successful store-exclusive), the relevant reads-from/value or RMW relation, and
the target-specific proof that those events implement release/acquire. It is the canonical source of a
synchronizes-with edge. Thus an x86 `MOV` unlock may have `explicitOrder = none` while one proved
protocol use is a release; unrelated stores are not relabelled, and a failed compare/exchange or
store-exclusive creates no witness.

An execution graph contains at least:

- per-thread program order (`po`);
- syscall/API invocation-to-platform-transition, ordered platform subevent, block/resume, and
  return-to-thread edges;
- byte/range-granular reads-from (`rf`) for Normal memory, relating each returned byte to a write
  byte;
- per-location Normal-memory coherence/modification order (`co`), with an explicit initial write
  for every modeled Normal location;
- Normal-memory from-read (`fr`), derived where appropriate;
- address, data, and control dependencies needed by the target model;
- barrier-order edges;
- atomic-RMW and exclusive-pair/reservation relations where the target requires them;
- lifecycle events such as spawn and join;
- target device-transition/value relations for Device and port-I/O events, including destructive
  reads, request/completion, and device-local order, without inventing Normal-memory initial writes
  or coherence edges.

Origin and domain are orthogonal: for example, every concurrent kernel child-TID set/clear in the
pinned clone profile is a platform-origin `atomicStore` to a registered, stable, aligned 32-bit
Normal-memory object. It participates in the same `rf`/`co` relations and requires the target's
single-copy-atomicity proof; it is not an unclassified write that bypasses the atomic/plain mode
invariant. An MMIO register access instead uses the device relation. Invocation/return and device
request/completion edges keep those events linked to the program that caused or observed them,
making release-before-notify and API refinement statable in the graph.

The graph's `rf` relation, not a duplicate single-source field in `MemoryEvent`, is authoritative.
Byte/range granularity permits a read to be assembled from multiple writes and avoids baking a
same-width assumption into the common interface even though the first executable profiles defer
mixed-size races. Program keys are thread-local, platform/device keys are local to their stable
instance, and initial keys are structural; graph and trace equality must not depend on a global
allocation order. Logical `ThreadId` values are generative and never reused within an execution or
trace; platform TIDs, handles, APIC IDs, and MPIDR values map to the current logical instance but are
not program-event or vector-clock identities.

The event graph is the common proof-facing representation. Each ISA may use the executable model
best suited to it, provided connection theorems relate that model to this graph.

---

## 5. Architecture-Specific Consistency Models

### 5.1 x86-64: TSO for Write-Back Memory

The first x86 model is an operational TSO machine over WB memory. Before M2-X, the profile must pin
whether it is Intel-64-only or the cited common subset of Intel 64 and AMD64. A CPU outside that
source-backed vendor/profile set may run functional controls but reports memory-model validation as
`not-validated`.

- each x86 execution agent owns a FIFO store buffer;
- a plain store enters that buffer;
- an approved naturally aligned non-locked atomic load/store follows the same operational
  load/forwarding or store-buffer transition as its underlying `MOV`; `AccessClass.atomicLoad` or
  `.atomicStore` changes its authority and single-copy-atomicity contract, not its TSO queue order;
- a load forwards from the youngest same-range or covering supported store in its own buffer,
  otherwise reading shared memory; partial-overlap composition is deferred from the first x86
  executable profile but remains representable in the common graph;
- a model-internal drain publishes the oldest buffered store;
- locked RMW operations drain prior stores and execute as indivisible globally ordered actions;
- `MFENCE` has its architectural full load/store ordering contract; an implementation may realize
  that contract by draining prior stores and preventing later loads and stores from crossing it;
- naturally aligned supported-width ordinary accesses are untearable as required by the selected
  x86 profile.

The portable parked-mutex state is a naturally aligned 32-bit word because Linux futexes operate on
32-bit words on every supported architecture. The initial x86 instruction demand therefore includes
memory `XCHG r/m32` (implicitly locked), `LOCK CMPXCHG r/m32` (plus any 64-bit forms independently
demanded), `MFENCE`, and optionally `PAUSE`. Release of a simple x86 mutex may use an approved
aligned `MOV` atomic-object store only when the x86 model proves the required
prior-write-before-release visibility.

UC/WC/MMIO ordering is not folded into WB TSO. LAPIC accesses and other devices use the device
model in §10 and force an explicitly cited x86 memory-type extension.

Required x86 connection theorems:

1. one-thread, drained executions agree observationally with the existing sequential interpreter;
2. an atomic descriptor corresponds to one indivisible dynamic action;
3. every admitted operational execution satisfies the x86 execution-graph consistency predicate;
4. bounded graph-consistent executions are represented by the operational enumerator (adequacy),
   so the two views have equal observable litmus outcomes rather than only one-way soundness;
5. the model-derived outcome sets for the x86 litmus suite match the stated TSO profile.

### 5.2 AArch64: Weak Memory, Acquire/Release, and Exclusives

AArch64 gets a separate consistency model sourced from a pinned Arm Architecture Reference Manual
profile and its matching official `cat`/herd7 material. The pinned formal model is the exact outcome
oracle; native hardware observations test that implementations produce only allowed outcomes, but
cannot establish the entire allowed set. AArch64 must not inherit x86 ordering defaults.

The first supported instruction and semantic surface includes:

- ordinary `LDR`/`STR` as plain weakly ordered accesses, not relaxed atomics;
- `LDAR`/`STLR` acquire and release accesses;
- `LDXR`/`STXR` and acquire/release variants as an exclusive-monitor protocol;
- `CLREX` as an explicit monitor-clearing transition;
- `DMB` with the scopes needed for shareable RAM and device interaction;
- `DSB` and `ISB` where device bring-up or system-register sequencing demands them;
- `WFE`/`SEV` for the bare-metal parking adapter, without treating either as a RAM fence.

Per-PE state includes a local reservation plus an abstraction of the architecture's local/global
exclusive monitors and reservation granule. An exclusive store is conditional: it writes only if
the monitor permits it and returns success/failure in the architectural status register. Conflicting
writes, `CLREX`, and modeled lifecycle/exception transitions invalidate monitor state as required by
the selected profile; permitted spurious `STXR` failure is represented. A successful `STXR`/`STLXR`,
not the preceding load-exclusive, is the lock-acquisition linearization point. Any eventual-success
claim needs a separately named fairness/progress assumption. An exclusive pair is therefore not
encoded as one indivisible `.atomicRmw` descriptor.

The v1 model covers aligned 32-bit and 64-bit operations in coherent shareable Normal memory. LSE
atomics, RCpc forms, mixed-size overlap, and non-shareable memory remain deferred until a consumer
requires them.

Required AArch64 connection theorems mirror x86 but are architecture-specific:

1. one-PE executions preserve the current sequential instruction semantics where ordering is
   unobservable;
2. exclusive-monitor success and failure correspond to the emitted event sequence;
3. acquire, release, and barrier descriptors are faithful to dynamic ordering behavior;
4. every admitted execution satisfies the chosen AArch64 consistency predicate;
5. every bounded execution consistent with the pinned Arm predicate is represented by the
   executable enumerator (adequacy), so it cannot pass by silently excluding allowed executions;
6. bounded outcome sets equal those of the pinned formal Arm profile, including but not limited to
   the named litmus suite, and every native observation is contained in that set.

### 5.3 What Is Shared and What Is Not

Shared:

- event identities and graph relations;
- provenance and authority;
- lock, guard, and obligation contracts;
- scheduler lifecycle and parking contracts;
- validation protocol and causal-trace projection.

Architecture-specific:

- allowed execution graphs;
- instruction encodings and static addressing descriptors;
- store-buffer versus exclusive-monitor state;
- fence/barrier semantics and scope;
- normal/device memory attributes;
- bare-metal CPU/PE bring-up.

---

## 6. Provenance, Borrowing, and Cross-Thread Authority

Memory ordering cannot repair an unauthorized or out-of-bounds access. Authority is checked before
the architecture consistency model is consulted.

### 6.1 Regions and Provenanced Pointers

Every allocatable region has a fresh, generative `RegionId`; identity is not derived solely from its
address because an address may be freed and reused. A pointer preserves its region identity while
offsetting. Constructing a pointer from an arbitrary integer is unavailable to ordinary assembly
authors. Dereference requires:

- a pointer into the named region;
- a proof that the dynamic range is in bounds and non-wrapping;
- authority for the requested access kind;
- any alignment and stable-address properties required by atomics, futexes, or devices.

External memory enters through explicit environment grants at loader, allocator, syscall, or device
boundaries. A grant is a reviewed trust boundary, not a general unchecked cast.

#### 6.1.1 Pointer-valued memory (v1 boundary)

Stored bytes do not carry provenance. Loading an address-sized integer never manufactures a
`ProvenancedPtr` or authority. A v1 program may store address bytes, but it may later dereference
that value only through a registered typed view whose ghost slot map still associates the field
with a live `RegionId`; moving or swapping the field must move that slot binding as well. Pointee
authority remains in the indexed context and is never reconstructed from bytes. Arbitrary external
bytes remain integers until an explicit boundary grant validates and associates them with a live
region.

Generic recursive or existential heap structures that recover ownership-carrying pointers are
outside v1. A consumer such as the line-sort descriptor table must use a purpose-built typed view
and prove preservation of its slot map, or wait for that later extension.

### 6.2 Authority States

The canonical authority algebra distinguishes:

- `Exclusive`: one context may read or write ordinary memory;
- `SharedRead`: one or more contexts may read and none may write;
- `Atomic`: contexts may access a specifically declared atomic object, but only with supported
  atomic operations.

`Atomic` is not authority to mutate an entire mutex-protected region. The lock word has atomic
authority; the protected region moves as exclusive authority to the successful acquirer.

This is a resource algebra, not a pairwise-disjoint list. Spatial composition requires disjoint
regions, while same-region composition permits identified shared-read leases and separately
shareable atomic-object authority. Atomic grants are instance- and generation-scoped leases under
an authoritative object record, not timeless facts derivable from an address. An exclusive owner
that lends reads is represented by a frozen owner fragment plus unique `LoanId -> holder` records;
a scalar reader count cannot prove which borrower returned which loan. Reclaim consumes the exact
matching loan token, and exclusive authority is restored if and only if the loan map becomes empty.
The borrower carries `MustReturnLoan loan issuer holder region`, or an equivalent result-indexed
terminal promise, so return and thread exit cannot lose a live loan.

Temporal borrowing is tracked in the indexed program type, not by duplicable capability values:

- lending a read suspends exclusive writes until all read loans are reclaimed;
- donation removes authority from the donor and installs it in the recipient in one modeled causal
  handoff: spawn, successful join, lock transfer, or a specified linear channel. V1 does not permit
  an unsynchronized write into an already-running thread's authority context;
- splitting a region suspends/consumes overlapping parent access authority and produces disjoint
  child authorities plus their obligations. Rejoin consumes the exact complete sibling set, with
  no outstanding descendant, loan, or typed view, before restoring parent authority;
- transmogrification creates a typed view only from a proof and carries a destruction/discharge
  obligation before the underlying raw authority returns.

The current `PermissionShare.Locked` constructor is compatibility vocabulary, not the final lock
model. Migration should separate atomic-object authority from protected-region ownership.

### 6.3 Global Cross-Thread Invariant

For every concrete byte range, the family of thread authority contexts satisfies a global access-
mode invariant:

- at most one context has ordinary write authority;
- if one context has ordinary write authority, no other context has read or write authority;
- multiple read authorities may coexist;
- a registered atomic object admits only its supported atomic accesses: atomic authority may overlap
  on that declared region, but no ordinary read or write authority may coexist until the object is
  unregistered and every atomic grant is consumed.

From this invariant and descriptor fidelity, prove that two authorized conflicting ordinary
accesses from distinct threads cannot occur and that a registered atomic object cannot be accessed
through a plain instruction. Atomic accesses are not waved away as “synchronized”; their safety and
ordering are discharged by the atomic-object and architecture models.

### 6.4 Spawn, Join, and Termination

Spawn accepts an explicit capability partition. Donated regions disappear from the parent before
the child can become runnable—even on a platform where the child may execute before the spawn API
returns. A failed spawn restores the pre-spawn partition; success commits it exactly once.
Shared-read and atomic grants may be installed in both contexts only when the global invariant
permits them.

Successful spawn creates a fresh logical `ChildInstanceId` and, for a joinable child, one unique
`JoinRight` carrying the child's result-indexed terminal contract. Neither identity is an OS thread
ID, child-TID address, reusable handle value, or raw `ThreadId`. Timeout, failed wait, or
observation-only wait preserves the right. Successful logical join consumes it exactly once and
returns only the sealed terminal bundle promised by the child's postcondition; it does not
manufacture every capability originally donated. Platform handles and their close obligations are
separate observation resources.

Every thread terminal transition seals a bundle that accounts for its entire resource context:
each authority, loan, atomic grant, guard, and obligation is returned, donated through a specified
handoff, discharged by its contract, or transferred to an explicitly named process-owned sink. An
obligation-free exclusive capability left in a dead thread is still invalid. Detach consumes a
`JoinRight` only when the child contract returns no join-owned linear resource, or atomically
redirects the declared terminal bundle to a process-owned sink. Process termination is separate,
checks every thread context and sealed terminal bundle, and may discharge only resources explicitly
declared process-scoped.

Spawn and join contribute program-happens-before only through a proved lifecycle-visibility
refinement. Parent-to-child spawn must make the promised pre-spawn writes visible before the child
uses donated authority; child-to-parent join must make the terminal bundle's promised writes visible
after successful join. A runnable/signaled state, child-TID clear, or wake event alone is not that
proof. Each platform adapter must cite an API/architecture guarantee that provides the edge or use an
explicit release/acquire publication word alongside its lifecycle mechanism.

---

## 7. Lock Invariants and Unlock Obligations

A v1 mutex is nonrecursive and connects disjoint atomic lock region `w` and protected region `p`.
Initialization consumes raw exclusive authority for both regions, checks/establishes the physical
unlocked representation, registers `w` as an atomic object, and creates a fresh `LockInstanceId`.
That instance identity is distinct from the fresh acquisition generation created on every success:

```lean
structure LockInv (instance : LockInstanceId) (w p : RegionId) where
  -- When unlocked, the invariant owns p.
  -- When locked, exactly one live guard owns p.
  invariant : LockStateRelation w p
```

The lock’s physical value does not by itself prove ownership. The ghost invariant relates the
physical protocol state, current owner identity and acquisition generation, protected authority,
wait state, and lifecycle. Contenders share atomic authority only for `w`; mixed atomic/plain access
to `w` is rejected. The invariant owns `p` while available, and exactly one live guard owns `p`
while held.

### 7.1 Acquire

Try-acquire has a result-dependent postcondition:

- failure leaves authority and obligations unchanged;
- success at the target's acquisition linearization point atomically creates a
  `LockGuard lock thread generation protected`, transfers exclusive authority for the protected
  region to that guard, and adds a matching `MustRelease lock thread generation`.

A blocking acquire returns only the success case but carries a liveness theorem conditional on the
scheduler, wakeup, and fairness assumptions. Mutual exclusion is a safety theorem and does not
depend on fairness.

An acquire synchronizes with the particular prior release it observes only when the architecture
model proves the required release/acquire relation. The proof cannot be generated merely because
both events mention the same address.

### 7.2 Release

Release requires the current thread’s instance- and generation-matched guard, protected-region
authority, and must-release obligation. At the target's physical release linearization point it
atomically returns the capability to the lock invariant and consumes the guard and obligation. It
also proves prior protected writes become visible before another acquire can receive the capability;
the ghost transfer may not occur before or after an unrelated physical event.

Target realizations differ:

- x86 may use locked acquire/CAS plus an aligned `MOV` release store under the TSO proof. On a
  registered atomic word that approved authoring operation emits `AccessClass.atomicStore` with
  `explicitOrder = none`; it is not authorized or modeled as a `.plain` access, even though the
  machine instruction is an ordinary `MOV`;
- AArch64 uses an acquire-capable load/exclusive sequence and `STLR` or a proven barrier sequence
  for release.

### 7.3 Typed Obligations

The obligation model must replace string-only protocol knowledge with typed resources including:

- `MustRelease lock owner generation`;
- `MustJoin child` or explicit detachment;
- `MustUnregisterWait queueEntry`;
- `MustKeepAliveWhileWaiters region`;
- existing allocation/view destruction and OS-resource obligations.

Acquire, release, wait, wake, join, cancellation, and termination update the obligation index through
safe constructors. A general operation capable of replacing `ComposedState.perms` or
`.obligations` arbitrarily is outside the checked authoring surface.

Scheduler-owned wait registrations are distinct from author-visible linear obligations: a blocked
thread cannot unregister itself. Wake, timeout, supported interruption/cancellation, and thread exit
must remove them through scheduler transitions. Mutex destruction requires authoritative lifecycle
control, an unlocked state, and proof that no guard, waiter, in-flight access, reservation, or
scheduler registration remains. It revokes and consumes every instance-scoped atomic grant,
consumes the `LockInv` and `LockInstanceId`, invalidates stale handles by generation, and returns raw
exclusive authority for both `w` and `p`. The 32-bit lock/parking word has stable lifetime until that
transition completes. Forced thread termination while holding a guard is unsupported in v1 rather
than silently discarding the guard or poisoning the invariant.

---

## 8. Thread Machine and Scheduler

The concurrent machine separates process-shared and per-thread state:

```text
ProcessState
  shared normal memory
  device and OS state
  thread table
  wait queues
  handles and lifecycle records

ThreadState tid
  registers, flags/status, PC/SP
  runnable | blocked reason | terminated result
  authority/obligation context

ExecutionAgentState agentId
  running : Option ThreadId
  x86: store buffer and required logical-processor-local state
  AArch64: local/global exclusive-monitor abstraction and required PE-local state

SchedulerMapping
  logical thread <-> current execution agent / not running
```

Architecture-local state belongs to the execution agent, not to a migratable logical thread. An
AArch64 reservation is never copied to another PE; descheduling, migration, exception transitions,
and explicit `CLREX` invalidate it as required by the pinned profile. An x86 store buffer remains
with its logical processor and may drain according to the TSO machine rather than migrating inside
`ThreadState`. The scheduler/platform connection theorem accounts for these transitions; a bounded
profile may pin threads to agents only if that restriction is explicit in both the model and runner.

A global step chooses one of:

- a runnable thread instruction on its assigned execution agent;
- an architecture-internal propagation/drain action;
- a kernel/API transition such as block, wake, spawn, terminate, join, context switch, or migration;
- a modeled device transition.

Scheduling nondeterminism is universally quantified in safety theorems. Progress theorems state
their fairness hypotheses explicitly. Fuel-bounded execution remains a test runner, not a proof of
termination or absence of deadlock.

---

## 9. Linux Futexes and Platform Parking

Parking is separate from memory ordering:

```text
park-if-equal(key, expected) -> blocked | value-changed | error
wake(key, maximum)           -> number-woken
```

The mutex slow path consumes one selected 32-bit abstract state machine (§15): its fast and slow
transitions, waiter mark, exact expected value passed to wait, unlock value, wake policy, and retry
loop are part of the proof. The generic parking API does not choose or silently repair that protocol.

The first Linux refinement supports process-private `FUTEX_WAIT` and `FUTEX_WAKE` operations. It
must model:

- a naturally aligned, mapped 32-bit futex word with stable lifetime;
- an atomic value check and waiter enqueue, preventing the lost-wakeup window;
- `EAGAIN` when the observed value differs from `expected`;
- queues keyed by address-space identity and address;
- waking at most the requested number of eligible waiters, with nondeterministic selection;
- the syscall return value and runnable/blocked transition;
- permitted wake/return without acquiring the user-space state, which is why the caller must
  recheck in a loop;
- removal of wait registrations on wake, supported cancellation, or thread exit;
- a caller loop that rechecks the user-space atomic state after every return.

Every park-if-equal adapter comparison is a well-formed `atomicLoad` of the registered, stable,
aligned 32-bit object under scoped platform authority. This includes the Linux `FUTEX_WAIT`
comparison and the selected Windows `WaitOnAddress` refinement. Each target proves the operation's
single-copy atomicity and value comparison; neither comparison is a hidden plain access that
bypasses §6.3, and neither creates memory synchronization by itself.

The v1 profile may require a null timeout and no signal model, returning an explicit unsupported
result for other operations rather than inventing semantics. Timed waits, shared futexes, requeue,
PI futexes, robust lists, and signal interruption are follow-on profiles.

`FUTEX_WAKE` is not a release fence and waking is not, by itself, a synchronizes-with edge. The
user-space atomic protocol performs release/acquire publication; futex supplies blocking and
wakeup. Wake-to-resume is a scheduler-causality edge, not a memory synchronizes-with edge. The lock
proof composes the two. It must nevertheless prove that the lock-state release publication is
ordered before the notification side effect (`FUTEX_WAKE`, `WakeByAddress*`, `SEV`, or IPI), adding
a target barrier when required. That ordering prevents a resumed waiter from re-enqueuing after the
only wake; it is a lost-wakeup theorem, not a claim that wake itself publishes protected data.

### 9.1 Linux Thread Exit and Join

The first real Linux join uses child-TID lifecycle semantics: thread creation registers a stable,
naturally aligned 32-bit child-TID word as an atomic object; actual child exit clears it and wakes
waiters; and the parent waits in a loop through the futex adapter using only approved atomic loads.
Every concurrent kernel set/clear selected by the pinned clone flags is a platform-authorized
`atomicStore` with the x86-64 or AArch64 single-copy-atomicity proof. A child-written ordinary done
flag is only a completion handoff; it does not prove the child has terminated or that its stack can
be reclaimed. Thread exit is distinct from process exit, and stack/TID storage and their atomic
registration remain live until join has completed and the registration can be revoked safely.

Child-TID clear/wake establishes lifecycle observation, not by itself the user-memory visibility
edge required by §6.4. The v1 Linux adapter therefore uses a target-specific release/acquire start
publication around child entry and a child-release/parent-acquire terminal publication in addition
to child-TID lifecycle join. Logical join completes only when both termination and visibility
conditions hold.

The precise clone flags, syscall ABI, error results, and child-TID clear/wake behavior must be
ingested from the Linux ABI before the adapter is implemented.

### 9.2 Windows Lifecycle and Parking

The Windows refinement models these facts explicitly:

- successful thread creation may make the child runnable before the API returns, so authority is
  partitioned before that transition; failure restores it;
- returning from a start routine and `ExitThread` terminate one thread, while `ExitProcess`
  terminates the process;
- a thread object becomes signaled at termination, but waiting for it, owning a join right, and
  closing its handle are separate protocol transitions and obligations;
- waits have success, timeout, and failure outcomes, and handle lifetime is preserved while a wait
  is pending;
- per-thread OS state such as last-error values lives in `ThreadState`, not process-global state;
- the v1 mutex slow path uses `WaitOnAddress` plus `WakeByAddressSingle`/`WakeByAddressAll` over the
  stable 32-bit lock word; early returns and races are handled by always rechecking the user-space
  atomic state;
- thread-object signaling/waiting supplies lifecycle observation. The v1 adapter also uses explicit
  target-specific release/acquire start and terminal publication words; a later profile may remove
  them only after pinned Microsoft guarantees prove the same §6.4 visibility contract.

Bare metal has no futex or Win32 wait API: its parking adapter may begin with a proved
spin/`PAUSE` or spin/`WFE` loop and later use interrupts/IPIs, while preserving the same lock
contract.

---

## 10. Bare-Metal SMP and Device Memory

The shared bare-metal contract is small:

- discover or start a finite set of processing elements;
- assign each a unique `ThreadId` and per-CPU/PE stack;
- establish coherent shared Normal/WB memory before publishing work;
- bring secondaries through a rendezvous into the generic scheduler;
- provide park/wake and termination behavior;
- model device accesses as explicit device events with required ordering.

The selected x86 spin/`PAUSE` or interrupt strategy and AArch64 spin/`WFE`/interrupt strategy must
refine the generic wait contract explicitly. A spinning implementation may refine blocking only as
named stuttering steps; a notification optimization cannot be credited with RAM ordering.

INIT/SIPI, PSCI `CPU_ON`, spin-table release, `WFE`, and `SEV` are lifecycle or notification
mechanisms, not RAM synchronization. Publishing a boot mailbox and donated authority requires a
proved target-specific release/acquire rendezvous before the secondary consumes either.

### 10.1 x86-64

The x86 design must choose and verify:

- AP discovery and INIT–SIPI–SIPI through xAPIC, or a justified x2APIC route;
- the real-mode trampoline below 1 MiB, including the transition through protected to long mode,
  or an explicitly declared and differentially checked TCB byte blob;
- page-table and per-CPU stack setup;
- MTRR/PAT/page-table memory-type resolution and precedence proving shared RAM is WB and LAPIC/device
  mappings have the UC/device attributes assumed by their ordering rules;
- APIC-ID to `ThreadId` mapping;
- LAPIC UC-memory ordering and interrupt-command completion;
- QEMU `-smp` execution with accelerator classification.

### 10.2 AArch64

The AArch64 design must choose and verify:

- PSCI `CPU_ON`, spin-table release, or another explicitly supported platform mechanism;
- the exception level and SMC/HVC conduit assumptions;
- `MPIDR_EL1` to `ThreadId` mapping and per-PE stacks;
- coherent shareable mappings and the relevant MAIR/TCR/SCTLR configuration;
- GIC setup when interrupt-driven wakeups are introduced;
- `WFE`/`SEV` rendezvous and parking without confusing event-register behavior with a memory
  barrier;
- Device-memory and barrier semantics for GIC and PL011 MMIO.

### 10.3 Emulation Honesty

QEMU is valuable for boot protocol, encoding, lifecycle, and deterministic functional negative
controls. In particular, a TCG run is not weak-memory evidence. A
backend that does not faithfully expose the architecture’s weak-memory outcomes cannot validate
the memory model. Every run records native/KVM/WHPX/TCG status and reports “not validated” rather
than manufacturing a pass when required witness outcomes are unavailable.

---

## 11. Causality and Observable Traces

Four relations must remain distinct:

1. **ISA execution consistency** determines which memory executions are allowed using `po`, `rf`,
   `co`, dependencies, barriers, and architecture rules.
2. **Program happens-before** is generated by same-thread order plus genuine synchronization:
   spawn, successful join, and release/acquire pairs linked by the relevant read-from relation.
3. **Scheduler control causality** includes edges such as wake-to-resume without implying memory
   visibility.
4. **Observable causal order** is the projection of labelled program and scheduler causality onto
   effect events without conflating their edge kinds.

The explicit labelled edge graph is authoritative. Vector clocks may cache reachability only after
relations 2 and 3 are established, using separate relation-aware clocks or retaining the source-label
set on every edge. Comparing one clock over their union cannot recover whether an edge came from
program synchronization, scheduler control, or both, and may never synthesize that label. Clocks do
not replace relation 1. Plain reads-from is not automatically synchronizes-with, and futex wake is
not automatically synchronizes-with.

Concurrent canonical traces require stable origin-local event identities and equality of labelled
partial orders modulo schedule-independent event-key renaming/poset isomorphism, not equality of
arbitrary list linearizations or raw vector-clock numbers. The trace theorem is bidirectional on
observable events through an explicit node quotient. Every raw observable maps to exactly one
canonical node; a node has a nonempty raw-event fiber and therefore cannot be invented. A fiber may
contain multiple events only under a named per-effect coalescing rule, with stream, label, payload
fold, and causal-barrier preservation proved. Between distinct quotient nodes, a projected causal
edge appears in the trace if and only if the corresponding labelled program/scheduler causal edge
exists. One-way edge soundness alone would permit canonicalization to drop isolated events or
required edges.

---

## 12. Required Proof Package

The model is complete enough for use only when the following theorem families exist:

| Family | Required result |
|---|---|
| Instruction descriptor fidelity | Every program access/barrier is well formed and agrees with its static descriptor, target order/domain constraints, and actual step |
| Origin fidelity | Initial, instruction, platform, and device events have disjoint well-formed keys and refine only their owning transition rules and authority domains |
| Bounds/provenance | Every emitted access is in bounds, non-wrapping, aligned as required, and retains its region identity |
| Authority preservation | Every step preserves the per-thread contexts and global access-mode invariant |
| No ordinary data race | Distinct threads cannot perform authorized conflicting ordinary accesses |
| Atomic-mode safety | Registered atomic bytes admit only approved atomic operations; mixed atomic/plain access and stale grants after destruction are unrepresentable |
| Architecture consistency | Every admitted x86/AArch64 execution satisfies its architecture model |
| Emission/decoding fidelity | Emitted synchronization programs decode to the modeled instructions with relocation and layout preservation; the residual hardware-semantics boundary is cited and differentially tested |
| Atomic fidelity | Approved aligned atomic loads/stores and x86 RMW/AArch64 exclusive actions match target single-copy-atomicity, width, alignment, memory-type, success, and failure premises |
| Protocol synchronization | Every synchronizes-with edge has an instance/generation-matched witness tied to concrete release/acquire event keys, reads-from/RMW evidence, and a target realization proof |
| Lifecycle transfer | Spawn/donate, sealed termination, detach, and one-shot join preserve every authority, loan, grant, and obligation |
| Lock safety | At most one live guard owns a protected region; successful acquire/release transfer it correctly |
| Lock visibility | A new guard observes writes promised by the prior release under the target model |
| Futex refinement | Linux wait/wake refines atomic park-if-equal/wake without adding memory-order edges |
| Platform lifecycle | Windows, Linux, x86 bare metal, and AArch64 bare metal refine generic thread/PE transitions |
| Device/domain fidelity | Effective attributes select Normal versus Device/port-I/O semantics correctly; device values/side effects and ordering/completion barriers refine the selected device specification |
| Trace fidelity | The explicit observable-node quotient is total and non-inventing, preserves labels/payloads under named coalescing, and carries labelled causal edges iff their projected source edges exist, modulo event-key renaming |
| One-thread preservation | Existing sequential proofs survive as the one-thread/one-PE specialization |
| Progress | Under named fairness and platform assumptions, blocking acquire/join eventually returns when its protocol permits |

Safety and liveness remain separate. A safety theorem must not silently assume a fair scheduler, and
a terminating test run is not a liveness proof.

---

## 13. Validation Matrix

Each architecture owns a model-derived litmus suite. Tests share a declarative schema and harness
protocol, not hand-copied expected tables.

| Target | Model-side | Emitted/native | Bare metal |
|---|---|---|---|
| x86-64 | TSO outcome enumeration; locked/fenced variants | Windows and Linux x86-64 binaries on native or hardware-virtualized CPUs | AP bring-up, lock/counter, RAM litmus when accelerator is credible |
| AArch64 | Weak-memory outcome enumeration; plain, acquire/release, barrier, exclusive variants | Linux AArch64 binaries on native or KVM-backed systems | PE bring-up, lock/counter, RAM litmus when backend is credible |

Validation rules:

- every hardware-observed outcome must be model-allowed;
- reliably observable allowed outcomes are witness floors in scheduled stress runs, not flaky
  per-commit assumptions;
- histograms, seeds, architecture profile, CPU identifier, hypervisor/backend, and iteration budget
  are recorded;
- native validation runs only on CPUs covered by the pinned vendor/profile sources; other vendors
  report functional execution separately as `not-validated` for memory consistency;
- harness timeouts distinguish deadlock/hang from a forbidden memory outcome;
- negative controls deliberately remove or weaken a barrier/atomic/authority edge and must make the
  appropriate proof or test fail;
- harness correctness is verified independently enough that a stale result or serialized worker
  protocol cannot silently pass the model.

The portable lock counter is run on all supported targets, but its instruction sequence is target-
specific. Litmus expected outcomes are also target-specific.

---

## 14. Implementation Sequence and Exit Criteria

This roadmap replaces the deleted task-DAG references. A stage may be split into implementation
tasks, but its dependency and exit criteria remain here.

| Stage | Deliverable | Depends on | Exit criterion |
|---|---|---|---|
| M0 | Common well-formed dynamic event/graph vocabulary and target projection interfaces | current memory hooks | Existing x86 and AArch64 ordinary accesses project only to well-formed events; malformed-combination and omission controls fail |
| M1 | Provenanced regions, typed views, and indexed authority/obligation transitions | M0 | Unauthorized, stale, or byte-reloaded pointers without a live typed-view binding cannot be dereferenced; hierarchical allocation and realistic elaboration-cost gates pass |
| M2-X | x86 WB/TSO machine, atomics, fences, enumeration | M0 | x86 litmus theorems, one-thread theorem, decode/emission and relocation fidelity, and silicon validation |
| M2-A | AArch64 Normal-memory model, acquire/release, barriers, exclusives | M0 | Arm litmus theorems, one-PE theorem, decode/emission and relocation fidelity, and native validation |
| M3 | Generic process/thread scheduler, lifecycle, and park/wake contract | M0 | Two-thread stepping, park-if-equal/wake, spawn/join, and execution-agent state preservation |
| M4 | Cross-thread authority partition and lifecycle transfer | M1, M3 | Global access-mode/no-race theorems plus exact loan return, sealed terminal bundle, detach, and one-shot join conservation |
| M5-S | Portable lock invariant, result-indexed guards, typed release obligations | M4 | Fresh-instance init, acquire/release witness, failing try-acquire, and full resource-preserving destruction inverse—including stale-handle/grant rejection—satisfy the target-independent lock theorem |
| M5-X | x86 lock realization and visibility theorem | M2-X, M5-S | 32-bit mutex protocol implements M5-S under x86 TSO |
| M5-A | AArch64 lock realization and visibility theorem | M2-A, M5-S | 32-bit exclusive protocol implements M5-S under the AArch64 model; LSE requires a later profile extension |
| M6-P | Hosted Linux and Windows lifecycle/wait refinements | M4 | Spawn failure/success, lifecycle visibility, real one-shot join, blocked/runnable state, handle/TID lifetime, terminal bundles, platform authority for registered lifecycle/parking atomic words, and API outcomes refine the generic contracts |
| M6-X | Linux x86-64 futex and Windows x86-64 lifecycle/parking adapters | M2-X, M6-P | Thread lifecycle, join, wait, and wake paths execute independently of mutex integration; child-TID set/clear and park-if-equal comparisons satisfy atomic-mode, alignment, and x86 single-copy-atomicity obligations |
| M6-A | Linux AArch64 futex and lifecycle adapter | M2-A, M6-P | Thread lifecycle, join, wait, and wake paths execute independently of mutex integration; child-TID set/clear and park-if-equal comparisons satisfy atomic-mode, alignment, and AArch64 single-copy-atomicity obligations |
| M6-LX | Linux/Windows x86 blocking-lock integration | M5-X, M6-X | The selected 32-bit parked-mutex state machine separately refines Linux futex and Windows `WaitOnAddress`/`WakeByAddress*`, including release-before-notify, lost-wakeup, and spurious-return cases |
| M6-LA | AArch64 blocking-lock integration | M5-A, M6-A | The same selected abstract state machine, through AArch64-specific atomics, including release-before-notify, lost-wakeup, and spurious-return cases, refines the portable lock and parking contracts |
| M7-X | x86 bare-metal SMP and device-memory extension | M2-X, M3, M5-X | Two CPUs prove boot-mailbox handoff, run lock/counter, refine the selected wait strategy, and validate one device order/completion protocol plus barrier/attribute negative control; backend honesty reported |
| M7-A | AArch64 bare-metal SMP and device-memory extension | M2-A, M3, M5-A | Two PEs prove boot-mailbox handoff, run lock/counter, refine the selected wait strategy, and validate one device order/completion protocol plus barrier/attribute negative control; backend honesty reported |
| M8 | Concurrent causal trace projection and equivalence integration | M3, M5-S | Total/non-inventing observable-node quotient plus bidirectional labelled-edge fidelity modulo event-key renaming |
| M9 | Full cross-target Spike 8 validation matrix | M6-LX, M6-LA, M7-X, M7-A, M8 | Model, emitted binaries, OS adapters, and both bare-metal paths satisfy §13 |

M2-X and M2-A should proceed in parallel after M0. M1 can also proceed in parallel, but no lock or
thread-safety claim lands until the three paths meet at M4/M5-S and the relevant M5-X/M5-A
realization.

Execution discipline:

- implementation work names the owning stage in its change and updates the stage's current-status
  evidence here; retired task IDs are not resurrected as a parallel dependency graph;
- a common-interface change supplies projections or an explicit design-only status for both x86-64
  and AArch64 in the same change, preventing silent TSO defaults;
- an ISA or platform refinement may advance independently once its own dependencies are complete;
  no cross-target dependency is added merely for scheduling convenience;
- each semantic increment lands with its connection lemma, model-level test, emitted/native test
  where available, and a planted negative control appropriate to its trust boundary;
- a stage is complete only on its stated exit criterion, not because representative examples pass.

---

## 15. Decisions Required Before Implementation

The following are deliberate stop-and-design gates:

1. **AArch64 formal profile:** exact Arm architecture revision/features, shareability assumptions,
   and official model material to ingest.
2. **Common event representation:** concrete Lean types and whether bounded enumeration uses one
   graph engine or per-architecture engines connected to the graph.
3. **Indexed authoring surface:** how `BlockM` prevents arbitrary permission/obligation replacement
   while retaining usable errors and acceptable elaboration cost.
4. **Windows wait profile:** pin the minimum supported Windows version plus exact
   `WaitOnAddress`/`WakeByAddress*`, thread-object wait, timeout, and error contracts. A thread-handle
   join is not a mutex parking primitive.
5. **x86 AP startup:** verified 16/32-bit trampoline versus a declared, validated TCB blob.
6. **AArch64 secondary startup:** PSCI conduit and QEMU/real-platform profile.
7. **Futex v1 errors:** exact supported return codes and explicit behavior for unsupported timeout,
   signal, and shared-process cases.
8. **Parked-mutex protocol:** pin the 32-bit state values and transitions, fast/slow-path
   linearization points, waiter marking, exact wait expected value, release store, wake policy, and
   retry behavior. A 0/1 always-wake protocol and a 0/1/2 contended protocol are not proof-
   interchangeable.
9. **x86 vendor profile:** choose Intel 64 only or a common Intel/AMD64 subset and state the
   eligible CPU/vendor test matrix. AMD hardware is not covered by an Intel-only citation.

Each decision must update this document and cite authoritative architecture or OS material before
Lean semantics are added.

### 15.1 Reference-intake gate

Implementation does not cite this design as architectural ground truth. Before the corresponding
stage starts, `references.json` must pin and hash authoritative material for:

| Surface | Required source family |
|---|---|
| x86-64 | the registered Intel SDM edition for an Intel-only profile; additionally the matching AMD64 Architecture Programmer's Manual material before AMD CPUs are eligible: WB/TSO rules, locked operations/fences, memory types, and multiprocessor initialization |
| AArch64 | an exact Arm Architecture Reference Manual profile plus matching official A-profile `aarch64.cat`/herd tooling material |
| Linux | kernel UAPI/syscall ABI and Linux man-pages definitions for clone/child-TID lifecycle and futex wait/wake |
| Windows | Microsoft documentation for thread creation/exit, thread-object waits, handle lifetime, and the selected address-wait primitive |
| x86 bare metal | Intel startup/APIC material and selected platform/device specifications |
| AArch64 bare metal | Arm PSCI, exception-level, GIC, translation/memory-attribute, and selected platform/device specifications |

Each Lean declaration cites the narrowest applicable registered anchor. A hardware observation or
QEMU behavior is validation evidence, not a substitute for the architecture/OS contract.

---

## 16. Requirement Closure

| Need | Where it is satisfied |
|---|---|
| x86 TSO | §5.1, M2-X |
| AArch64 weak memory | §5.2, M2-A |
| Shared cross-architecture contract | §§3–4, §5.3, M0 |
| Provenanced pointers and borrowing | §6, M1/M4 |
| Pointer-valued fields and hierarchical allocation | §§6.1.1–6.2, M1 |
| Cross-thread donation and join | §6.4, M3/M4 |
| Lock invariants | §7, M5-S/M5-X/M5-A |
| Must-unlock obligations | §7.3, M5-S |
| Linux futex | §9, M6-P/M6-X/M6-A |
| Windows threads/waits | §§8–9, M6-P/M6-X |
| x86 bare-metal SMP | §10.1, M7-X |
| AArch64 bare-metal SMP | §10.2, M7-A |
| MMIO/device ordering | §4 and §10 |
| Causal traces | §11, M8 |
| Litmus and silicon validation | §13, M9 |
| Safety and liveness separation | §§8, 12 |

This table is the acceptance checklist for future plan changes. A proposed concurrency feature that
does not identify its authority rule, architecture ordering rule, lifecycle effect, obligation
effect, and validation vehicle is incomplete.

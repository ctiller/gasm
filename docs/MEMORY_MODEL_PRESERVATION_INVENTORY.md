# Memory-model preservation inventory

**Status:** authoritative pass-1 preservation inventory, re-verified over
[`MEMORY_MODEL.md`](MEMORY_MODEL.md) at repository base
`4c3ef8b3c3a629f90b706c9fda33458d42b0cdc9`. This document records source-owned meaning and
acceptance conditions only. It does not design a successor, name successor APIs or theorems, map
requirements to a new destination, authorize migration, weaken a clause, or authorize implementation.
Historical plans, ledgers, prototypes, and proof files are spare-parts evidence only.

## 1. How to read this inventory

The source declares itself the canonical cross-architecture design and implementation roadmap and
states that no concurrent memory model is implemented yet. Accordingly:

- **Normative** means the source requires the claim for the applicable selected profile.
- **Conditional** means the requirement activates only when its profile, operation, failure path, or
  stronger claim is selected.
- **Deferred** means the seam or negative compatibility boundary is preserved now, but the future
  profile is not a current implementation or M0--M9 acceptance burden.
- **Baseline evidence** means §2 reports relevant machinery present in the tree; it does not prove
  the completed semantic claim.
- **Gate** means normative implementation or theorem statements must not begin before the named
  decision and reference intake are accepted.

Every row is preservation-sensitive. Silence in a future proposal is not a disposition. A later
preservation ledger must cite each row and record unchanged recovery, an explicitly approved change,
or an explicitly retained deferral. No row may be discharged merely by renaming a type, importing a
historical proof, passing a representative test, or asserting that a feature is unlikely to occur.

## 2. Root status, ownership, and invariants

| Source anchor | Claim to preserve | Qualifier / current evidence status |
|---|---|---|
| [preamble](MEMORY_MODEL.md#memory-concurrency-ownership-and-synchronization-model) | The document owns the shared architecture for memory, concurrency, ownership, synchronization, and Spike 8; target documents own encodings/platform detail. ABI contexts consume and transport this world rather than define a parallel ownership or cleanup system. | Normative ownership rule. §2 is only a baseline inventory; missing/future items are requirements, not implemented declarations. |
| [central rule](MEMORY_MODEL.md#memory-concurrency-ownership-and-synchronization-model) | Ownership transfer and synchronization share an architecture-neutral contract, while every ISA and execution environment separately proves its realization. | Normative. Explicitly rejects generic x86 TSO, “AArch64 as TSO plus fences,” futex-as-barrier, and bare-metal-as-OS-thread-API shortcuts. |
| [§1 goals](MEMORY_MODEL.md#1-goals-guarantees-and-scope) | Architecture-correct x86/AArch64 execution; capability-enforced access; linear cross-thread transfer; lock guard/release accounting; blocking adapters; two SMP paths; faithful labelled causal traces; differential validation; honest one-host-process scope; and selected observable performance/security bounds. One demand may refine to several mechanisms and several demands may share one mechanism only through an explicit theorem. | Normative completed-system envelope. Hosted multiprocess behavior is deferred, not silently approximated. The common model assumes neither universal multi-copy atomicity nor a fixed two-thread cardinality; it is parameterized by thread/agent count although the first suite is two-thread/two-PE. |
| [§1 first profile](MEMORY_MODEL.md#1-goals-guarantees-and-scope) | Initially admit aligned 32/64-bit shared words, WB/coherent-shareable Normal memory, target-proved atomicity, explicit Device/MMIO, private futex, and bounded initial litmus/lock programs. | Conditional profile boundary. Mixed-size overlap, SMC, persistence, non-temporal access, and wider futex surfaces require explicit widening plus validation. |
| [§1 M3 scope](MEMORY_MODEL.md#1-goals-guarantees-and-scope) | M3 is one host process's CPU thread domain or one bare-metal CPU/PE machine, not multiprocessing and not one universal address space. | Normative scope exclusion; GPU/device/IOMMU/RDMA domains remain independently indexed. |
| [§1 extension rule](MEMORY_MODEL.md#1-goals-guarantees-and-scope) | Future Wasm, SPIR-V/Vulkan, WebGPU, DMA, network/IPC, and storage domains need their own agents, locations, scopes, relations, and consequences while reusing only genuinely common seams. | Deferred but preservation-critical. §15 decision 2 must keep target-indexed extension points open. |

## 3. Verified baseline and nonclaims

Source: [§2 Verified Current Baseline](MEMORY_MODEL.md#2-verified-current-baseline).

| Area | Present evidence reported by the source | Missing semantic closure that must remain visible |
|---|---|---|
| x86 memory | Sealed byte memory, width-indexed access, mandatory per-instruction access descriptions, frame lemmas. | Atomic forms, fences, store buffers, concurrent machine. |
| AArch64 memory | Sealed byte memory and an access-spec vocabulary. | Descriptor integration, atomic order, barriers, exclusives, concurrent machine. |
| Capabilities | Permission-share and memory-permission vocabulary. | Constructor enforcement, provenanced authoring, temporal loans, cross-thread transfer. |
| Obligations | Generic token list and return/exit predicates. | Typed lock/join/wait obligations and non-forgeable indexed evolution. |
| Indexed programs | Indexed state-transformer bind. | Borrow/obligation indexing and constructors that prevent arbitrary state replacement. |
| Boundary contexts | Relational entry/exit, exact export/link/component certificates, universal root connection substrate. | M1 world, coherent heterogeneous rows/conservation, closed profile registry, substantive M2-B realizations and admission. |
| Causality | Thread identities, vector clocks, causal events, single-thread stamping. | Concurrent graph, sound synchronizes-with generation, multithread trace projection. |
| OS threads/processes | Single-state hooks and one implicit root. | Runnable/blocked lifecycle, joins/waits; multiprocess remains explicitly deferred. |
| Bare metal | Single-CPU paths. | SMP startup, coherence premises, wake/interrupt model, per-agent state. |

No concurrency claim is implemented until stated over at least two threads/PEs. A one-thread ordering
result is not concurrent-model validation.

## 4. Layering and boundary closure

Source: [§3 Layering and Ownership of Semantics](MEMORY_MODEL.md#3-layering-and-ownership-of-semantics).

| Clause | Meaning to preserve | Controls, assumptions, and status |
|---|---|---|
| Three-level lens | Level 1 states communication/synchronization consequences and bounds; level 2 independently chooses a domain plan; level 3 proves actual ISA/platform/device/provider/transport realization. | Normative. Neither a domain proof without level 3 nor an ISA fact without a selected domain plan closes the root. |
| Mandatory connection: origin | Program events arise from actual described instruction steps; initial/platform/device events arise only from their owner transitions. | Normative origin non-forgery. |
| Mandatory connection: authority | Each program event is covered by current thread authority; platform/device/initial events use their separately scoped authority/invariant. | Normative. |
| Mandatory connection: entries | Every verified-code call/root/start/callback/handler boundary relates physical state to exact logical arguments, binding, and live authority/obligation world; caller/link or platform/loader establishes the tuple. | Exact provenance/generation cannot be decoded from equal physical bits. Admission and artifact connection are independent premises. |
| Mandatory connection: results | Results, fresh identities, outcomes, and after-world remain relational when erased information is not physically recoverable; functional projection is limited to proved scalar/physical data and cannot mint authority or freshness. | Normative nonvacuity and generativity rule. |
| Mandatory connection: consistency/emission | Every admitted execution satisfies its ISA predicate; emitted bytes decode to modeled instructions with relocation/layout fidelity. | Hardware-semantics residue is a cited TCB assumption and differential-test target. |
| Mandatory connection: synchronization/trace | CPU release/acquire edges require actual read-from/lifecycle witnesses; other domains retain their own relation witnesses. Every projected causal order retains a selected-profile labelled path, bidirectionally for declared observables. | Wake, notification, device signal, and CPU synchronization are not interchangeable. |
| Address-wait separation | Unary address waits refine only the narrow parking contract; composite wait, notification, interrupt, and device signals use separate adapters. | Normative prevention boundary. |
| Current ABI substrate | Current boundary/context modules are staging substrate, not a competing model and not completion of M1/M2-B. | Baseline evidence only; shared indexed world, conservation, registry, substantive realization/admission remain missing. |
| Boundary-profile closure | Each concrete M2-B profile has one closed registry entry for entry/result subset, origin, admission, artifact/TCB connection, and prevention class; closure connects logical transition and authority change to physical control/artifact transition. | False/empty relations, trivial admission, unconstrained ghost ordering, weak artifact relation, and physical identity minting must fail. Reusable per profile; callers prove only entry premises. |
| Profile independence | Ordinary call, syscall, root, thread lifecycle, native lifecycle, and parking profiles are selected independently and confer nothing on siblings. | `VerifiedProgram` requires the exact reachable closure. Future child/image boundaries remain deferred. |

## 5. Event, binding, graph, and target-projection vocabulary

Source: [§4 Common Dynamic Memory-Event Vocabulary](MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary).

| Clause | Meaning to preserve | Controls / qualifier |
|---|---|---|
| Target-specific operands, common envelope | Static addressing remains target-specific; after effective-address resolution, each target provides a checked projection into a thin common envelope. | The illustrated CPU record is information content, not an accepted universal Lean representation. |
| M0 boundary | Preserve generative identities; profile-indexed agent/reference/location/payload/relation/consequence families; well-formed projections; labelled paths; trace laws. | Future-domain constructors await their own reference intake. A meaningless non-CPU sentinel must test openness without guessing an API. |
| Dynamic binding | Resolution is time-indexed by object, key, generation, rights, logical/backing footprint, and explicit alias/overlap; bind/unbind/rebind transitions own validity. | Raw equality neither proves alias nor identity. Backing need not be a CPU numeric address. |
| Async capture | Each asynchronous operand captures the generation at its profile-selected snapshot/consumption event; later effects/returns/cleanup retain it. | Required negative control: capture old generation, rebind key, then later effect must still target/return only the captured generation. |
| CPU event well-formedness | Role/value presence, width, failure write-absence, legal orders, target width/alignment/atomicity, memory domain, origin/key agreement, and target-specific constraints are enforced. | Orthogonal fields do not license malformed combinations. `none` ordering is neither `relaxed` nor proof of non-atomicity. |
| Barriers and maintenance | Barriers, cache maintenance, translation/IOMMU maintenance, and device transitions have explicit scope/domain/completion semantics rather than fake memory ranges or generic fences. | Target retains finer encoding and partial-range/alias rules. |
| CPU synchronization witness | A mutex synchronization edge names instance/generation, release/acquire observation, success linearization when distinct, read-from/RMW evidence, and target proof. | Failed RMW/exclusive actions produce no witness. This shape is not universal for GPU/device/API relations. |
| Execution graph | Retain `po`, invocation/platform edges, byte/range `rf`, Normal-memory `co` and initial writes, `fr`, dependencies, barriers, RMW/exclusive relations, lifecycle, and target-native device/value/consequence relations. | `rf` is authoritative and never duplicated as a source field. One byte/range read may assemble bytes from multiple writes; the common interface cannot bake in same-width single-source reads even while initial mixed-size validation is deferred. Device/port-I/O receives no invented Normal-memory coherence. |
| Platform atomic access | Kernel child-TID writes and comparable platform transitions participate in atomic/plain safety and target atomicity; invocation/return connects them to the causing program. | Platform origin is not an escape hatch from §6.3. |
| Stable identity | Event identity is origin-local; logical thread IDs are generative and not raw OS/CPU identifiers. Graph equality is independent of global allocation order. | Normative non-reuse and non-conflation rule. |

## 6. Architecture-specific consistency

### 6.1 x86-64

Source: [§5.1 x86-64: TSO for Write-Back Memory](MEMORY_MODEL.md#51-x86-64-tso-for-write-back-memory).

- Pin Intel-only versus cited Intel/AMD subset; uncovered CPUs are functional-only and
  `not-validated` for memory-model claims.
- Model per-agent FIFO buffers, same-range forwarding, oldest-store drains, indivisible locked RMW,
  architectural `MFENCE`, and selected aligned access atomicity over WB memory.
- Preserve the distinction between atomic authority/class and the underlying `MOV` TSO transition.
- Keep UC/WC/MMIO outside WB TSO and require separate device/memory-type evidence.
- Preserve the library-specific 32-bit instruction demand without turning it into the portable mutex
  representation.
- Required connections: one-thread preservation; indivisible atomic actions; execution-graph
  consistency; sound/complete bounded enumeration against an independent finite relation and bound;
  finite-suite equality to selected TSO; broader enumerator adequacy only when a stronger advertised
  claim consumes it.

### 6.2 AArch64

Source: [§5.2 AArch64: Weak Memory, Acquire/Release, and Exclusives](MEMORY_MODEL.md#52-aarch64-weak-memory-acquirerelease-and-exclusives).

- Pin the Arm ARM/profile, shareability, errata, official `cat`, and herd7 identity; the formal model
  is the allowed-outcome oracle and native observations only test containment.
- Preserve plain `LDR`/`STR`, `LDAR`/`STLR`, exclusive sequences and monitor state, `CLREX`, scoped
  barriers, system sequencing, and WFE/SEV notification without x86 defaults.
- Successful store-exclusive is the acquisition linearization event; spurious failure and profile
  invalidations are represented; eventual success needs an explicit progress premise.
- V1 is aligned 32/64-bit coherent-shareable Normal memory. LSE, RCpc, mixed size and non-shareable
  behavior remain conditional future profiles. A generic acquire label cannot erase RCsc/RCpc.
- Required connections: one-PE preservation; exact exclusive events; descriptor/order fidelity;
  admitted-execution consistency; exact finite enumerator; equality with pinned Arm suite and native
  containment; broader adequacy only for stronger consuming claims.

### 6.3 Shared versus target-owned

Source: [§5.3 What Is Shared and What Is Not](MEMORY_MODEL.md#53-what-is-shared-and-what-is-not).
Event identity/relations, provenance/authority, lock/guard/obligation contracts, lifecycle/parking,
validation protocol and trace projection are shared. Allowed graphs, encodings/addressing, local
machine state, barrier semantics/scope, memory attributes, and SMP startup remain architecture-owned.

## 7. Provenance, borrowing, and lifecycle authority

### 7.1 Regions and pointer-valued memory

Sources: [§6.1](MEMORY_MODEL.md#61-regions-and-provenanced-pointers),
[§6.1.1](MEMORY_MODEL.md#611-pointer-valued-memory-v1-boundary), and
[§6.1.2](MEMORY_MODEL.md#612-indirect-resources-bindings-and-aliases).

- Region identity is fresh and generative, not address-derived. Dereference requires matching region,
  in-bounds non-wrapping range, access authority, and required alignment/stability.
- External grants are explicit reviewed boundaries; integer conversion is not ordinary authority.
- Loaded bytes never manufacture a provenanced pointer. V1 pointer fields require a live typed-view
  slot binding that moves with the field; pointee authority remains indexed separately.
- Generic recursive/existential ownership recovery is outside v1. Deferred reclamation profiles must
  provide their own protect/lifetime/ordering discipline and cannot convert bytes to authority.
- Indirect resources distinguish naming, binding mutation, content access, and reclamation. Exact
  generation, device/namespace, rights, logical scope, and backing footprint are retained; alias,
  sparse/nonresident behavior, import, destruction, and invalidation are profile-owned.

### 7.2 Authority algebra and global invariant

Sources: [§6.2](MEMORY_MODEL.md#62-authority-states) and
[§6.3](MEMORY_MODEL.md#63-global-cross-thread-invariant).

- Preserve distinct exclusive, shared-read, and registered-atomic modes; atomic authority covers only
  the declared object, not the protected region.
- Composition is a resource algebra. Read loans carry unique identity/holder records and exact return
  promises; donation moves rather than copies; splits suspend overlapping parent access; rejoin needs
  the exact descendant-free sibling set; typed views carry destruction/discharge.
- Globally, ordinary writer uniqueness and reader/writer exclusion hold; registered atomic bytes
  permit only supported atomic operations and exclude ordinary access until all grants are consumed.
- Prove no authorized ordinary race and no plain access to registered atomics from the invariant plus
  descriptor fidelity.
- Seqcount/seqlock is a conditional, profile-local exception using quarantined unvalidated snapshots,
  explicit commit/retry, independent pointer lifetime, writer serialization/wrap/tearing and
  scheduling/interruption premises. It does not weaken the ordinary invariant.

### 7.3 Spawn, join, termination, and root exit

Source: [§6.4 Task/thread spawn, join, and termination](MEMORY_MODEL.md#64-taskthread-spawn-join-and-termination).

- Spawn partitions authority before a child can run; failure restores once and success commits once.
- Success creates generative task identity and, when joinable, a unique result-indexed join right.
  Timeout/observation preserves it; logical join consumes it once and returns only the sealed bundle.
  Platform handles/close obligations are separate.
- Every terminal bundle accounts for every authority, loan, atomic grant, guard, and obligation via
  return, named handoff/discharge, or transfer to a live tracked recipient. Detach is permitted only
  under the stated bundle/sink condition.
- Root exit accounts for all threads and unconsumed bundles. Only explicitly root-lifetime resources
  use a target teardown theorem. OS termination, a droppable Boolean, or failure-domain abort is not
  normal discharge.
- Spawn/join memory visibility requires a separately proved lifecycle visibility relation; runnable,
  signaled, clear, or wake alone is insufficient.

### 7.4 Deferred hosted processes

Source: [§6.5 Deferred hosted-process extension](MEMORY_MODEL.md#65-deferred-hosted-process-extension).
M0--M9 contains no process creation/image/reap/inheritance/cross-process authority or shared robust
constructor. Preserve generative domain qualification, binding generations, relational results,
resource-specific failure, and the negative rule that task join is not process observation. Detailed
future meaning remains solely in `FUTURE_PROCESS_MODEL.md` and activates consumer-by-consumer after
M9; it is not current closure. Current logical cross-domain sharing is frozen COW snapshot only and
must generation-rebind to fresh backing before any store. A future physical COW realization triggers
on every store-class effect, not ordinary writes alone; opaque child/image writable sharing requires
explicit environment-interference authority.

## 8. Lock and synchronization-library contract

Source: [§7 Lock Invariants and Unlock Obligations](MEMORY_MODEL.md#7-lock-invariants-and-unlock-obligations).

| Subclause | Meaning to preserve | Qualifiers / controls |
|---|---|---|
| Portable lock invariant | The v1 nonrecursive mutex connects an opaque stable core, disjoint protected region, and implementation-declared auxiliary resources without fixing width, layout, parking, algorithm, or queue policy. Initialization consumes raw authority, registers core atomics, and creates a fresh lock identity distinct from every acquisition generation. | Normative M5-S surface. Physical bits alone do not establish ownership. Healthy and recovery guards are non-interchangeable. |
| Auxiliary resources | Contender/infrastructure nodes remain owned until checked lending; publication, handoff, cancellation, withdrawal, reuse, and retirement carry typed lifetime/accounting. | Queued locks are future profiles; `ParkedMutex32` remains the M7 baseline without closing the seam. |
| [§7.1 Acquire](MEMORY_MODEL.md#71-acquire) | Result-indexed outcomes distinguish non-acquisition with exact return/deferred withdrawal, healthy acquisition with guard/authority/release promise, profile-specific quarantined recovery, and permanent nonrecoverability. | First `ParkedMutex32` exposes only non-acquisition/healthy acquisition. Robust POSIX and Windows abandonment remain distinct gated profiles. |
| Acquire progress | Safety, system acquisition progress, starvation freedom, and bounded wait are distinct; stronger claims name continuous eligibility, successful progress events/rank, fairness/interference, and eventual holder release/handoff/recovery. | Cancellation/timeout/cleanup/deferred withdrawal cannot witness acquisition progress. Mutex progress does not imply multi-lock deadlock freedom. |
| Owner and async acquire | Owner identity is profile-owned. Handoff/reindex is an explicit linear transition. Pending async acquire holds only a pending resource until the selected success event. | Failure/cancellation creates no guard and returns or explicitly defers every scoped resource. Same-address mention does not create synchronization. |
| [§7.2 Release](MEMORY_MODEL.md#72-release) | Release consumes the exact owner/instance/generation guard, protected authority, and release promise at the physical linearization event; it returns authority to the invariant and proves promised visibility. | x86 replacement stores and AArch64 release/exclusive updates need exact whole-word/packed-state proofs. Ghost transfer cannot float to an unrelated event. |
| [§7.3 Typed Obligations](MEMORY_MODEL.md#73-typed-obligations) | Preserve typed release, recovery, withdrawal, join/detach, wait-unregister, keep-alive, allocation/view and OS-resource obligations with safe result-indexed evolution. | Arbitrary permissions/obligation replacement is outside checked authoring. Scheduler registrations differ from author obligations. Destruction is the exact resource inverse and forced holder termination is unsupported absent a recovery profile. |
| [§7.4 Implementations](MEMORY_MODEL.md#74-implementations-and-library-selection) | Each implementation supplies core/auxiliary representation, state and lifecycle, linearization/results, owner policy, event realization, progress, parking, and exact refinement. Selection is trait-directed. | `ParkedMutex32` is preferred, not universal. Packed/specialized designs prove width/alignment/scope, reachability, payload preservation, result/visibility, wait/lost-wakeup, notification, target and validation claims. Handler eligibility is separately proved. The CPU-thread M5-S contract is not automatically eligible for shader/device agents: a target proves topology participation, visibility, safety, no-deadlock and progress; spinning/blocking is rejected without independent forward progress, while collective/barrier plans require convergent or dynamically uniform participation. |
| [§7.5 Multi-lock](MEMORY_MODEL.md#75-multi-lock-ordering-and-deadlock-demands) | Per-lock safety does not prove program deadlock freedom. A demand may use well-founded rank, multi-lock primitive, rollback/backoff, scheduler/transaction plan, fusion, or another explicit acyclic wait proof. | Fusion must preserve authority union, progress, observability, footprint and performance; mention of synchronization alone selects nothing. |
| [§7.6 Future libraries](MEMORY_MODEL.md#76-future-cpu-synchronization-library-profiles) | Read/write locks expose compatible shared-reader guards or one exclusive-writer guard and pin upgrade/downgrade, preference, recovery and progress. Condition variables atomically release the selected mutex and register the wait, retain the predicate-loop duty, permit profile-spurious wake, and reacquire a valid guard for every returned result. Semaphores own bounded generative permits with exact initial/max count, overflow, timeout/cancel, visibility, destruction and progress. | Deferred and independently profiled. Negative controls reject wake-as-predicate/publication, permit-as-mutex, reader/writer overlap, lost registration, duplicate permits and unsafe destruction. |

## 9. Scheduler, asynchronous contexts, and waits

### 9.1 CPU thread/PE scheduler

Source: [§8 Thread/PE Machine and Scheduler](MEMORY_MODEL.md#8-threadpe-machine-and-scheduler).

- M3 owns one host-process CPU thread domain or bare-metal machine with shared domain state, logical
  thread state, execution-agent-local architecture state, and a scheduler mapping.
- It does not own a process table/handle graph/address-space theorem; identities remain generative and
  domain-qualified and heterogeneous domains keep their own agents/schedulers.
- Store buffers and reservations belong to execution agents with profile-specific migration,
  deschedule, exception and drain behavior.
- Global steps include selected thread instructions, propagation, API/lifecycle/scheduler transitions,
  and modeled device transitions.
- Safety quantifies over scheduling nondeterminism; progress states fairness explicitly. Fuel is a
  runner, not termination or deadlock evidence.

### 9.2 Deferred processes and optional scheduler profiles

| Source | Preservation requirement | Status |
|---|---|---|
| [§8.1](MEMORY_MODEL.md#81-deferred-hosted-process-system-layer) | Keep the M3 process deferral and the later composition seams: domain qualification, binding generations, relational lifecycle, environment agents/channels, resource-specific failure. Heterogeneous device domains remain possible without becoming processes. | Deferred; no placeholder burden. |
| [§8.2](MEMORY_MODEL.md#82-restartable-sequences) | Rseq binds a registered thread, CPU/domain identity, critical range, commit and abort. Only final commit creates the consequence; earlier effects are not rolled back and need restart/idempotence/quarantine/compensation; no irreversible authority transfer occurs before commit. | Future profile with exact kernel/libc/ABI/layout/interrupt and progress intake, including a pinned nesting-prohibition policy. Gives no guard or visibility without separate proof. |
| [§8.3](MEMORY_MODEL.md#83-direct-user-scheduling-handoffs) | A user handoff preserves two logical identities and models timeout/signal/exit/cancel/wake races, accounting, rebinding, and wait-record lifetime. | Historical `SwitchTo`/`FUTEX_SWAP` material is prior art only. Control transfer gives neither guard transfer nor publication. |

### 9.3 Interrupt, exception, signal, trap, and cancellation

Source: [§8.4 Interrupt, Exception, Signal, and Trap Contexts](MEMORY_MODEL.md#84-interrupt-exception-signal-and-trap-contexts).

- Handler locality, identities, entry/return/control edges, masks/priorities, nesting, stacks,
  save/restore, and architecture-local effects are profile-specific.
- Callable safety is an indexed trait over exact context, nesting/priority/mask, authority footprint,
  reentrancy, allowed blocking/allocation/fault/host calls, bounded stack/progress, and cleanup.
  Thread safety, IRQ safety, NMI safety, signal/APC safety, and future lifecycle phases do not imply
  one another.
- Simultaneously active traits compose by intersection. Entry grants no ordinary authority; return
  restores only the selected suspended context.
- Selected Windows SEH distinguishes continuation, search/propagation, nested first-pass filters,
  nonlocal and collided unwind. Frame-by-frame cleanup, exact unwind metadata/artifact, context
  mutation, retired frames, and live exception state are preserved. Ordinary return, unwind,
  propagation and fatal termination are not interchangeable.
- Every interruption point is atomic or exposes valid restart/compensation/partial-effect states.
  Retry cannot duplicate an accepted effect or lose wait registration. Safety is transitive through
  the reachable call graph.
- Handler authority is explicit. Self-deadlock, forbidden blocking/allocation/fault/runtime calls,
  and unproved lock use are rejected. Fatal/abort outcomes use total resource-class-specific
  dispositions, never wildcard `indeterminate` or normal cleanup. Surviving device/remote resources
  remain outside CPU/host abort unless their own profile says otherwise.

### 9.4 Address parking and composite waits

Source: [§9 Address Parking and Composite Platform Waits](MEMORY_MODEL.md#9-address-parking-and-composite-platform-waits).

- Unary `park-if-equal`/`notify` is a narrow, platform-result-sensitive address adapter, not a
  universal wait or memory-order operation. PAUSE/WFE/SEV/IPI are not silently atomic enqueue.
- Composite wait-any/all has typed heterogeneous entries, exact generation/lifetime, one atomic
  validate/register step, and result-indexed authority. Its exact object index/set, timeout,
  interruption, APC, failure, and abandoned-ownership outcomes remain platform/profile-specific.
  Repeated unary waits cannot simulate it.
- The selected mutex owns its slow-path state, expected value, transition, wake policy and retry;
  the generic adapter does not repair protocol bugs.
- Linux private futex requires stable aligned mapped 32-bit lifetime, atomic comparison/enqueue,
  `EAGAIN`, address-domain queue identity, bounded nondeterministic wake, exact return/state change,
  spurious/retry behavior and registration removal. Linux exposes a number-woken result; Windows
  address wake exposes no count and the portable seam cannot fabricate one.
- Every comparison is an approved atomic load of a registered object at the admitted width; it does
  not bypass atomic/plain safety or create synchronization.
- Timeout, signal, shared futex, requeue, PI, robust and wider operations remain explicit follow-on
  profiles rather than invented semantics.
- Release/acquire publication is distinct from notify/wake. Release-before-notify and lost-wakeup
  ordering are separately proved; wake-to-resume is scheduler causality only.
- The first `ParkedMutex32` profile selects only the unary seam; unopened composite profiles create
  no wide baseline proof tax.

### 9.5 Hosted lifecycle profiles

| Source | Requirement | Profile boundary / evidence need |
|---|---|---|
| [§9.1 Linux](MEMORY_MODEL.md#91-linux-thread-exit-and-join) | Child-TID storage is a stable registered aligned 32-bit atomic; selected kernel set/clear participates in target atomicity; clear/wake is lifecycle observation; separate release/acquire publication establishes §6.4 visibility; exact clone/syscall/errors/lifetime are ingested. | M6-T plus selected native lifecycle and optional parking, never a process-reap claim. |
| [§9.2 Windows](MEMORY_MODEL.md#92-windows-thread-lifecycle-and-parking) | Partition before child runnable; distinguish thread/process exits; separate thread-object signal, wait, join right, and handle close; preserve timeout/failure/pending lifetime; keep per-thread state local; prove address-wait retry and separate lifecycle visibility publication. | Thread/object and address-parking profiles are independent. Process creation/jobs remain deferred. |
| [§9.2 bare-metal tail](MEMORY_MODEL.md#92-windows-thread-lifecycle-and-parking) | Spin/PAUSE or spin/WFE and later interrupt/IPI wrappers preserve the same lock contract; explicit atomic recheck performs comparison. | No futex/Win32 semantics on bare metal. |

## 10. Bare-metal, DMA, interrupt delivery, and emulator honesty

Source: [§10 Bare-Metal SMP and Device Memory](MEMORY_MODEL.md#10-bare-metal-smp-and-device-memory).

| Subclause | Requirements to preserve | Controls / assumptions |
|---|---|---|
| Shared SMP contract | Finite PE discovery/start, unique logical identities/stacks, coherent Normal/WB setup, rendezvous, park/wake/termination, explicit device events. | Startup and notification mechanisms do not publish RAM; mailbox/authority handoff requires target release/acquire. |
| [§10.1 x86](MEMORY_MODEL.md#101-x86-64) | Choose APIC route; trampoline or declared TCB blob; tables/stacks; MTRR/PAT/page attributes; APIC mapping/order/completion; QEMU accelerator classification. | Exact source/profile and device evidence required. |
| [§10.2 AArch64](MEMORY_MODEL.md#102-aarch64) | Choose PSCI/spin-table mechanism, exception level/conduit, MPIDR mapping/stacks, coherent MAIR/TCR/SCTLR, GIC if selected, WFE/SEV behavior, Device/barrier semantics. | Exact source/profile evidence required. |
| [§10.3 DMA](MEMORY_MODEL.md#103-dma-coherency-and-cache-ownership) | Pin coherency/address mapping, direction, cache granule/partial-line isolation, ownership transitions, maintenance/completion, barrier scope, doorbell order and completion event. | Barrier is not maintenance; maintenance is not completion; interrupt/doorbell is not either. API-level pinned provider contracts may abstract unmodeled driver details honestly. |
| [§10.4 control delivery](MEMORY_MODEL.md#104-interrupt-and-control-delivery) | Preserve distinct device signal, controller route, CPU acceptance, handler entry, status/completion observation, acknowledgement/EOI, driver unblock, scheduler wake. | Negative controls reject interrupt-as-completion, entry-as-DMA-visible and entry-as-wake absent the exact selected path. |
| [§10.5 emulation](MEMORY_MODEL.md#105-emulation-honesty) | Record native/KVM/WHPX/TCG classification and report `not validated` when the backend cannot expose required weak behavior. | QEMU functional evidence is not weak-memory validation. |

## 11. Causality and trace fidelity

Sources: [§11 Causality and Observable Traces](MEMORY_MODEL.md#11-causality-and-observable-traces)
and [§11.1 Global and heterogeneous order](MEMORY_MODEL.md#111-global-and-heterogeneous-order).

- Keep five distinct layers: target consistency, CPU program happens-before, scheduler control
  causality, target/domain-native causality, and checked observable projection. Projection is not a
  second source model.
- There is one event envelope but no unlabeled global memory happens-before. Consequences are typed:
  publication/acceptance/consumption, execution, visibility, authority transfer, completion,
  terminality, result observation, reclamation, notification, reuse, capacity, delivery,
  acknowledgement, persistence, and observable dependence remain distinct.
- Generative operations explicitly allow zero/one/many events and correlate them. Suppression,
  multishot results, zero-copy lease return, queue-slot reclamation, and notification/work-completion
  separation cannot be collapsed by shared IDs.
- Prevention must reject notification-as-completion, completion-as-terminal/resource-return,
  resource-return-as-slot-return, and local-completion-as-delivery.
- Demand fusion is permitted only when it proves every consequence, scope, authority, participation,
  failure, progress, observability and bound. Primitive choice is fixed only when itself contractual.
- CPU synchronization does not imply persistence; wake does not publish; submission does not
  complete; local completion does not prove remote processing; storage completion is not durability.
- Exact device/control and Vulkan host/WSI paths retain their native labels, ranges, generations,
  availability/visibility and loss consequences rather than becoming CPU fences.
- “Happens-after” is inverse of a named relation. Nontransitive relations cannot be cached in a
  transitive clock. Vector clocks may cache only separately proved transitive projections and never
  invent source labels or replace target consistency.
- Projected edges retain exact canonical nodes, source path, scopes and profile proof. Trace equality
  is labelled partial-order equivalence modulo stable key renaming, not list or raw-clock equality.
  Quotients are total, non-inventing and acyclic; coalescing is named and preserves stream/label/
  payload/barriers; trace order is iff admitted observable source-path reachability, so isolated
  events and required order cannot be dropped.

## 12. Required proof-package inventory

Source: [§12 Required Proof Package](MEMORY_MODEL.md#12-required-proof-package).
Applicability is derived from the selected demand, reachable operations, profiles, claimed
properties, and failure paths. It is presently a mandatory review artifact, not a claimed mechanical
checker. Unselected features add no tax; selected claims bring their full transitive authority,
ordering, lifecycle, platform, validation, and prevention closure.

| Proof family | Required preserved result |
|---|---|
| Instruction descriptor fidelity | Every access/barrier is well formed and agrees with static description, target constraints, and the actual step. |
| Origin fidelity | Initial, instruction, platform, and device events have disjoint keys and only owner transitions/authority. |
| Binding-generation fidelity | Generative bind evolution, explicit aliasing, event-time live resolution, no stale revival/redirection, and exact hazard scope. |
| Bounds/provenance | Every emitted access is in-bounds, non-wrapping, aligned as required, and region-preserving. |
| Authority preservation | Every step preserves per-context authority and the global access invariant. |
| No ordinary race | Distinct threads cannot perform authorized conflicting ordinary accesses. |
| Atomic-mode safety | Registered atomics admit only approved atomic operations; mixed plain access and stale grants are impossible. |
| Architecture consistency | Every admitted x86/AArch64 execution satisfies the selected architecture model. |
| Emission/decoding | Exact instruction, relocation and layout fidelity; residual hardware semantics cited and differentially tested. |
| Atomic fidelity | Exact target width/alignment/type/order/success/failure and single-copy-atomicity premises. |
| CPU protocol synchronization | Each CPU release/acquire edge is instance/generation/event/read-from/RMW/target-proof backed. |
| Target relation refinement | Non-CPU native relations/scopes survive projection and cannot be manufactured through CPU witness types. |
| Consequence separation | Every path yields only profile-admitted consequences; all cross-kind escalations have failing controls. |
| Task/thread lifecycle | Spawn, terminal bundle, detach, one-shot join and root exit conserve all live resources without process claims. |
| Root/failure disposition | Graceful root closure is complete; abort is selected and resource-specific, not normal discharge or global invalidation. |
| Lock safety | Unique healthy or quarantined exceptional ownership, exact result transfer, recovery/handoff discipline, and auxiliary accounting. |
| Lock visibility | New guard observes the writes promised by its matched release under the target model. |
| Multi-lock/deadlock | Claimed order/deadlock property has a well-founded, acyclic, or other explicit protocol proof. |
| Mutex implementation refinement | Reachable representation/auxiliary states, lifecycle inverse, atomic transitions, linearization, payload, owner and progress refine the portable contract. |
| Synchronization-library refinement | RW-lock, condition-variable and semaphore profiles prove their own authority, wait, cancel, destruction, visibility and progress laws. |
| Parking-plan refinement | Exact wait object/value/retry/result/order/lost-wakeup; composite waits and spin progress separately proved. |
| Futex refinement | Private futex refines only the atomic address park/notify contract, adding no ordering edge. |
| Platform lifecycle | Linux, Windows and both bare-metal paths refine generic thread/PE transitions. |
| Handler-context safety | Exact checked call graph, interruption states, locality, nesting, result-specific return/resume/unwind/fatal resource effects, metadata, and self-deadlock control. |
| Device/domain fidelity | Exact memory attributes, device values/effects/order/completion, and no interrupt/control consequence escalation. |
| Trace fidelity | Total, non-inventing, acyclic labelled quotient with iff source-path reachability and stable-key equivalence. |
| One-thread preservation | Sequential proofs survive as the one-thread/one-PE specialization. |
| Progress | Only the precisely proved class under named eligibility, success, release/recovery, fairness and interference; cleanup liveness stays separate. |
| Prevention coverage | Every applicable defect class is rejected at the earliest sound structural, theorem, build, or external-oracle boundary. |

Safety and liveness remain separate. Terminating tests and fuel do not establish liveness.

### 12.1 Prevention-class registry

Also owned by [§12](MEMORY_MODEL.md#12-required-proof-package). A selected profile keeps one entry
per defect class or materially distinct trust boundary; one sound control may cover several clauses.
Structural defects use types/theorems/build gates, while emitted/native mutation is reserved for
external-oracle boundaries.

| Class | Mutations/unsound shortcuts that must fail | Owner status |
|---|---|---|
| Authority/provenance | Raw/stale bytes or IDs mint pointer, grant, guard, permit, or handle right. | M1/M4 or importing profile. |
| Lock/result accounting | Failed/cancelled acquire grants ownership; node is reused; cleanup counts as acquisition; release/destruction drops obligations. | M5-S plus implementation. |
| Wait/control | Wake publishes; unary waits fake composite atomicity; cross-platform wake results are fabricated. | M3/M6 adapter. |
| Interrupt/DMA/nonlocal control | Interrupt or handler entry implies completion/visibility/wake; context traits are widened; SEH outcomes are conflated; retired frames or metadata are lost. | M7 or selected async/device profile. |
| Reserved process/failure domain | Raw process IDs/handles retarget; wait equals join/reap/publication; local exit invalidates surviving external resources. | Deferred, only after selected post-M9 process capability. |
| Heterogeneous consequence | Submission/completion/delivery/persistence or target relations are conflated. | Owning GPU/I/O/RDMA/network/storage profile. |
| Trace projection | Nodes/edges are invented/dropped, labels/paths lost, or quotient creates self-edge/cycle. | M0/M8. |

## 13. Validation inventory

Source: [§13 Validation Matrix](MEMORY_MODEL.md#13-validation-matrix).

- x86 model-side validation is TSO enumeration with locked/fenced variants; emitted/native runs are
  Windows/Linux on native or hardware virtualization; bare metal validates startup, mutex counter,
  and credible-backend RAM litmus.
- AArch64 separately enumerates weak plain/acquire-release/barrier/exclusive outcomes, runs Linux on
  native/KVM, and validates PE startup/mutex/litmus on a credible backend.
- Hosted-process validation remains post-M9 with no current row or hidden acceptance dependency.
- Every observed hardware outcome must be allowed. Reliably observable allowed outcomes are stress
  witness floors, not flaky per-commit demands.
- Record histogram, seed, exact architecture profile, per-agent identity/features/topology,
  firmware/microcode when observable, backend/hypervisor, migration/affinity, and iteration budget.
- Only source-covered CPUs count as memory-model validated; other hardware reports functional-only.
- Timeout distinguishes hang/deadlock from forbidden outcome. External-oracle defect classes need a
  mutation that makes the session fail; structural defects should fail earlier. Harness freshness and
  worker protocol require independent protection.
- `ParkedMutex32` is the cross-target baseline but has target-specific code. Specialized mutexes and
  each litmus suite retain their own target-specific validation.

## 14. Stage and exit-criterion inventory

Source: [§14 Implementation Sequence and Exit Criteria](MEMORY_MODEL.md#14-implementation-sequence-and-exit-criteria).
M6 siblings and every `M2-B[p]` are independent exact profiles; completion never transfers to a
sibling. Bootstrap/TCB artifact evidence proves only the pinned transition, not opaque child code.

| Stage | Preserved deliverable and exit criterion | Current owner/evidence status |
|---|---|---|
| M0 | Thin open event/graph/projection envelope. x86, AArch64, and meaningless non-CPU sentinel round-trip exact identity/binding/location/labels/path/consequences; malformed/stale/forged/escalated cases fail. | Required future stage; §2 reports only partial access/event vocabulary. |
| M1 | Provenance, typed views, indexed authority/obligations, abstract relational boundaries, closed profile-registry shape, canonical normal forms and bounded automation. Unauthorized/stale/byte pointers and vacuous boundary evidence fail. | Required future stage; current boundary substrate is partial evidence, not closure. |
| M2-X | x86 WB/TSO, atomics/fences, exact bounded enumerator, selected-suite equality, sequential preservation, emission fidelity, silicon containment. | Required after gates/intake; no concurrent x86 machine currently claimed. |
| M2-A | AArch64 weak memory, acquire/release/barriers/exclusives, exact enumerator, Arm-suite equality, sequential preservation, emission fidelity, native containment. | Required after gates/intake; current descriptor vocabulary is incomplete. |
| M2-B[p] | One closed exact boundary profile with result subset, origin, admission, authoritative source/TCB, artifact link, physical/logical relations, save rules and prevention coverage. | Independently selected future closures; no substantive profile currently admitted. |
| M3 | One-process CPU logical-thread/PE scheduler, lifecycle, narrow parking and open composite/control seams; two-agent stepping and no process/heterogeneous conflation. | Required future stage. |
| M4 | Cross-thread partition and lifecycle transfer with global no-race, loans, terminal bundle, detach and one-shot join conservation. | Required future stage after M1/M3. |
| M5-S | Representation-independent mutex contract with stable core/auxiliary resources, extensible outcomes, owner identity, typed obligations and exact progress/refinement. | Required future stage after M4 and Decision 11. |
| M5-L | One pinned `ParkedMutex32` state machine/linearization/wait/retry/healthy/no-auxiliary specialization and precise progress or safety-only classification. | Library-specific future stage after portable contract and Decision 8. |
| M5-X / M5-A | Target realization and visibility for the same M5-L protocol under x86 / AArch64; specialized implementations keep the common refinement boundary. | Independent future stages after corresponding ISA. |
| M6-T[Linux] / M6-T[Windows] | Semantic hosted thread lifecycle, visibility, join, blocked/runnable, terminal bundle and graceful all-thread root accounting; Windows separately owns persistent object/handle/status/close. | Independent future profiles, no native claim by themselves. |
| M6-NX[Linux] / M6-NA[Linux] | Native Linux thread lifecycle and child-TID refinement; root uses `exit_group`, not thread-only exit; optional libc/async surfaces add exact closures only. | Independent exact ISA/boundary/lifecycle profiles. |
| M6-NX[Windows] | Native Windows thread/object lifecycle and root `ExitProcess`; closed call surface plus environment/TCB excludes forced stop/suspend or else exact abort/liveness disposition is selected; APC/SEH are conditional. | Independent exact boundary/lifecycle profile. |
| M6-X[Linux] / M6-A[Linux] | Exact private aligned 32-bit futex parking on x86 / AArch64 without thread-lifecycle claims. | Independent optional parking profiles. |
| M6-X[Windows] | Exact admitted `WaitOnAddress` width/lifetime/result/atomicity without lifecycle claims. | Independent optional parking profile. |
| M6-LX[Linux] / M6-LX[Windows] / M6-LA[Linux] | Target/library blocking integration with release-before-notify, lost-wakeup and spurious-return proofs; adapter remains open to other libraries. | Independent future integrations. |
| M7-X / M7-A | Two-agent boot handoff, `ParkedMutex32` counter, wait refinement, one device ordering/completion protocol, negative controls, backend honesty; selected calls/DMA/interrupts add only exact burdens. | Independent bare-metal future profiles. |
| M8 | Total/non-inventing acyclic trace quotient and bidirectional labelled-path fidelity modulo key renaming/transitive representation. | Required future integration. |
| M9 | Complete model, native lifecycle, parking/lock, both bare-metal, and trace validation matrix. | Final current-roadmap acceptance stage; hosted processes remain post-M9. |

Stage discipline is normative: common-interface changes cover both current ISAs or explicitly remain
design-only; profiles progress independently once dependencies close; each increment cites prevention
coverage; a stage completes only on its exit criterion, never representative examples.

## 15. Stop-and-design decision inventory

Source: [§15 Decisions Required Before Implementation](MEMORY_MODEL.md#15-decisions-required-before-implementation).

| Decision | Exact matter that must be accepted before implementation | Status / nonclaim |
|---|---|---|
| 1. AArch64 formal profile | Arm ARM edition/profile/shareability, errata disposition, matching official `cat`, and herd7 release/hash. | Open hard gate for M2-A. |
| 2. Common event representation | Stable thin target-indexed interchange, generative IDs, dynamic bindings/aliases, well-formed projection, labelled paths, consequence families, and exact finite-runner relation; exercise with real CPU projections and a semantically meaningless non-CPU sentinel. | Open hard gate for M0. Must not guess future queue/GPU/domain semantics or universalize CPU shapes/transitivity. |
| 3. Indexed authoring and boundary surface | Prevent arbitrary permission/obligation replacement; choose relational entry/result/freshness discipline; exact caller/loader establishment, target admission, artifact identity, closed profile registry, normal forms/automation, and elaboration budget. | Open hard gate for M1 and M2-B. M1 alone admits no concrete ABI/loader/syscall/handler/artifact. |
| 4a. Windows thread-object wait | Pin object lifetime, wait/status/timeout, selected abandonment, rights and close. | Independent M6-T/NX gate. |
| 4b. Windows address wait | Pin minimum OS and exact address comparison/timeout/error/wake behavior. | Independent M6-X gate; not implied by 4a. |
| 5. x86 AP startup | Choose verified trampoline versus declared/validated TCB blob. | Open M7-X gate. |
| 6. AArch64 startup | Choose PSCI conduit and QEMU/real-platform profile. | Open M7-A gate. |
| 7. Futex v1 errors | Pin supported returns and explicit unsupported timeout/signal/shared behavior. | Open Linux parking gate. |
| 8. `ParkedMutex32` protocol | Pin exact 32-bit states/transitions, linearization, waiter marking, expected value, release, wake, and retry. | Library-only M5-L gate. Competing protocols are not interchangeable; specialized locks decide separately. |
| 9. x86 vendor profile | Intel-only versus cited common Intel/AMD subset, hardware matrix, manuals, errata and dispositions. | Open M2-X gate; tests do not waive sources/errata. |
| 10. Scheduler seams | Pin unary parking, composite wait, target notification, interrupt/control, scheduler wake, platform result, authority, registration generation/cancellation, and which M3 seams instantiate. | Open M3 gate. No fabricated wake count or visibility. |
| 11. Mutex refinement seam | Pin core/aux split, owner/affinity, healthy/exception extension, recovery/poison/handoff, progress/fairness, cleanup-liveness separation, and destruction inverse. | Open M5-S gate. Specializations may omit features only while preserving open seams. |
| 12. Hosted processes | Remains deliberately unopened; after M9 only a selected consumer opens the smallest capability profile and its sources/closure/validation. | Deferred, not a current gate. Preserve thread/process/join/raw-ID negative boundaries. |
| 13. Async callable seam | Pin every selected IRQ/NMI/exception/signal/APC/trap/cancel context, locality/migration, all result/control outcomes, unwind metadata/artifact, masks/nesting/stacks, authority, allowed effects, reentrancy/order, cleanup/abort and progress bounds. | Conditional hard gate for every stage admitting such a surface. Safety cannot widen across contexts without refinement. |
| 14. Process-shared synchronization | Opens only with Decision 12 and a selected process-shared capability; private futex proves no robust/shared/recovery facts. | Deferred. Current obligation is only to keep M5-S's exceptional-result seam open. |

### 15.1 Stage-entry gate matrix

Also source-owned by [§15](MEMORY_MODEL.md#15-decisions-required-before-implementation).

| Entry | Required accepted decisions/intake before normative work |
|---|---|
| M0 | Decision 2. |
| M1 | Decision 3 including registry, freshness, normal forms, automation and resource budget. |
| M2-X | Decision 9 plus x86 §15.1 intake. |
| M2-A | Decision 1 plus full AArch64 §15.1 intake. |
| M2-B[p] | Decision 3, one closed exact registry entry, exact boundary intake, prevention coverage, and Decision 13 only if selected. |
| M3 | Decision 10. |
| M5-S | Decision 11 after M4 authority/obligation surface. |
| M5-L / inherited target realizations | Decision 8 after M5-S and before either architecture realization. |
| M6-T[Linux] | Linux lifecycle intake; Decision 13 only for selected async surfaces. |
| M6-T[Windows] | Decision 4a and lifecycle intake; Decision 13 only for selected extra async surfaces. |
| M6-NX/NA | Corresponding semantic lifecycle, ISA, exact boundary/native intake; async validation only when selected. |
| M6-X/A Linux | Decision 7, M3, ISA, syscall boundary and exact private-futex intake. |
| M6-X Windows | Decision 4b, M3, x86, call boundary and exact address-wait intake. |
| M7-X / M7-A | Decision 5 / 6, Decision 13, bare-metal/interrupt intake, and every selected boundary intake. |

No row is an exemption: the stage that first admits any call/root/start/callback/unwind/handler
closes its exact boundary intake, and every async surface closes Decision 13. Prototypes before a
gate are isolated, nonnormative, cannot fix public types/theorems or count as progress, and are later
discarded or rebased.

## 16. Reference-intake inventory

Source: [§15.1 Reference-intake gate](MEMORY_MODEL.md#151-reference-intake-gate).
The design document is not architectural ground truth. `references.json` must pin/hash the narrowest
authoritative sources before corresponding semantics. Hardware/QEMU observations validate but do not
replace contracts.

| Surface | Source-family and assumption content that must remain required |
|---|---|
| Boundary ABI/loading/linking | Exact selected psABI/PE/AAPCS/ELF revisions; syscall/exception rules; stack, probes and unwind; relocation/resolution/TLS/indirect calls/load generations; selected control-flow protection; source/TCB, nonvacuity, admission and artifact evidence for relational entry/fresh results. |
| x86-64 | Exact Intel, and AMD when eligible, manuals covering WB/TSO, locks/fences, memory types, startup and every applicable erratum/disposition. |
| AArch64 | Exact Arm ARM/profile/shareability/errata, official `cat`, and herd7 identities. |
| Linux hosted lifecycle | Exact kernel/UAPI/libc/man-pages for selected clone/thread lifecycle, child-TID, outcomes/publication, root versus thread exit, without importing process creation or parking. |
| Linux private parking | Exact private aligned 32-bit futex comparison/block, errors, mapping/lifetime, wake result and retry. |
| Windows hosted lifecycle | Exact thread creation/exit/object wait/status/rights/handle/result/publication/root accounting; base closed call surface and named environment/TCB exclude forced stop/APC/SEH or else exact selected dispositions apply. |
| Windows address parking | Exact minimum OS and address-wait widths, registration/lifetime, timeout/error/spurious and observable wake rules. |
| Deferred hosted processes | No current intake; after M9 only consumer-selected sources under Decision 12. |
| x86 bare metal | Intel startup/APIC plus selected platform/device specifications. |
| AArch64 bare metal | PSCI, exception level, GIC, translation/attributes, and selected platform/device specifications. |
| RISC-V future | Exact ISA/platform/extensions, formal RVWMO artifacts/tools, PPO/dependencies, fences, AMO/LRSC ordering and optional Ztso. |
| DMA/interrupt future | Exact OS/architecture/interconnect/IOMMU/controller/device revisions, coherence/direction, maintenance/barriers, generations, ownership, doorbells, routing/acknowledgement and separate completion/visibility. |
| Async callable contexts | Exact architecture/platform rules for every selected context/outcome, locality, unwind/handler metadata and emitted opcodes, masks/nesting/stacks/reservations, call surface, effects and failure cleanup. |
| Optimistic/reclamation future | Exact seqcount/seqlock and compiler/memory rules; separately exact RCU/hazard/epoch publication, protection, grace/quiescence, retirement/reclamation and progress. |
| WebAssembly threads future | Exact Core/embedding snapshot, atomic/racy profile, tearing, wait/notify, memory identity/grow, agent lifecycle, reentrancy, traps/termination/interruption and engine matrix. |
| SPIR-V/Vulkan future | Exact Vulkan/SPIR-V/tool/formal artifacts and errata; resource/binding/alias/descriptor/external memory, host coherency/ranges, WSI ownership/layout/sync/presentation/loss, and separation of API, presentation and shader relations. |
| WGSL/WebGPU future | Exact W3C snapshots, embedding/import/validation and device-loss/resource timeline. |
| `io_uring` future | Exact kernel/UAPI/liburing, ring ordering, selected operations/flags, consumption/results, multishot/zero-copy, independent notification/return/reclamation, generations, cancellation and operation effects. |
| libverbs/RDMA future | Exact rdma-core/provider/transport/QP, DMA premises, MR/MW and key generation, alias/lifetime, CQ notification versus completion, buffer return, remote observation and persistence. |
| Network/IPC/storage future | Selected protocols/OS contracts, shared identity, cache/persistence, loss/failure/crash/recovery assumptions. |
| Hosted synchronization extensions | Exact distinct robust/abandoned contracts; Linux futex2/`futex_waitv`; Windows multiple-object waits; result-indexed ownership/cancel; and exact MCS/qspinlock sources with node provenance, affinity, nesting and progress assumptions. |
| CPU synchronization libraries | Exact selected RW-lock/CV/semaphore contracts for authority, predicate/wake, permits, cancellation, destruction, exceptional outcomes and progress. |
| Linux rseq future | Exact kernel/libc/ABI/codegen/registration/migration/signal/membarrier/commit-abort/restart/fallback; process interactions only if separately selected. |
| Direct user scheduling future | Exact available ABI and races, accounting, generations, control versus publication; historical proposals are not contracts. |

## 17. Requirement-closure checklist

Source: [§16 Requirement Closure](MEMORY_MODEL.md#16-requirement-closure).

| Need | Source-owned closure point to preserve |
|---|---|
| x86 TSO / AArch64 weak memory | §5.1 M2-X / §5.2 M2-A. |
| Shared contract | §§3--4, §5.3, M0. |
| Relational boundaries/fresh results/artifacts | §3, M1 seam plus every applicable exact M2-B and lifecycle/handler realization. |
| Provenance/borrowing/pointer fields | §6, M1/M4, including §§6.1.1--6.2. |
| Donation/join | §6.4, M3/M4. |
| Hosted processes/shared robust recovery | Explicitly post-M9 under §§6.5/8.1, Decision 12 and `FUTURE_PROCESS_MODEL.md`. |
| Mutex invariant/implementation/release obligations | §7, M5-S/L/X/A and §7.3. |
| Linux/Windows hosted lifecycle and waits | §§8--9 with independently selected semantic, native and parking profiles. |
| Async context safety | §8.4, selected M7 or hosted async profile. |
| Bare-metal SMP/device ordering | §10, M7-X/A and §4. |
| Causal traces | §11, M8. |
| Litmus/silicon validation | §13, M9. |
| Safety/liveness separation | §§8 and 12. |

The source's final completeness rule is preserved verbatim in meaning: a concurrency feature is
incomplete unless it identifies its authority rule, architecture ordering rule, lifecycle effect,
obligation effect, and validation vehicle.

## 18. Pass-1 disposition

This inventory deliberately makes no judgment about how a property-directed lowering design should
represent any row. No current declaration, historical ledger, or passing control is promoted into a
successor contract here. Before any migration or implementation, an independently reviewed later
pass must prove that every applicable row above is retained without semantic weakening and that
every explicitly deferred row remains deferred rather than accidentally closed or silently dropped.

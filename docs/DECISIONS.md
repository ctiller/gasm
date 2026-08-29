# Architectural and Technical Decisions

This document consolidates the genuine technical and architectural decisions for `gasm`, distilled from the historical decision records (ADRs). It filters out transient workflow, agent-orchestration, and repository-management rules to focus entirely on the system's structural invariants.

## 1. Vision and Scope
- **The Validation Gate is the Product (ADR 0001)**: Concrete implementation code is discardable. Programs are formal boundaries on what *must* be true. The validation gates that enforce these boundaries are the core product of the repository.
- **Target Systems and Scale (ADR 0016, 0022)**: Designed for game engines, operating systems, web/gRPC servers, and databases at a scale of millions to tens of millions of lines of code. This scale explicitly mandates that decomposition machinery is prioritized alongside model growth. Graphics and networking are prioritized architectural paths.
- **Demand-Driven Model Growth (ADR 0008)**: Models remain deliberately incomplete and grow only on concrete demand. Every increment must be differentially validated in the same change that introduces it, before any other component depends on it.

## 2. Proof Architecture and Tractability
- **Modular Decomposition for Universal Equivalence (ADR 0003)**: Monolithic whole-program proofs are intractable. Universal correctness is instead achieved via modular decomposition: per-routine contracts, step lemmas, and composition rules that assemble into whole-program theorems.
- **DSLs as the Unit of Proof Leverage (ADR 0011)**: Domain Specific Languages (DSLs) are the preferred unit of proof. Prove the language in total once, so the proof applies to every program in that language.
- **Canonical Observation Standard (ADR 0014)**: Observables in equivalence proofs are strictly bounded to syscall-boundary effects (up to a declared coalescing congruence) and contract-footprint memory. Internal structures and timing are explicitly unobservable.
- **`read` as the Universal Binder (ADR 0015)**: To prevent domain-shrinking and hardcoded-output evasions, every input operation (like `read` or `recv`) must bind an arbitrary result. Contracts must be universally parametric over any returned data (including partial reads and EOF).

## 3. Security, Capabilities, and Consistency
- **Memory Capabilities Mandate (ADR 0004)**: Memory access without an attached, in-scope capability proof must fail to assemble. These capabilities simultaneously act as frame conditions for modular proof composition.
- **`native_decide` Restricted to Exhaustive Finite Domains (ADR 0002)**: `native_decide` can only discharge verification obligations if the proposition is universally quantified over its entire, finite domain. Single-instance ground checks are merely regression tests, not verification evidence.
- **Connection Theorems for Duplication (ADR 0005)**: Redundant encodings of the same model-level fact may coexist only when linked by a kernel-checked connection theorem that proves their equivalence.

## 4. Modeling, Fuzzing, and Governance
- **Performance Model as a Strategic Asset (ADR 0006)**: Performance models are parametric cost functions with concrete coefficients (e.g., `5·N² + 3·N + 293` cycles), not bare asymptotic classes. They are backed by hardware-fuzzed calibration data.
- **Findings Become Gates (ADR 0009)**: The ratchet law: every review or fuzz finding must terminate in a mechanical prevention of its class. The mandated preference hierarchy is: unrepresentable by construction > kernel-checked theorem > build-failing linter > oracle control vectors.
- **TCB Ledger and Differential Fuzzing (ADR 0013)**: Trust is chosen, not discovered. Everything trusted-but-unprovable (hardware, APIs, external tools) is explicitly tracked in a TCB ledger, and every entry must have a differential fuzzer validating the model against the real system.
- **Model-Debt Record (ADR 0030)**: Hardware and OS semantics that are knowingly omitted or
  simplified (e.g., caches, store buffers, PCIe bandwidth, FPU state) must be explicit in
  `docs/TECHNICAL_NOTES.md` or the owning canonical subsystem document so they cannot silently
  distort performance rankings or correctness claims.

## 5. Memory, Ownership, and Concurrency

The detailed normative design and staged exit criteria are in `docs/MEMORY_MODEL.md`. These are the
durable decisions future implementations must preserve:

- **Three proof levels keep demands reusable**: high-level code states communication,
  synchronization, resource and consequence demands; an ISA-independent domain plan chooses the
  mutex, graphics, async-I/O, RDMA, protocol or storage architecture; target realizations finally
  prove that plan against each ISA, OS, device, provider and transport. No level may silently assume
  a guarantee owned by a lower or different level.
- **One common event graph, separate ISA consistency models**: x86-64 uses a WB/TSO operational
  model; AArch64 uses a pinned official Arm weak-memory profile. Neither architecture is the
  other's fallback semantics.
- **Value-, range-, and origin-faithful events**: dynamic accesses record values, access role,
  domain, and explicit atomic class; reads-from is byte/range-granular for Normal memory, initial
  writes are explicit, platform/device events are owned by their transition rules, and barrier
  semantics retain ordering/completion/scope information.
- **Bindings are dynamic and generational**: a resolved reference carries its target key and
  generation, logical object, rights and location/backing footprint. Bind/unbind/rebind and alias
  transitions invalidate stale resolution witnesses; each asynchronous resource operand captures
  its generation at the profile-declared snapshot/consumption event and never reinterprets a reused
  fd, handle, slot, `rkey`, IOVA, descriptor or address afterward.
- **Authority precedes ordering**: provenance and the resource algebra decide whether an access is
  authorized; the architecture model then decides which authorized concurrent executions are
  allowed. Vector clocks replace neither layer.
- **Borrowing is indexed and generational**: exclusive ownership, frozen-owner fragments,
  exact-token read loans, instance-scoped atomic grants, causal donation, and result-indexed join
  returns are tracked by closed indexed transitions rather than duplicable token values. In v1,
  pointer bytes recover a registered typed view, not provenance or authority by themselves.
- **Locks separate contract from representation**: contenders share atomic authority for a stable
  implementation-defined core while admitted queue locks may borrow generative contender/per-agent
  auxiliary nodes; one fresh lock instance owns the disjoint protected region; and each acquired
  generation carries result- and owner-indexed guards and obligations. The planned verified
  `ParkedMutex32` library is the preferred healthy-only, thread-affine, no-auxiliary default, not the
  definition of a mutex. Specialized libraries prove their core/auxiliary resources, encoding,
  results/recovery, owner policy, atomic transitions, parking and exact progress class. First-profile
  CPU synchronization is justified by an explicit release/acquire witness tied to concrete event
  keys, not by relabelling generic loads or stores; non-CPU profiles keep their native relations.
  Destruction is the checked inverse of initialization and returns every auxiliary loan.
- **Address parking is not publication**: Linux futex and Windows
  `WaitOnAddress`/`WakeByAddress*` operations refine a narrow park-if-equal/notification adapter and
  create scheduler causality only. Composite wait sets and interrupts use separate result-indexed
  seams. Release publication precedes address notification; memory visibility comes from the
  target-proved atomic protocol rather than scheduler wake itself. A selected device/interconnect
  profile may prove ordered interrupt delivery, but handler entry is not universally completion,
  visibility, or scheduler wake.
- **Consequences do not collapse**: acceptance, consumption, effect completion, terminality, result
  publication/observation, notification, resource return, queue-slot reclamation, remote delivery,
  acknowledgement and persistence are independently typed. A profile theorem may relate them; a
  shared operation ID or event name may not.
- **Observable causality retains its source**: every projected trace order carries a profile-selected
  labelled source-path witness, whether it came from CPU program order, scheduler control, GPU/API
  execution, device/interrupt delivery, a transport acknowledgement, or persistence. Equivalence is
  over induced reachability between observable quotient nodes, not one primitive-edge encoding or a
  CPU-only vector clock.
- **Thread/task lifecycle is explicit and process lifecycle is separate**: M3 covers one hosted
  address space or one bare-metal machine with logical threads/PEs; independently completed
  M4 proves cross-thread authority partition and sealed terminal-bundle/join conservation;
  independently completed M6-T[Linux]/M6-T[Windows] profiles refine hosted threads;
  the M6-P family introduces generative processes, address spaces, images, namespaces, status and
  process objects through independently selectable Linux M6-PL and Windows M6-PW profiles; and
  M6-PS is an optional POSIX/Linux process-shared robust-synchronization semantic profile, with
  independently completed M6-PS-X/A target realizations. A
  fresh one-shot `JoinRight` is a task/thread contract: spawn commits donated authority and a
  release publication before the child becomes runnable, and successful join observes actual
  termination through a proved acquire publication and returns only the child's sealed terminal
  bundle. Detach requires an empty join-owned bundle or an explicit transfer to a named live
  recipient whose cleanup remains tracked. No dead or terminating process is a magic resource sink.
- **Process identity, failure and handles remain typed**: process termination/status observation,
  POSIX status consumption/reaping and Windows process-object lifetime are distinct consequences;
  none is `JoinRight`. Every process belongs to an explicit failure domain, and graceful or forced
  termination applies the selected survivor, close, invalidation, owner-death, orphan/reparent,
  cancellation, leak or indeterminate transition per resource instead of globally invalidating a
  world or pretending normal discharge. Handle/object derivation distinguishes local entries,
  underlying objects, rights, generations and close obligations across copy/alias, move,
  attenuation, inheritance, name import and object-specific transfer.
- **ABI and lifecycle boundaries bind logical identity relationally**: an ordinary caller/link proof
  or loader/platform start transition establishes the exact physical-entry-to-arguments/binding/live-
  world tuple. Fresh erased result identities and authority changes live in a relational exit/after-
  world binding unless a functional projection is proved to be non-authorizing physical scalar data.
  Concrete target admissibility and artifact identity remain mandatory before execution is certified.
  Independently selected M2-B profiles own one exact ordinary-call, syscall, loader-root or handler
  entry kind; proving one proves none of the others. Hosted lifecycle semantics, their native
  M6-NX/M6-NA realization, and optional M6-X/M6-A address parking are separate certificates, so a
  consumer takes only the pieces its reachable implementation uses.
- **Asynchronous and restricted-lifecycle callability are profile-indexed**: interrupt, exception,
  NMI, signal, APC, trap and cancellation handlers do not inherit an ordinary thread's callable
  surface; each proves its exact authority, nesting/mask/reentrancy, stack,
  blocking/allocation/fault/host-call, cleanup and progress bounds. At-fork callbacks, restricted
  fork-child code and vfork-borrowed children are separate lifecycle phases with their own callable
  operations, authority, allowed exits and failure transitions rather than handler-stack fields.
  When selected, SEH resume, continue-search/propagation and nonlocal unwind are distinct outcomes;
  unwind accounts for intervening frames and cleanup handlers through exact emitted metadata rather
  than masquerading as ordinary return or fatal termination.
- **Proof burden follows the mechanically derived applicability closure across all proof domains**:
  functional, ABI/link, memory/provenance, effect/observable, lifecycle, security, performance and
  liveness claims all use the same rule. Selected targets,
  reachable effects/operations, advertised guarantees and failure paths determine the required proof
  set. Unselected profiles and stronger unclaimed properties impose no obligation; selected claims
  bring all transitive safety/platform duties. Generic proofs are reused once, while specialized
  implementations prove only their refinement delta and stronger advertised properties.
- **Whole-program verification is certificate composition, not a monolithic replay**: the
  applicability closure yields the required certificate keys; artifact/emission, export/link,
  provider/runtime, entry, admissibility, ABI-context, and behavioral certificates are proved at
  their owning reusable layers and indexed by the same final artifact/platform/capability selection.
  One general composition rule constructs `VerifiedProgram` exactly when every applicable key is
  present and coherent. Optional unselected features add no key; reachable features cannot evade one.
- **Bare metal is a first-class two-architecture target**: x86 AP/LAPIC and AArch64
  PSCI-or-spin-table/GIC paths implement the same lifecycle/lock contracts through distinct startup
  and device-order rules. Startup notification alone is not RAM synchronization.
- **Validation tells the truth**: formal model outcome sets are normative; hardware observations
  must be contained in them. TCG-only runs validate function/boot behavior, not weak-memory claims.

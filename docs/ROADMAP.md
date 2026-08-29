# Gasm Technical Roadmap & Future Designs

This document summarizes future work. Canonical subsystem documents own detailed dependencies and
acceptance criteria; historical task identifiers are not an active coordination surface.
Only `docs/MEMORY_MODEL.md`'s M0–M9 names are implementation-stage identifiers. The profile names
below are descriptive workstreams, not a second stage namespace.

## 1. Graphics & Compute (Spikes 6 & 7)
* **Headless Compute (Spike 6):** Future expansion for headless compute execution patterns.
* **Windowed Swapchain (Spike 7):** Design for multi-loop reactive contracts and swapchain integration.
* **Heterogeneous event-graph seam:** Generalize CPU thread/address-range events to hierarchical
  execution agents, target-indexed locations/references, scopes, and typed relation labels before
  shader or multi-device proofs depend on M0's shape.
* **SPIR-V/Vulkan synchronization profile:** A DSL retaining Vulkan execution and memory
  dependencies, storage-class-parameterized relations, availability/visibility, host/device
  domains, resource ownership, barrier participation, and RAW/WAR/WAW hazards without flattening
  them into one vector clock. Model sparse bind/unbind/rebind generations and physical-backing
  alias/overlap separately from logical resource/descriptor identity and lifetime.
  The host-memory refinement must distinguish coherent from noncoherent mappings and prove the exact
  `nonCoherentAtomSize` range/alignment and availability/visibility effects of
  `vkFlushMappedMemoryRanges` and `vkInvalidateMappedMemoryRanges`; neither host cache maintenance
  operation is a generic CPU fence.
* **Vulkan WSI/presentation profile (Spike 7):** Keep this independently gated from the current
  compute-only profile. Pin surface/swapchain and acquired-image generations, recreation, image
  layout and queue-family/presentation-engine ownership, acquire/present semaphore and fence
  relations, queue completion versus presentation acceptance versus display visibility,
  frame-availability backpressure, and out-of-date/suboptimal/surface-loss/device-loss outcomes.
  Select and ingest the exact platform WSI extensions and window-system contracts before adding
  public types or claims.
* **WGSL/WebGPU refinement:** After exact WGSL/WebGPU reference intake, prove the constrained WGSL
  atomics/barriers and WebGPU content/device/queue timelines refine the shared heterogeneous graph;
  do not treat WGSL as merely another SPIR-V spelling.
* **Shader progress and blocking-synchronization profile:** Do not automatically admit the CPU
  mutex contract as a shader-invocation primitive. Pin invocation, subgroup, and workgroup topology,
  dynamic-uniformity and barrier-participation rules, residency assumptions, and every independent-
  forward-progress guarantee. The portable default rejects a spinning or blocking lock whose
  release may depend on an invocation or workgroup not guaranteed to execute; a specialized shader
  lock is admissible only through a target/device-specific safety, visibility, no-deadlock, and
  progress proof. Include divergent-barrier and lock-holder-starvation negative controls.
* **FP Kernel DSL:** Deterministic Shader Profile for floating-point kernel definitions.
* **Vulkan Host Model:** Formal modeling of Vulkan host behaviors and GPU differential-validation harnesses for rigorous state verification.

## 2. Networking & OS Capabilities (Spike 4)
* **Networking Buildout:** Implementing a "real socket model" alongside a verified reactive network contract.
* **Common asynchronous-operation profile:** Generative operation identities and captured dynamic
  binding generations; separately typed publication, acceptance, consumption, effect completion,
  terminality, result publication/observation, notification, resource return, and profile-defined
  capacity/queue-entry reclamation; zero/one/many event correlation; cancellation; and in-flight obligations shared by
  kernel and device queues. No consequence constructor implies another without a profile theorem.
* **Linux `io_uring` profiles:** Prove the SQ and CQ release/acquire protocols separately
  from operation execution; model links, multishot and zero-copy completions, SQPOLL/shared-ring
  serialization, fixed/provided resources, cancellation races, and the exact event that returns each
  buffer or slot. Provided-buffer publication grants the kernel selection authority. An observed
  buffer-return CQE transfers exactly the profile-defined buffer or completed segment to the
  application; `IORING_CQE_F_BUF_MORE` exposes only the completed segment while retaining the buffer
  for further kernel consumption, so whole-buffer reuse or re-provisioning requires the operation-
  specific final-return witness. Account for ordinary, multishot, bundled, and incremental-
  consumption CQEs; pin `IORING_FEAT_NODROP`, CQ-overflow backlog/flush and legacy lost-CQE behavior,
  backpressure, completion ordering, and the effect of an unobservable completion on reclamation
  and terminal accounting. A profile that permits CQE loss after overflow cannot claim exact
  completion-driven reclamation: it is rejected or retains the affected resources as unrecoverably
  outstanding under an explicit failure outcome. Model completion suppression and zero-copy result
  CQEs separately from later notification CQEs that return buffer leases; distinguish SQ-head
  consumption and CQ-head reclamation from operation terminality. A registered-resource update can
  publish a new binding while an accepted operation still holds the captured old generation; any
  later tag CQE/resource-release event retires that old generation rather than re-resolving the slot.
* **Hosted process lifecycle profiles:** Add the independently gated M6-PL POSIX/Linux and M6-PW
  Windows refinements of the common M6-P-family system topology for
  generative process/image/address-space/namespace identities; fork/clone/vfork, exec/spawn or
  `CreateProcess`; terminality, status observation, POSIX reaping and Windows persistent process
  objects; PID/handle reuse; parent/reaper/job relations; and resource-specific failure-domain
  dispositions. Thread `JoinRight` remains a high-level task contract rather than an OS process wait.
* **IPC and handle/object derivation profiles:** Model shared-memory object identity across address
  spaces and message IPC. Keep portable process-shared futex/robust owner-death/recovery semantics in
  optional M6-PS, with independently completed M6-PS-X/A target realizations. Distinguish local descriptor/handle entries,
  intermediate open descriptions/provider objects, underlying objects, rights and close obligations;
  prove copy/alias, move, attenuation, inheritance, name import and object-specific transfer with
  result-indexed source disposition and failure atomicity. `SCM_RIGHTS` normally creates a fresh
  receiver descriptor alias while retaining the sender entry; equal numeric entries across
  namespaces prove nothing.
* **Transport profiles:** TCP byte-stream and datagram flow identities, local completion versus
  delivery versus application acknowledgement, connection shutdown and reset, retransmission and
  explicit failure/recovery assumptions.
* **libverbs and RDMA transport profiles:** PD/MR/MW/QP/CQ/SRQ resource authority,
  work-request and completion lifetimes, QP/transport ordering, local DMA, remote placement versus
  observation, provider/transport variants, and optional persistent/global-flush consequences.
  Keep CQ notification/event acknowledgement separate from retrieved work completions and buffer
  return. MR/MW/`rkey` and address bindings are generational; an `rkey` received as bytes never
  manufactures authority without an explicit typed import protocol.
* **Durability and recovery:** Separate logical file/page-cache visibility, device I/O
  completion, stable persistence, crash cuts, and recovery; pin filesystem, mount, device-cache, and
  flush semantics before claiming a durable-before edge.
* **Win32 API Differential Harness:** Formal models for OS capabilities, including OS-level
  read/write files and differential validation. Completion-port profiles keep immediate operation
  success/terminality separate from notification emission, including selected modes that suppress a
  completion-port packet on synchronous success.
* **Security Contracts:** Implementation of constant-time/secrecy contract classes to prevent timing attacks, and verified defenses against stack buffer overflows.

## 3. Multithreading & SMP (Spike 8)
* **Three-level synchronization architecture:** Keep high-level communication/synchronization
  demands separate from ISA-independent domain plans (mutex, Vulkan/WebGPU, `io_uring`, verbs,
  protocol or storage) and from final ISA/platform/device realizations. Dynamic execution graphs
  retain each profile-selected labelled source path in the observable trace rather than projecting
  only CPU program/scheduler edges.
* **Two architecture models:** x86-64 WB/TSO with store buffers and locked operations; AArch64
  weak memory with acquire/release, barriers, and exclusive monitors.
* **Hosted concurrency:** Keep semantic thread/object lifecycle, native lifecycle/ABI realization,
  and optional address parking as independently consumable certificates. Windows thread-object
  lifecycle must not depend on `WaitOnAddress`; Linux native creation/join must not depend on a
  process-private futex unless it uses one. Keep unary address parking narrow; add a
  separate future composite-wait profile for futex2 wait vectors and Windows wait-any/wait-all with
  atomic registration and result-indexed ownership/interruption effects.
* **Portable mutex extension profiles:** The initial thread-affine healthy-only `ParkedMutex32`
  library must advertise and prove the Gate-11-selected progress class, or remain explicitly
  safety-only; this roadmap does not choose that class in advance. Future POSIX robust and Windows abandoned-mutex
  refinements retain their distinct ownership/recovery outcomes. Queue-lock implementations use a
  stable lock core plus acquisition- or per-agent-contributed nodes with generative publication,
  handoff, cancellation, affinity/nesting and exact-return obligations; MCS and qspinlock are not
  misdescribed as fixed instance-owned footprints.
* **Future CPU synchronization libraries:** Give read/write locks, condition variables and
  semaphores separate contracts rather than treating them as mutex aliases. RW locks need
  reader/writer authority, upgrade/downgrade and preference/fairness rules; condition variables need
  atomic mutex-release/registration, predicate-loop, spurious-wake, cancellation and reacquisition
  rules; semaphores need bounded generative permits, cross-thread post, overflow, cancellation,
  visibility, destruction and progress rules. Pin exact POSIX/Windows contracts before public types.
* **Linux restartable-sequence profile:** Model one registered logical thread, CPU/memory-
  concurrency-domain observation, critical range, final commit instruction and kernel abort redirect.
  Pre-commit effects are not rolled back and must be restart-safe or quarantined; repeated aborts need
  a named fallback/progress proof. Pin the kernel, UAPI, libc/`librseq`, code-generation and signal/
  migration behavior before implementation.
* **Direct user-scheduling profile:** Treat Google's `SwitchTo` and proposed `FUTEX_SWAP` as
  non-upstream prior art. Any implementation requires an exact available ABI and separately proves
  scheduler handoff, races, accounting, control causality, memory publication and resource lifetime;
  it neither changes logical thread identity nor transfers a thread-affine mutex guard by itself.
* **Two bare-metal SMP paths:** x86 AP/LAPIC startup and AArch64 PE/PSCI-or-spin-table startup,
  each including device-memory ordering and honest emulator/silicon classification.
* **Interrupt/exception contexts:** Model handler stacks on execution agents, entry and distinct
  ordinary-return, resumable-continuation, search/propagation, nonlocal-unwind/cleanup,
  non-returning exec/immediate-exit and fatal outcomes; model masks/priorities/nesting, save/restore
  and reservation invalidation; suspend rather than transfer
  interrupted-thread authority; grant explicit handler authority; and reject locks that can
  self-deadlock against the interrupted context. Keep CPU exceptions, device interrupts, hosted
  signals, Wasm traps and embedding cancellation as distinct profiles/outcomes.
* **DMA coherency, interrupt, and ownership profiles:** Before any hosted or bare-metal DMA proof, pin
  the CPU/device coherency domain, mapping/IOMMU contract, transfer direction, cache-line isolation,
  ownership transitions, target cache-maintenance operations and completion point, barrier scopes,
  MMIO-doorbell ordering, interrupt-controller delivery/acknowledgement, and distinct completion and
  visibility evidence. State consequences rather than a universal instruction recipe; Linux DMA
  APIs and each bare-metal architecture profile supply separate refinements. An exact MSI/device
  profile may provide ordered delivery, but handler entry is never globally equated with completion,
  DMA visibility, or scheduler wake.
* **Future WebAssembly shared-memory profile:** Keep current Wasm single-agent/unshared. Pin the
  exact Core threads snapshot and embedding; sequentially consistent atomics, specified racy/tearing
  behavior, `memory.atomic.wait32`/`wait64`, notify, multi-memory identity, main-agent blocking
  eligibility and asynchronous embedding APIs; include concurrent shared `memory.grow`, atomic size,
  failure/zero-initialization and embedding buffer/view-length behavior; validate against each
  admitted engine profile.
* **Future RISC-V/RVWMO profile:** Pin an exact unprivileged ISA/platform profile and formal RVWMO
  artifact; model preserved program order, dependencies, `FENCE` predecessor/successor `I`, `O`,
  `R`, and `W` sets, AMO and LR/SC `.aq`/`.rl` semantics—including SC success/failure and the failed-
  SC no-store case—and Ztso only as a separately selected extension. `.aq`/`.rl` order only the
  memory-or-I/O address domain accessed by the annotated atomic; cross-domain ordering requires the
  appropriate `FENCE`, with address-domain classification pinned by the execution-environment and
  physical-memory-attribute profile.
* **Validation:** Architecture-specific litmus suites, the standard-library `ParkedMutex32` lock
  counter, blocking-path tests, and proof-linked negative controls.

The canonical design and dependency sequence are `docs/MEMORY_MODEL.md`; Spike 8 is the
end-to-end validation vehicle in `docs/SPIKES/SPIKE8_MULTITHREADING.md`.

## 4. Borrowing & Memory Semantics
* **Provenance and indexed authority:** Generative regions, provenanced pointers, temporal read
  loans, causally delivered donation, result-indexed join returns, and a global access-mode
  invariant separating ordinary-exclusive, frozen/read-loan, and registered-atomic regions.
* **Relational ABI/boundary entry and exit:** Connect physical entry state to exact logical arguments,
  binding and live authority/obligation world with an entry-origin relation, not a function that
  reconstructs erased provenance or generations from bits. A caller/link proof establishes ordinary
  calls; loader/platform transitions establish roots, thread/process starts and handlers. Bind exit
  results/outcomes relationally whenever fresh erased identity is involved, or prove any functional
  projection is limited to non-authorizing physical scalars. The selected target proves complete
  physical admissibility for its entry/exit kind, and artifact identity connects the theorem to
  emitted bytes. M1 owns only the abstract seam; independently selectable M2-B[p] certificates own
  exact ordinary-call, syscall, loader-root and handler profiles, and proving one must not burden or
  certify another. Converge the ABI-context implementation on this split; do not connect it to
  `Callable` or `VerifiedProgram` until the applicable whole-program caller-or-loader link theorem
  exists.
* **Lock invariants and obligations:** An implementation-independent mutex contract separates
  atomic synchronization-representation authority from exclusive protected-region ownership;
  result-indexed guards and typed must-release obligations are shared by a preferred verified
  `ParkedMutex32` library and by specialized proved representations, including packed-state variants.
* **Memory hooks:** Keep every dynamic access linked to the static descriptor, authority check,
  architecture model, and measurement surface.
* **Validated optimistic snapshots:** Add seqcount/seqlock only through a profile-specific
  speculative access mode whose contents cannot affect committed results, contract-visible output,
  authority transitions, pointer dereference, or irreversible external effects before validation.
  Successful validation commits only the permitted scalar/copied snapshot; pointers need an
  independent lifetime witness, and the Linux seqcount-only profile forbids pointer-bearing data.
  Pin writer serialization, sequence generation and wrap, barriers, width/tearing assumptions, and
  the profile's scheduling, preemption/interruption, and retry/progress premises; do not weaken the
  ordinary data-race-free authority invariant.
* **Safe memory reclamation profiles:** Model RCU, hazard pointers, and epoch reclamation as
  separate typed protection and reclamation protocols. Protection associates a typed published
  pointer/reference with a live `RegionId` and yields a guard-bound provenance/lifetime witness, not
  general field-access authority. Reuse requires the complete ordered profile history: removal and
  retirement before the applicable RCU grace period; visible hazard publication, source
  revalidation, retirement, and a later scan proving no matching protection; or retirement in an
  epoch followed by every relevant participant's required advance/quiescence. None reconstructs
  provenance from raw bytes.

## 5. Performance Calibration & Cost Functions
* **Model Calibration:** Developing a staged model calibration lifecycle using an RDTSC harness.
* **Parametric Cost Models:** Moving towards composable cost views and parametric cost functions to scale analysis (e.g., "Zlib to infinity").

## 6. Proving & Continuous Validation
* **Codec Soundness:** Driving universal roundtrip soundness proofs for foundational codecs (Zlib, PNG, Gzip).
* **Continuous Fuzzing:** Establishing a checked-in, deterministic continuous fuzzing corpus alongside mutation coverage tooling.
* **Verification Infrastructure:** Expanding axiom gate closure coverage, TCB (Trusted Computing Base) ledgers, and trust/fail-open auditing.
* **Trust-repair exit gate:** The build is green, allowlist debt is removed, every implemented spike
  has one universal `VerifiedProgram`, and those proofs are factored as reference examples of the
  general certificate-composition law. Reusable artifact, export/link, provider/runtime, entry,
  admissibility, ABI-context, and behavior certificates live at their owning layers; spike modules
  prove only applicability-derived local deltas. A monolithic or target-duplicated proof does not
  satisfy this milestone even if it typechecks.
* **Task Automation:** Future implementation of dependency tooling for work sequencing.

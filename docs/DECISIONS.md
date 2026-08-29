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

- **One common event graph, separate ISA consistency models**: x86-64 uses a WB/TSO operational
  model; AArch64 uses a pinned official Arm weak-memory profile. Neither architecture is the
  other's fallback semantics.
- **Value-, range-, and origin-faithful events**: dynamic accesses record values, access role,
  domain, and explicit atomic class; reads-from is byte/range-granular for Normal memory, initial
  writes are explicit, platform/device events are owned by their transition rules, and barrier
  semantics retain ordering/completion/scope information.
- **Authority precedes ordering**: provenance and the resource algebra decide whether an access is
  authorized; the architecture model then decides which authorized concurrent executions are
  allowed. Vector clocks replace neither layer.
- **Borrowing is indexed and generational**: exclusive ownership, frozen-owner fragments,
  exact-token read loans, instance-scoped atomic grants, causal donation, and result-indexed join
  returns are tracked by closed indexed transitions rather than duplicable token values. In v1,
  pointer bytes recover a registered typed view, not provenance or authority by themselves.
- **Locks separate contract from representation**: contenders share atomic authority for an
  implementation-defined synchronization representation; one fresh lock instance owns the
  disjoint protected region; and each successful generation carries a matched guard and must-release
  obligation. The planned verified `ParkedMutex32` library is the preferred cross-platform default,
  not the definition of a mutex. Specialized libraries may use another protocol or pack additional
  state into the atomic object only by proving their encoding, atomic transitions, parking behavior,
  and refinement to the same contract. Synchronization is justified by an explicit release/acquire
  witness tied to concrete event keys, not by relabelling generic loads or stores. Failed acquire
  transfers nothing, and destruction is the checked inverse of initialization.
- **Parking is not publication**: Linux futex and Windows `WaitOnAddress`/`WakeByAddress*`
  operations refine park-if-equal/wake and create scheduler causality only. Release publication
  precedes notification; memory visibility comes from the target-proved atomic release/acquire
  protocol rather than from wake itself.
- **Lifecycle is explicit**: spawn commits donated authority and a release publication before the
  child becomes runnable; a fresh one-shot `JoinRight` observes actual termination through an
  acquire publication and returns only the child's sealed terminal bundle. Detach requires an empty
  join-owned bundle or a named process sink, and thread exit and process exit are distinct.
- **Bare metal is a first-class two-architecture target**: x86 AP/LAPIC and AArch64
  PSCI-or-spin-table/GIC paths implement the same lifecycle/lock contracts through distinct startup
  and device-order rules. Startup notification alone is not RAM synchronization.
- **Validation tells the truth**: formal model outcome sets are normative; hardware observations
  must be contained in them. TCG-only runs validate function/boot behavior, not weak-memory claims.

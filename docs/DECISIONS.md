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
- **Model-Debt Ledger (ADR 0030)**: Hardware and OS semantics that are knowingly omitted or simplified (e.g., caches, store buffers, PCIe bandwidth, FPU state) must be explicitly tracked in a debt ledger to prevent silent performance mis-rankings or correctness gaps.

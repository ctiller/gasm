# Gasm Technical Roadmap & Future Designs

This document summarizes future work. Canonical subsystem documents own detailed dependencies and
acceptance criteria; historical task identifiers are not an active coordination surface.

## 1. Graphics & Compute (Spikes 6 & 7)
* **Headless Compute (Spike 6):** Future expansion for headless compute execution patterns.
* **Windowed Swapchain (Spike 7):** Design for multi-loop reactive contracts and swapchain integration.
* **Synchronization DSL:** A Domain-Specific Language designed around the Vulkan memory model, handling happens-before and RAW (Read-After-Write) hazards.
* **FP Kernel DSL:** Deterministic Shader Profile for floating-point kernel definitions.
* **Vulkan Host Model:** Formal modeling of Vulkan host behaviors and GPU differential-validation harnesses for rigorous state verification.

## 2. Networking & OS Capabilities (Spike 4)
* **Networking Buildout:** Implementing a "real socket model" alongside a verified reactive network contract.
* **Win32 API Differential Harness:** Formal models for OS capabilities, including OS-level read/write files and differential validation.
* **Security Contracts:** Implementation of constant-time/secrecy contract classes to prevent timing attacks, and verified defenses against stack buffer overflows.

## 3. Multithreading & SMP (Spike 8)
* **Common concurrency semantics:** Dynamic execution graphs, a generic thread scheduler, and
  correct projection of program happens-before into causal traces.
* **Two architecture models:** x86-64 WB/TSO with store buffers and locked operations; AArch64
  weak memory with acquire/release, barriers, and exclusive monitors.
* **Hosted concurrency:** Windows lifecycle/waits and Linux thread lifecycle plus process-private
  futex wait/wake on x86-64 and AArch64.
* **Two bare-metal SMP paths:** x86 AP/LAPIC startup and AArch64 PE/PSCI-or-spin-table startup,
  each including device-memory ordering and honest emulator/silicon classification.
* **Validation:** Architecture-specific litmus suites, a portable lock counter, blocking-path
  tests, and proof-linked negative controls.

The canonical design and dependency sequence are `docs/MEMORY_MODEL.md`; Spike 8 is the
end-to-end validation vehicle in `docs/SPIKES/SPIKE8_MULTITHREADING.md`.

## 4. Borrowing & Memory Semantics
* **Provenance and indexed authority:** Generative regions, provenanced pointers, temporal read
  loans, causally delivered donation, result-indexed join returns, and a global access-mode
  invariant separating ordinary-exclusive, frozen/read-loan, and registered-atomic regions.
* **Lock invariants and obligations:** Atomic lock-word authority separated from exclusive
  protected-region ownership; result-indexed guards and typed must-release obligations.
* **Memory hooks:** Keep every dynamic access linked to the static descriptor, authority check,
  architecture model, and measurement surface.

## 5. Performance Calibration & Cost Functions
* **Model Calibration:** Developing a staged model calibration lifecycle using an RDTSC harness.
* **Parametric Cost Models:** Moving towards composable cost views and parametric cost functions to scale analysis (e.g., "Zlib to infinity").

## 6. Proving & Continuous Validation
* **Codec Soundness:** Driving universal roundtrip soundness proofs for foundational codecs (Zlib, PNG, Gzip).
* **Continuous Fuzzing:** Establishing a checked-in, deterministic continuous fuzzing corpus alongside mutation coverage tooling.
* **Verification Infrastructure:** Expanding axiom gate closure coverage, TCB (Trusted Computing Base) ledgers, and trust/fail-open auditing.
* **Task Automation:** Future implementation of dependency tooling for work sequencing.

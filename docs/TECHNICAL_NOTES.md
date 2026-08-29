# Technical Notes & Architectural Debts

This document consolidates genuine technical insights, open architectural debts, and formal verification notes extracted from project tracking files.

## 1. Formal Verification & Trusted Computing Base (TCB)
- **Universality via Modular Decomposition**: The system uses per-routine contracts and composition rules, avoiding whole-program monolithic proofs.
- **DSLs as the Unit of Proof Leverage**: Total theorems are proven at the DSL level (e.g., assembly, bit-reader) to apply to all inhabitants, making proof costs sublinear.
- **`native_decide` & `bv_decide` Trust Tiers**: Allowed only for propositions exhaustively quantified over finite domains. `bv_decide` shares the same trust class as `native_decide` (compiled execution trusting an external SAT solver like CaDiCaL) and is not kernel-checked.
- **Emitter Last Mile Gap**: There is no proposition linking logical `executable.textBytes` to `serializeInstructions`. `traceEquivalence` walks the AST list, and `emit` writes the bytes, leaving the serialization unlinked.
- **Gate Principles (Law 13)**: Every fuzz/review finding must terminate in mechanical prevention of its whole class (preference: unrepresentable by construction > build-time theorem > build-failing linter > oracle control vectors).
- **Axiom Gate Coverage**: `Tools/CheckGatesAxioms.lean` enumerates tracked build-closure modules and standalone-scans modules outside the umbrella-import baseline, so unimported built modules are no longer invisible to the axiom gate (`docs/REVIEW.md` §4.1.1).

## 2. Machine & OS Model Debts
- **Performance Model**: 
  - Entirely lacks memory hierarchy modeling (no L1-L3 latency, cache miss costs, or frequency).
  - Dependency chains and critical-path costs are unmodeled; nominal cycle counts are derived from flat uniform-spread approximations of port pressure.
  - Lacks system-level transport models (PCIe, memory transfers), preventing accurate CPU vs. GPU placement cost functions.
- **Memory Model**:
  - Represents memory as a total function without faults, permissions, canonicality, or alignment checks. Binding with `MemoryPermissions` capability machinery is required.
  - x86 has no atomics, `LOCK`, fences, store buffers, concurrent machine, or WB/TSO ordering model.
  - AArch64 has an addressing descriptor but no instruction-level memory-event requirement, weak-
    memory execution model, barriers, exclusive monitors, or concurrent machine.
  - Current permission and obligation records are duplicable values and `BlockM.set` can replace
    them; they do not enforce provenance, borrowing, lock guards, or must-release obligations.
  - The consolidated resolution and dependency gates are `docs/MEMORY_MODEL.md` §§4–14.
- **OS/Environment Inventions**: 
  - `ReadFile` supports bounded short reads, but the file hooks still lack realistic handle,
    error, pipe, and console semantics; stdout and stderr are not distinguished faithfully.
  - Sockets are completely invented (no blocking, 100% successful I/O), and OS error states (`GetLastError`) are unmodeled.
  - `VirtualAlloc` returns a constant address.
- **Wasm**:
  - Width-checked signed and unsigned LEB128 decoders and their roundtrip theorems exist in
    `Gasm/Targets/Wasm/LEB128.lean`; remaining Wasm debts are tracked in `docs/TARGETS/WASM.md`.

## 3. Graphics & GPU Architectural Notes
- **Observation Standard**: GPU rendering output (`readbackPixels`) must carry actual pixel data, not just an audit trace of a readback event.
- **Synchronization Model**: Must use a happens-before/synchronizes-with model (mapped onto VectorClock machinery), not a resource-layout FSM. RAW (Read-After-Write) hazards must be actively modeled.
- **Floating-Point Determinism**: Cross-driver bit-exact equality is impossible. Requires a "Deterministic Shader Profile" (integer/basic FP, NoContraction) where equality holds, utilizing ULP-tolerance refinement everywhere else.
- **Read-Binder**: Graphics proofs must quantify over all valid input buffer contents and interleavings, rather than asserting pointwise correctness on a fixed gradient.
- **Capabilities (Law 11)**: Requires descriptor hand-off with temporal release fences, bounding shader memory accesses to fail at assembly if violated.

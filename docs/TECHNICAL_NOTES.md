# Technical Notes & Architectural Debts

This document consolidates genuine technical insights, open architectural debts, and formal verification notes extracted from project tracking files.

## 1. Formal Verification & Trusted Computing Base (TCB)
- **Universality via Modular Decomposition**: The system uses per-routine contracts and composition rules, avoiding whole-program monolithic proofs.
- **DSLs as the Unit of Proof Leverage**: Total theorems are proven at the DSL level (e.g., assembly, bit-reader) to apply to all inhabitants, making proof costs sublinear.
- **`native_decide` & `bv_decide` Trust Tiers**: Allowed only for propositions exhaustively quantified over finite domains. `bv_decide` shares the same trust class as `native_decide` (compiled execution trusting an external SAT solver like CaDiCaL) and is not kernel-checked.
- **Emitter Last Mile Gap**: There is no proposition linking logical `executable.textBytes` to `serializeInstructions`. `traceEquivalence` walks the AST list, and `emit` writes the bytes, leaving the serialization unlinked.
- **Gate Principles (Law 13)**: Every fuzz/review finding must terminate in mechanical prevention of its whole class (preference: unrepresentable by construction > build-time theorem > build-failing linter > oracle control vectors).
- **Axiom Gate Blind Spot**: The current `CheckGatesAxioms` tool operates on the import closure, making unimported modules (like `Emit.lean` variants) invisible. Needs filesystem-level enumeration.

## 2. Machine & OS Model Debts
- **Performance Model**: 
  - Entirely lacks memory hierarchy modeling (no L1-L3 latency, cache miss costs, or frequency).
  - Dependency chains and critical-path costs are unmodeled; nominal cycle counts are derived from flat uniform-spread approximations of port pressure.
  - Lacks system-level transport models (PCIe, memory transfers), preventing accurate CPU vs. GPU placement cost functions.
- **Memory Model**: 
  - Represents memory as a total function without faults, permissions, canonicality, or alignment checks. Binding with `MemoryPermissions` capability machinery is required.
  - No atomics, `LOCK`, fences, or TSO ordering model implemented, despite early documentation claims.
- **OS/Environment Inventions**: 
  - `ReadFile` and `WriteFile` hooks model ideal disk I/O (no short reads, stdout identical to stderr), lacking pipe/console semantics. 
  - Sockets are completely invented (no blocking, 100% successful I/O), and OS error states (`GetLastError`) are unmodeled.
  - `VirtualAlloc` returns a constant address.
- **Wasm**: 
  - The LEB128 decoder is missing, meaning the Wasm emission round-trip is unstatable and unprovable.

## 3. Graphics & GPU Architectural Notes
- **Observation Standard**: GPU rendering output (`readbackPixels`) must carry actual pixel data, not just an audit trace of a readback event.
- **Synchronization Model**: Must use a happens-before/synchronizes-with model (mapped onto VectorClock machinery), not a resource-layout FSM. RAW (Read-After-Write) hazards must be actively modeled.
- **Floating-Point Determinism**: Cross-driver bit-exact equality is impossible. Requires a "Deterministic Shader Profile" (integer/basic FP, NoContraction) where equality holds, utilizing ULP-tolerance refinement everywhere else.
- **Read-Binder**: Graphics proofs must quantify over all valid input buffer contents and interleavings, rather than asserting pointwise correctness on a fixed gradient.
- **Capabilities (Law 11)**: Requires descriptor hand-off with temporal release fences, bounding shader memory accesses to fail at assembly if violated.

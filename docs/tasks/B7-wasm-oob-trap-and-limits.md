---
id: B7
title: Enforce WebAssembly trap semantics on out-of-bounds memory access and validate memory limits
status: ready
blocked_on: ""
after: [TC2]
related: [TC9, TC20]
bar: ""
track: wasm
priority: 8.6
priority_set: 2026-08-28T02:00:00Z
design: inline
design_review: waived-mechanical
date: 2026-08-28
---

# B7: Enforce WebAssembly trap semantics on out-of-bounds memory access and validate memory limits

## Context

Sourced from `MODEL_DEBT.md` **B7 (Wasm out-of-bounds accesses do not trap)** and **B8 (`Limits.max` and `memory_grow` failure are dead)**, ranked High in correctness-model debt and flagged by `docs/tasks/TC9-fail-open-audit.md` as an urgent sibling item:

1. **Silent Memory Expansion on OOB Write**:
   In `Gasm/Targets/Wasm/Semantics.lean:92-97`:
   ```lean
   def writeMem8 (mem : ByteArray) (addr : Nat) (val : UInt8) : ByteArray :=
     if addr < mem.size then
       mem.set! addr val
     else
       let padding := ByteArray.mk (Array.mkArray (addr - mem.size) 0)
       (mem ++ padding).push val
   ```
   When an instruction writes past linear memory bounds, `writeMem8` appends zero-padding and grows the byte array. Under the official WebAssembly 1.0 specification (Wasm Spec §4.5.3), any memory access beyond the allocated linear memory bound **must trap**.
   Furthermore, because `evalInstr` implements `.memory_size` as `s.memory.size / 65536` (`lines 350-352`), an out-of-bounds write corrupts subsequent `memory_size` queries, making the divergence observable in program logic.

2. **OOB Read Returns Zero Rather Than Trapping**:
   In `Gasm/Targets/Wasm/Semantics.lean:63-64`:
   ```lean
   def readMem8 (mem : ByteArray) (addr : Nat) : UInt8 :=
     if addr < mem.size then mem.get! addr else 0
   ```
   Reading beyond linear memory returns 0 instead of causing a runtime trap.

3. **`Limits.max` Ignored and `memory_grow` Never Fails**:
   `Limits.max` (`Gasm/Targets/Wasm/Types.lean:35`) is never consulted during module evaluation. `memory_grow` (`Semantics.lean:353-358`) always succeeds and never returns `-1` (the Wasm error sentinel for memory allocation failure).

### Why this is a live soundness gap
The Wasm differential fuzzer (`Fuzzable.lean:136-158`) generates memory operations only on statically constrained, in-bounds addresses (offsets 16, 64 in page 1), making this bug structurally invisible to differential testing against Node/V8. Any gasm-verified Wasm routine that accidentally performs an out-of-bounds access will succeed in gasm's in-Lean simulator but crash with an unhandled `RuntimeError: memory access out of bounds` when executed on real engines.

## Deliverables & acceptance criteria

- **Model Traps on Memory Accesses**:
  Update `WasmMachineState` to record trap state (e.g. `trapped : Bool := false` or an explicit `TrapReason` enum), and update `readMem8`, `writeMem8`, `load8_u`, `store8`, etc. in `Gasm/Targets/Wasm/Semantics.lean` to set `trapped := true` when `addr >= mem.size`, halting execution rather than silently padding memory.
- **Enforce Page Allocation & Limits in `memory_grow`**:
  Check `Limits.max`. If growing by the requested pages exceeds `max` (or the 64KiB page ceiling $2^{16}$ pages = 4GiB for Wasm32), push `(-1 : Int32)` onto the stack without growing memory.
- **Differential Negative Control Vectors**:
  Add differential tests in `test_spike_wasm` / `wasm_fuzzer` that deliberately attempt out-of-bounds loads and stores, proving that gasm's simulator and the Node.js / V8 oracle agree on trapping behavior.
- `lake build` and `scripts/run_gates.py --quick` pass cleanly.

## Pointers

- `Gasm/Targets/Wasm/Semantics.lean:60-100` (`readMem8`, `writeMem8`), `:325-360` (`memory_size`, `memory_grow`).
- `Gasm/Targets/Wasm/Types.lean:30-40` (`Limits`, `MemoryType`).
- `MODEL_DEBT.md` §B7, §B8.
- `docs/tasks/TC9-fail-open-audit.md` (identifying B7 as sibling debt).

## Notes

- 2026-08-28: Task created following comprehensive codebase security audit finding silent memory growth on OOB writes in `Gasm/Targets/Wasm/Semantics.lean:92`.
- 2026-08-28 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 8.0 → 8.6. The owner's
  "checked models" clause (alongside "no axioms, strong verification") names this task directly:
  `docs/ORACLE_DEBT.md` Part 4 flags that every Wasm-target grandfathered/finite-forall proof in the
  allowlist (Spike1/2/3/5 Wasm entries) is currently a proof about a model this task documents as
  non-conformant to the real WebAssembly spec — an axiom-free proof of the wrong model is not the
  trustable state the owner described. `docs/tasks/PA12-wasm-trap-guard-and-leb128-witness.md` and
  `docs/tasks/PA15-fibonacci-loop-invariant-induction.md` are
  `related` to this task for exactly that reason (not hard `after` edges, since neither routine they
  touch performs an out-of-bounds access today).

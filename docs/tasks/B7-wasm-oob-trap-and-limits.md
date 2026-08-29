---
id: B7
title: Enforce WebAssembly trap semantics on out-of-bounds memory access and validate memory limits
status: done
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
- 2026-08-27: **done.** `WasmMachineState` gained a `memMax : Option UInt32` field
  (`Semantics.lean`); `writeMem8` no longer zero-pads/grows on an out-of-bounds address (it is now
  a total no-op there, matching `readMem8`'s existing style) and the OOB decision moved to
  `evalInstr`'s own `.i32_load`/`.i32_load8_u`/`.i64_load`/`.i32_store`/`.i32_store8`/`.i64_store`
  cases, which now implement the spec's exact reduction-rule inequality (`i + ao.offset + N/8 >
  |mems[x].bytes|` → trap, `wasm-exec-instructions#memory-instructions`) and set `trapped := true`
  instead of reading/writing. `memory_grow` now checks `memMax` (threaded from the module's
  declared `Limits.max` via a new `WasmModule.memoryMaxPages` field, `Linker.lean`) and an
  additional Wasm32 address-space ceiling (2^16 pages), pushing the `-1` sentinel and leaving
  memory untouched when either bound would be exceeded, per the spec's `memory.grow`
  non-determinism note ("Failure MUST occur if the referenced memory instance has a maximum size
  defined that would be exceeded"). Nine new differential `WasmDiffCase`s
  (`Gasm/Targets/Wasm/SemanticsFuzzer.lean`, "Out-of-Bounds Access & Memory-Limit Coverage"
  section; documented in `docs/TARGETS/WASM_ORACLE_HARNESS.md#9-out-of-bounds-and-memory-limit-fuzz-coverage`)
  fuzz addresses at the exact boundary, one/several bytes past it (straddling, for the 32/64-bit
  widths), far past it, and at `0xFFFFFFFF`, plus `memory.grow` against a declared `Limits.max`
  (both the success and mandatory-failure sides) and against the implicit no-declared-max ceiling.
  `lake exe wasm_fuzzer` (all cases): 76 passed, 0 failed, 0 skipped, 2835 vectors, exit 0.
  RED/GREEN control performed by temporarily restoring the exact pre-fix `writeMem8`/load-store/
  `memory_grow` bodies: the 6 new OOB load/store cases and `memory_grow_exceeds_declared_max` then
  FAIL against the unchanged host oracle (exit 1) — `memory_grow_exceeds_declared_max` reports
  `Model=i32 5, Host=i32 1` (model wrongly grew to 5 pages past a declared max of 4; the real
  engine correctly refused and stayed at 1) — and `memory_grow_exceeds_hard_ceiling`'s huge-delta
  vector against the reverted model additionally attempts a multi-hundred-terabyte
  `List.replicate` allocation rather than failing fast, an aggravating resource-exhaustion
  consequence of B8 beyond the correctness mismatch itself. Restoring the fix returns the suite to
  76/76 green. No `sorry`, no new axioms, no new `native_decide` use. `Stdlib/`/`Spikes/` audit: no
  code depends on the old permissive behavior — no Stdlib/Spike Wasm code touches
  `WasmMachineState`/`evalInstr`/`readMem8`/`writeMem8` directly (Spikes emit real `.wasm` binaries
  run on external engines, which always trapped correctly); `Gasm/Targets/WASI/ABI.lean`'s
  `wasiHostCall` does call `readMem32`/`writeMem32` directly (bypassing `evalInstr`'s new
  instruction-level trap check entirely, since it isn't dispatched through `.i32_load`/
  `.i32_store`), but `wasiHostCall` is not currently wired into any executing spike/test/fuzzer
  (grep-confirmed: no caller besides its own definition) — flagged as a pre-existing, separate gap
  for whenever WASI gets its own execution harness, not a regression this fix introduces or an
  in-scope fix for B7/B8.
- 2026-08-28: **the flagged `wasiHostCall` gap above is closed.** Following the owner's memory-hook
  generalization question (`docs/MEMORY_HOOK.md` §12), `Gasm/Targets/Wasm/MemoryCell.lean` seals
  `WasmMachineState.memory` behind a `private`-constructor `WasmMemory` cell, mirroring
  `Gasm/Targets/X86_64/MemoryCell.lean`'s `X86_64Memory` seal: the raw `ByteArray` is no longer a
  directly-typed field, and every read/write anywhere in the tree (`evalLeafInstr`'s six memory
  cases in `Semantics.lean`, and `wasiHostCall`'s `fd_read`/`fd_write`/`sock_recv`/`sock_send` in
  `ABI.lean`) now goes through this module's checked, `Option`-returning accessors, which trap
  (`trapped := true`, pre-call state otherwise unmutated) rather than silently clipping or raw
  `ByteArray.set!`-ing past the end of memory. The bypass this note flagged is now structurally
  unrepresentable, not merely absent because nothing calls it yet. See `docs/MEMORY_HOOK.md` §12.3
  for the full mechanism and its verification (build + `wasm_fuzzer`/`validate_spike_wasm`/
  `test_spike1_wasm` before/after).

/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import Gasm.Core.Arch
import Gasm.Core.Types
import Gasm.Effects.Trace
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.MemoryCell

namespace Gasm.Targets.Wasm

open Gasm.Core
open Gasm.Effects

/- REF: wasm-exec-instructions#memory-instructions -/
/-- A finite resource refusal made by the execution platform.  This is distinct from a Wasm
    trap: `memory.grow` reports the refusal to guest code as `-1`, while the platform trace keeps
    the reason so a verified whole-program contract cannot erase an allocation failure. -/
inductive WasmResourceFailure where
  | memoryPages (requestedPages : Nat) (availablePages : Nat) : WasmResourceFailure
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-exec-runtime#values -/
/-- Runtime typed value representation on the operand stack and locals. -/
inductive WasmVal where
  | i32 : UInt32 → WasmVal
  | i64 : UInt64 → WasmVal
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-exec-runtime#configurations -/
/-- Pure machine state for the WebAssembly runtime interpreter. -/
structure WasmMachineState where
  stack            : List WasmVal := []
  locals           : List WasmVal := []
  -- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -- `WasmMemory` (MemoryCell.lean) is the
  -- sealed cell; this field can only be read/written through `WasmMem`'s checked, trap-signaling
  -- API (`WasmMem.read8/32/64`, `write8/32/64`, `readBytes`/`writeBytes`, and the bulk
  -- `ofBytes`/`zero`/`grow`/`toBytes` construction/observation entry points) -- no other function
  -- in the tree can touch these bytes, closing the raw-`ByteArray.set!`/unchecked-`readMem32`
  -- bypass `wasiHostCall` used before this change (`docs/MEMORY_HOOK.md`'s
  -- closing note).
  memory           : WasmMemory   := WasmMem.empty
  -- REF: wasm-exec-runtime#memory-instances -- "It is an invariant of the semantics that the
  -- length of the byte sequence, divided by page size, never exceeds the maximum size of
  -- memtype." `memMax` (in 64 KiB pages, matching the Wasm `mem.grow`/`Limits.max` unit) is that
  -- declared maximum for this machine's linear memory, threaded through from the module's
  -- `MemType`/`Limits` (`Types.lean`) at instantiation time; `none` means no maximum was
  -- declared (B8: previously this bound existed in `Limits.max` but was never consulted by
  -- `memory_grow` at all -- see that instruction's case in `evalInstr` below). Defaults to
  -- `none` so every existing state-literal (`{}`, `{ stack := ... }`, ...) built before this
  -- field existed keeps behaving exactly as it did (an unconstrained memory), not a silent
  -- behavior change.
  memMax           : Option UInt32 := none
  -- Set exactly when `memory.grow` is refused by the platform's finite page capability.  It is
  -- sticky for the invocation: guest code receives Wasm's `-1` result, but an enclosing WASI
  -- execution must still expose the resource outcome rather than mistake later recovery code for
  -- a successful unbounded allocation.
  resourceFailure  : Option WasmResourceFailure := none
  stdin            : ByteArray    := ByteArray.empty
  stdinPos         : Nat          := 0
  -- F1 (Law 9 root fix): raw octet strings, not `String`s -- see
  -- `Gasm.Effects.TraceState.incomingRequests`.
  incomingRequests : List ByteArray := []
  trapped          : Bool         := false
  exitCode         : Option UInt32 := none
  events           : List AnyEvent := []
  -- REF: wasm-exec-runtime#administrative-instructions -- fuel-conversion note (see
  -- `defaultWasmFuel`/`WasmRunResult` below): once the fuel-bounded interpreter core
  -- (`evalInstrMatch`/`evalInstrs`/`evalLoop`) genuinely runs out of fuel, its own return type
  -- (`WasmRunResult`, an `Except`) already makes that outcome structurally impossible to confuse
  -- with a completed run at that layer. This field exists ONLY for the handful of legacy,
  -- non-`Except`-returning convenience wrappers (`evalInstr`, `stepWasm`, `runWasmFunction`) that
  -- collapse a `WasmRunResult` back down to the pre-fuel `WasmMachineState × ControlSignal`/
  -- `WasmMachineState` shapes those call sites (the differential fuzzer, spike helper functions)
  -- were written against -- it is the one place fuel-exhaustion becomes "just a flag," and it is
  -- kept structurally parallel to `trapped` (a distinct, dedicated bit that no existing code path
  -- sets or clears for any other reason) precisely so a caller checking it cannot mistake fuel
  -- running out for either a trap or a genuine normal completion. No load-bearing whole-program
  -- equivalence theorem in this codebase reads this field: those go through `runWasiTraceState`'s
  -- un-collapsed `WasmRunResult`, each proven (`#guard`) never to hit `.error` at all.
  fuelExhausted    : Bool         := false
  deriving Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Replaces only host-supplied input streams. All guest-observable machine components and the
    current stream position are preserved. -/
def WasmMachineState.withExternalInputs (state : WasmMachineState)
    (stdin : ByteArray) (requests : List ByteArray) : WasmMachineState :=
  { state with stdin := stdin, incomingRequests := requests }

@[simp] theorem WasmMachineState.withExternalInputs_stack
    (state : WasmMachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).stack = state.stack := rfl

@[simp] theorem WasmMachineState.withExternalInputs_trapped
    (state : WasmMachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).trapped = state.trapped := rfl

@[simp] theorem WasmMachineState.withExternalInputs_exitCode
    (state : WasmMachineState) (stdin : ByteArray) (requests : List ByteArray) :
    (state.withExternalInputs stdin requests).exitCode = state.exitCode := rfl

/- REF: wasm-exec-runtime#stack -/
/-- Branch or return control flow signal during structured instruction evaluation. -/
inductive ControlSignal where
  | next : ControlSignal
  | br   : Nat → ControlSignal
  | ret  : ControlSignal
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-exec-runtime#stack -/
/-- Pops a 32-bit integer from the operand stack. -/
def popI32 (s : WasmMachineState) : UInt32 × WasmMachineState :=
  match s.stack with
  | .i32 v :: rest => (v, { s with stack := rest })
  | _ => (0, s)

/- REF: wasm-exec-runtime#stack -/
/-- Pops a 64-bit integer from the operand stack. -/
def popI64 (s : WasmMachineState) : UInt64 × WasmMachineState :=
  match s.stack with
  | .i64 v :: rest => (v, { s with stack := rest })
  | _ => (0, s)

/- REF: wasm-exec-runtime#stack -/
/-- Pushes a typed value onto the operand stack. -/
def pushVal (val : WasmVal) (s : WasmMachineState) : WasmMachineState :=
  { s with stack := val :: s.stack }

-- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -- the raw `readMem8`/`readMem32`/
-- `readMem64`/`writeMem8`/`writeMem32`/`writeMem64` helpers that used to live here (operating on
-- a bare `ByteArray`, total/silently-permissive on out-of-bounds addresses) are retired: they were
-- exactly the shape `Gasm/Targets/WASI/ABI.lean`'s `wasiHostCall` could call directly to bypass
-- `evalInstr`'s trap check (`docs/MEMORY_HOOK.md`'s closing note). Their
-- replacements, `WasmMem.read8/32/64`/`write8/32/64` (`MemoryCell.lean`), are `Option`-returning
-- (never silently permissive) and operate on the sealed `WasmMemory` cell, so the only way to
-- touch linear-memory bytes anywhere in the tree is through them.

/- REF: wasm-exec-runtime#administrative-instructions -/
/-- **Fuel bound for the structurally-recursive Wasm interpreter core (`evalInstrMatch`/
    `evalInstrs`/`evalLoop` below).** Converting that group from `mutual partial` to fuel-based
    structural recursion on an explicit `Nat` (following `Gasm/Targets/X86_64/Semantics.lean`'s
    `runProgramTraceWithLoops` shape) is what makes the group have real defining equations at all
    -- `partial def`s compile to an `opaque` constant with none (confirmed via `#print evalInstrs`
    before this change; see `spike1_wasm_canonical_effect_trace_equivalence`'s prior docstring in
    `Spikes/Spike1Hello/Wasm/Equivalence.lean` and `evalInstr_trapped_next` in
    `SemanticsFuzzer.lean` for the two places this previously blocked a proof outright), while a
    real WebAssembly `loop` must still be able to not terminate, so SOME bound is unavoidable for
    totality. `100000000` (100 million) is chosen generously relative to every actual program this
    codebase runs the interpreter over -- the largest, Spike 2's iterative Fibonacci, loops at most
    90 times (`test_spike2_wasm`'s "all 90 Fibonacci numbers"), and every spike's compiled module is
    under 2.2KB (`validate_spike_wasm`'s byte counts) -- and is cheap regardless of how it compares
    to real usage: fuel is consumed one unit per interpreter step actually taken (see `evalInstrs`),
    so the KERNEL reduction cost of a `decide`/`rfl` proof over a short-running program tracks the
    actual step count, never this nominal ceiling (`Nat` literals reduce via the kernel's built-in
    GMP-backed arithmetic, not unary `Nat.succ` peeling). Every spike's own `runWasiTraceState` call
    is proven, not merely assumed, never to exhaust this bound -- see the `#guard
    !(runWasiTraceState ...).isError` checks alongside each spike's `Equivalence.lean`. If any of
    those ever start failing as new spikes/programs are added, THAT is the finding to report (per
    docs/EQUIVALENCE_PROOFS.md#11-the-definition-of-observation-canonical-equivalence-standard's
    anti-vacuity stance) -- raising this constant to make a failing check pass again is exactly the
    move this docstring warns against. -/
def defaultWasmFuel : Nat := 100000000

/- REF: wasm-exec-runtime#administrative-instructions -/
/-- **Outcome of one fuel-bounded run through the interpreter core.** `.ok (s, sig)` is a genuine
    stopping point reached within budget -- exactly what the old `mutual partial` group
    unconditionally returned (trapped or not, distinguished as before via `s.trapped`; a `.next`/
    `.br _`/`.ret` signal exactly as before). `.error s` is fuel exhaustion, carrying the partial
    machine state observed at the instant fuel reached zero. Modeled directly on `Except` rather
    than folding a boolean into `WasmMachineState` (the stop-reason analysis in
    `docs/MEMORY_HOOK.md` §12.5 diagnoses this as a soundness gap in the sibling
    `Gasm/Targets/X86_64/Semantics.lean`'s `runProgramTraceWithLoops`, which
    returns `[]` for fuel-out, "no instruction at rip", AND a clean fault alike) so that a caller
    pattern-matching on the OUTCOME itself -- not a field reachable only by first assuming the run
    completed -- cannot mistake "ran out of fuel" for "ran to completion" no matter which
    projection they reach for first. The pre-fuel external wrappers (`evalInstr`, `stepWasm`,
    `runWasmFunction`) still collapse this back to their historical unwrapped shapes for caller
    compatibility (see their own docstrings for exactly what is preserved and what is
    best-effort); `runWasiTraceState` (`Gasm/Targets/WASI/ABI.lean`) is the one whole-program entry
    point that returns this type uncollapsed, and is what every load-bearing equivalence theorem in
    this codebase is proven never to see `.error` from. -/
abbrev WasmRunResult := Except WasmMachineState (WasmMachineState × ControlSignal)

def WasmRunResult.withExternalInputs (stdin : ByteArray) (requests : List ByteArray) :
    WasmRunResult → WasmRunResult
  | .error state => .error (state.withExternalInputs stdin requests)
  | .ok (state, signal) => .ok (state.withExternalInputs stdin requests, signal)

/- REF: wasm-exec-runtime#administrative-instructions -/
/-- Convenience check for whether a `WasmRunResult` is the fuel-exhausted outcome, named for
    readability at `#guard`/proof call sites (`.isOk`/`isError`-style helpers are not derived
    automatically for `Except`). -/
abbrev WasmRunResult.isError (r : WasmRunResult) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

/- REF: wasm-exec-instructions#instructions -/
/-- Evaluation for every WebAssembly instruction EXCEPT the three structured control-flow forms
    (`.block`/`.loop`/`.if_else`) that recurse back into the fuel-bounded `mutual` group below --
    deliberately kept as an ordinary, non-recursive, non-`mutual` `def` (needs no `fuel` parameter
    at all) so its equations are trivially available to any tactic without touching the recursive
    core. `evalInstrMatch` dispatches `.block`/`.loop`/`.if_else` itself and delegates every other
    instruction here unchanged; the `.block _ _`/`.loop _ _`/`.if_else _ _ _` arms below are
    therefore dead in practice (never reached by that dispatch) and exist only so this match stays
    exhaustive over `WasmInstr` -- they return `(s, .next)`, matching this function's own catch-all
    for any other not-yet-modeled instruction, exactly as the pre-fuel-conversion `evalInstrMatch`
    did for both. Bodies below are byte-for-byte unchanged from the pre-fuel-conversion
    `evalInstrMatch`. -/
private def evalLeafInstrRaw (instr : WasmInstr) (s : WasmMachineState)
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmMachineState × ControlSignal :=
      match instr with
      | .unreachable => ({ s with trapped := true }, .next)
      | .nop => (s, .next)
      | .i32_const v => (pushVal (.i32 v) s, .next)
      | .i64_const v => (pushVal (.i64 v) s, .next)
      | .drop =>
        match s.stack with
        | _ :: rest => ({ s with stack := rest }, .next)
        | [] => (s, .next)
      | .select_op =>
        let (c, s1) := popI32 s
        match s1.stack with
        | val2 :: val1 :: rest =>
          let chosen := if c != 0 then val1 else val2
          ({ s1 with stack := chosen :: rest }, .next)
        | _ => (s1, .next)
      | .local_get idx =>
        let val := s.locals.getD idx (.i32 0)
        (pushVal val s, .next)
      | .local_set idx =>
        match s.stack with
        | v :: rest =>
          let newLocals :=
            if idx < s.locals.length then
              s.locals.set idx v
            else
              s.locals ++ List.replicate (idx - s.locals.length) (.i32 0) ++ [v]
          ({ s with stack := rest, locals := newLocals }, .next)
        | [] => (s, .next)
      | .local_tee idx =>
        match s.stack with
        | v :: _ =>
          let newLocals :=
            if idx < s.locals.length then
              s.locals.set idx v
            else
              s.locals ++ List.replicate (idx - s.locals.length) (.i32 0) ++ [v]
          ({ s with locals := newLocals }, .next)
        | [] => (s, .next)

      -- 32-bit Arithmetic & Bitwise
      | .i32_add =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 + v2)) s2, .next)
      | .i32_sub =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 - v2)) s2, .next)
      | .i32_mul =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 * v2)) s2, .next)
      | .i32_div_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i32 (v1 / v2)) s2, .next)
      | .i32_rem_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i32 (v1 % v2)) s2, .next)
      | .i32_and =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 &&& v2)) s2, .next)
      | .i32_or =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 ||| v2)) s2, .next)
      | .i32_xor =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 ^^^ v2)) s2, .next)
      | .i32_shl =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 <<< (v2 % 32))) s2, .next)
      | .i32_shr_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (v1 >>> (v2 % 32))) s2, .next)

      -- 32-bit Comparisons
      | .i32_eqz =>
        let (v, s1) := popI32 s
        (pushVal (.i32 (if v == 0 then 1 else 0)) s1, .next)
      | .i32_eq =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 == v2 then 1 else 0)) s2, .next)
      | .i32_ne =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 != v2 then 1 else 0)) s2, .next)
      | .i32_lt_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 < v2 then 1 else 0)) s2, .next)
      | .i32_gt_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 > v2 then 1 else 0)) s2, .next)
      | .i32_le_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 <= v2 then 1 else 0)) s2, .next)
      | .i32_ge_u =>
        let (v2, s1) := popI32 s
        let (v1, s2) := popI32 s1
        (pushVal (.i32 (if v1 >= v2 then 1 else 0)) s2, .next)

      -- 64-bit Arithmetic & Bitwise
      | .i64_add =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 + v2)) s2, .next)
      | .i64_sub =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 - v2)) s2, .next)
      | .i64_mul =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 * v2)) s2, .next)
      | .i64_div_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i64 (v1 / v2)) s2, .next)
      | .i64_rem_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        if v2 == 0 then ({ s2 with trapped := true }, .next)
        else (pushVal (.i64 (v1 % v2)) s2, .next)
      | .i64_and =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 &&& v2)) s2, .next)
      | .i64_or =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 ||| v2)) s2, .next)
      | .i64_xor =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 ^^^ v2)) s2, .next)
      | .i64_shl =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 <<< (v2 % 64))) s2, .next)
      | .i64_shr_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i64 (v1 >>> (v2 % 64))) s2, .next)

      -- 64-bit Comparisons
      | .i64_eqz =>
        let (v, s1) := popI64 s
        (pushVal (.i32 (if v == 0 then 1 else 0)) s1, .next)
      | .i64_eq =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 == v2 then 1 else 0)) s2, .next)
      | .i64_ne =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 != v2 then 1 else 0)) s2, .next)
      | .i64_lt_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 < v2 then 1 else 0)) s2, .next)
      | .i64_gt_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 > v2 then 1 else 0)) s2, .next)
      | .i64_le_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 <= v2 then 1 else 0)) s2, .next)
      | .i64_ge_u =>
        let (v2, s1) := popI64 s
        let (v1, s2) := popI64 s1
        (pushVal (.i32 (if v1 >= v2 then 1 else 0)) s2, .next)

      -- Memory Loads & Stores
      -- REF: wasm-exec-instructions#memory-instructions -- every case below implements the exact
      -- reduction rule "If i + ao.offset + N/8 > |mems[x].bytes|, then: Trap." (B7): the bounds
      -- check happens HERE, before `writeMemN`/`readMemN` is ever invoked, so an out-of-bounds
      -- access sets `trapped := true` and never touches `memory` at all -- it can no longer
      -- silently grow the byte array or return a fabricated `0`, and a subsequent `memory_size`
      -- can no longer observe a size change that a trapped instruction never should have caused.
      | .i32_store _ offset =>
        let (val, s1) := popI32 s
        let (addr, s2) := popI32 s1
        let a := addr.toNat + offset
        match WasmMem.write32 s2.memory a val with
        | some m' => ({ s2 with memory := m' }, .next)
        | none => ({ s2 with trapped := true }, .next)
      | .i32_store8 _ offset =>
        let (val, s1) := popI32 s
        let (addr, s2) := popI32 s1
        let a := addr.toNat + offset
        match WasmMem.write8 s2.memory a val.toUInt8 with
        | some m' => ({ s2 with memory := m' }, .next)
        | none => ({ s2 with trapped := true }, .next)
      | .i32_load _ offset =>
        let (addr, s1) := popI32 s
        let a := addr.toNat + offset
        match WasmMem.read32 s1.memory a with
        | some v => (pushVal (.i32 v) s1, .next)
        | none => ({ s1 with trapped := true }, .next)
      | .i32_load8_u _ offset =>
        let (addr, s1) := popI32 s
        let a := addr.toNat + offset
        match WasmMem.read8 s1.memory a with
        | some v => (pushVal (.i32 v.toUInt32) s1, .next)
        | none => ({ s1 with trapped := true }, .next)
      | .i64_store _ offset =>
        let (val, s1) := popI64 s
        let (addr, s2) := popI32 s1
        let a := addr.toNat + offset
        match WasmMem.write64 s2.memory a val with
        | some m' => ({ s2 with memory := m' }, .next)
        | none => ({ s2 with trapped := true }, .next)
      | .i64_load _ offset =>
        let (addr, s1) := popI32 s
        let a := addr.toNat + offset
        match WasmMem.read64 s1.memory a with
        | some v => (pushVal (.i64 v) s1, .next)
        | none => ({ s1 with trapped := true }, .next)
      | .memory_size =>
        let pages := (WasmMem.size s.memory + 65535) / 65536
        (pushVal (.i32 pages.toUInt32) s, .next)
      | .memory_grow =>
        -- REF: wasm-exec-instructions#memory-instructions -- "The memory.grow instruction is
        -- non-deterministic. It may either succeed, returning the old memory size sz, or fail,
        -- returning -1. Failure MUST occur if the referenced memory instance has a maximum size
        -- defined that would be exceeded." (B8.) `s1.memMax` is that declared maximum (in pages,
        -- REF: wasm-exec-runtime#memory-instances's meminst-max invariant), threaded through from
        -- the module's `Limits.max` (`Types.lean`) at instantiation. `hardCeilingPages` additionally
        -- enforces the Wasm32 address-space ceiling of 2^16 pages (4 GiB): this model's `WasmArch`
        -- addresses linear memory with 32-bit (`i32`) offsets (`TargetArch.wordWidth := 32` below),
        -- so a page count beyond 2^16 could never be addressed by any load/store this interpreter
        -- accepts, independent of whatever `memMax` was (or wasn't) declared. Whichever bound
        -- fires, growth fails WITHOUT mutating `memory` at all -- unlike the pre-fix (B8) behaviour,
        -- which always grew unconditionally and never returned the `-1` sentinel.
        let (delta, s1) := popI32 s
        let oldPages := (WasmMem.size s1.memory + 65535) / 65536
        let requestedPages := oldPages + delta.toNat
        let hardCeilingPages : Nat := 65536
        let exceedsDeclaredMax := match s1.memMax with
          | some maxP => requestedPages > maxP.toNat
          | none => false
        if exceedsDeclaredMax || requestedPages > hardCeilingPages then
          let availablePages := match s1.memMax with
            | some maxP => Nat.min maxP.toNat hardCeilingPages
            | none => hardCeilingPages
          (pushVal (.i32 (0xFFFFFFFF : UInt32))
            { s1 with resourceFailure := some (.memoryPages requestedPages availablePages) }, .next)
        else
          let padding := ByteArray.mk (Array.mk (List.replicate (delta.toNat * 65536) (0 : UInt8)))
          (pushVal (.i32 oldPages.toUInt32) { s1 with memory := WasmMem.grow s1.memory padding }, .next)

      -- Conversions
      | .i32_wrap_i64 =>
        let (v, s1) := popI64 s
        (pushVal (.i32 v.toUInt32) s1, .next)
      | .i64_extend_i32_u =>
        let (v, s1) := popI32 s
        (pushVal (.i64 v.toUInt64) s1, .next)

      -- Calls & Control
      | .call idx => hostCall idx s

      -- Structured Control Flow
      | .br depth => (s, .br depth)
      | .br_if depth =>
        let (c, s1) := popI32 s
        if c != 0 then (s1, .br depth) else (s1, .next)
      | .return_op => (s, .ret)
      -- Dead in practice: `evalInstrMatch` below dispatches all three of these itself and never
      -- delegates them here (see this function's own docstring). Present only for match
      -- exhaustiveness, exactly like the trailing `_ => (s, .next)` catch-all.
      | .block _ _ => (s, .next)
      | .loop _ _ => (s, .next)
      | .if_else _ _ _ => (s, .next)
      | _ => (s, .next)

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Ordinary Wasm instructions execute behind the architectural host-input boundary. Only an
    explicit imported call receives host input streams; every other instruction is observationally
    parametric in them and restores the caller's streams unchanged. -/
def evalLeafInstr (instr : WasmInstr) (s : WasmMachineState)
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) :
    WasmMachineState × ControlSignal :=
  match instr with
  | .call idx => hostCall idx s
  | other =>
      let sanitized := s.withExternalInputs ByteArray.empty []
      let result := evalLeafInstrRaw other sanitized hostCall
      (result.1.withExternalInputs s.stdin s.incomingRequests, result.2)

/-- Public typed leaf contract for a 32-bit constant.  Sequence proofs consume this equation
    without unfolding the private interpreter dispatcher. -/
@[simp] theorem evalLeafInstr_i32_const (value : UInt32) (state : WasmMachineState)
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) :
    evalLeafInstr (.i32_const value) state hostCall =
      (pushVal (.i32 value) state, .next) := by
  rfl

/-- Public typed leaf contract for stack drop. -/
@[simp] theorem evalLeafInstr_drop (state : WasmMachineState)
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) :
    evalLeafInstr .drop state hostCall =
      (match state.stack with
       | _ :: rest => ({ state with stack := rest }, .next)
       | [] => (state, .next)) := by
  cases hstack : state.stack <;>
    simp [evalLeafInstr, evalLeafInstrRaw, WasmMachineState.withExternalInputs, hstack] <;>
    cases state <;> simp_all

/-- Imported calls are already the common call/jump boundary and delegate exactly to the selected
    host realization. -/
@[simp] theorem evalLeafInstr_call (index : Nat) (state : WasmMachineState)
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) :
    evalLeafInstr (.call index) state hostCall = hostCall index state := by
  rfl

def WasmHostPreservesExternalInputFrame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : Prop :=
  ∀ index state stdin requests,
    hostCall index (state.withExternalInputs stdin requests) =
      let result := hostCall index state
      (result.1.withExternalInputs stdin requests, result.2)

theorem evalLeafInstr_external_input_frame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (hhost : WasmHostPreservesExternalInputFrame hostCall)
    (instr : WasmInstr) (state : WasmMachineState)
    (stdin : ByteArray) (requests : List ByteArray) :
    evalLeafInstr instr (state.withExternalInputs stdin requests) hostCall =
      let result := evalLeafInstr instr state hostCall
      (result.1.withExternalInputs stdin requests, result.2) := by
  cases instr <;> simp [evalLeafInstr, WasmMachineState.withExternalInputs]
  case call index => exact hhost index state stdin requests

@[simp] theorem popI32_external_input_frame
    (state : WasmMachineState) (stdin : ByteArray) (requests : List ByteArray) :
    popI32 (state.withExternalInputs stdin requests) =
      let result := popI32 state
      (result.1, result.2.withExternalInputs stdin requests) := by
  cases hstack : state.stack with
  | nil => simp [popI32, hstack, WasmMachineState.withExternalInputs]
  | cons head tail =>
      cases head <;> simp [popI32, hstack, WasmMachineState.withExternalInputs]

def finishBlockResult : WasmRunResult → WasmRunResult
  | .error state => .error state
  | .ok (state, .br 0) => .ok (state, .next)
  | .ok (state, .br (depth + 1)) => .ok (state, .br depth)
  | .ok (state, signal) => .ok (state, signal)

@[simp] private theorem finishBlockResult_external_input_frame
    (result : WasmRunResult) (stdin : ByteArray) (requests : List ByteArray) :
    finishBlockResult (result.withExternalInputs stdin requests) =
      (finishBlockResult result).withExternalInputs stdin requests := by
  cases result with
  | error state => rfl
  | ok result =>
      rcases result with ⟨state, signal⟩
      cases signal with
      | next => rfl
      | ret => rfl
      | br depth => cases depth <;> rfl

mutual
  /- REF: wasm-exec-instructions#instructions -/
  /-- Dispatches the three structured control-flow instructions (`.block`/`.loop`/`.if_else`),
      each of which recurses back into this `mutual` group and so needs `fuel`; every other
      instruction is delegated unchanged to `evalLeafInstr` above. `evalInstr` (defined after
      `end` below) is the one and only public entry point external callers (`stepWasm`,
      `runWasmFunction`) use; this function is never called directly from outside the mutual
      group. Fuel-converted (see `defaultWasmFuel`/`WasmRunResult` above): now an ordinary
      structurally-recursive, non-`partial` `def` -- `fuel` decreases by exactly one on every
      entry to this function (whether the matched instruction itself recurses or not), so the
      whole `mutual` group has a single, uniform, kernel-checkable decreasing measure, exactly
      mirroring `Gasm/Targets/X86_64/Semantics.lean`'s `runProgramTraceWithLoops`. -/
  def evalInstrMatch (fuel : Nat) (instr : WasmInstr) (s : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmRunResult :=
    match fuel with
    | 0 => .error s
    | fuel + 1 =>
      match instr with
      | .block _ body =>
        finishBlockResult (evalInstrs fuel body s hostCall)
      | .loop _ body => evalLoop fuel body s hostCall
      | .if_else _ thenBody elseBody =>
        let (c, s1) := popI32 s
        finishBlockResult (if c != 0 then evalInstrs fuel thenBody s1 hostCall
          else evalInstrs fuel elseBody s1 hostCall)
      | leaf => .ok (evalLeafInstr leaf s hostCall)

  /- REF: wasm-exec-instructions#expressions -/
  /-- Evaluates a list of instructions in sequence. The trap/exit guard is inlined here (rather
      than delegated to a call to the `evalInstr` wrapper, which is not yet in scope inside this
      `mutual` group) -- textually identical to the guard in the standalone `evalInstr` below, so
      every instruction dispatched from a sequence is skipped once the state traps or exits,
      exactly as it was when this guard lived inside a single combined function. Fuel-converted:
      `fuel` is consumed once per list element visited (whether that element is actually
      dispatched to `evalInstrMatch` or skipped by the trap/exit guard), giving the whole `mutual`
      group its single decreasing measure -- see `evalInstrMatch`'s docstring. -/
  def evalInstrs (fuel : Nat) (instrs : List WasmInstr) (st : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmRunResult :=
    match fuel with
    | 0 => .error st
    | fuel + 1 =>
      match instrs with
      | [] => .ok (st, .next)
      | i :: rest =>
        if st.trapped || st.exitCode.isSome then
          evalInstrs fuel rest st hostCall
        else
          match evalInstrMatch fuel i st hostCall with
          | .error st' => .error st'
          | .ok (st', .next) => evalInstrs fuel rest st' hostCall
          | .ok (st', other) => .ok (st', other)

  /- REF: wasm-exec-instructions#blocks -/
  /-- Evaluates a loop body repeatedly until loop exit. THE genuinely non-terminating case in this
      whole interpreter -- a real Wasm `loop` re-entering via `.br 0` has no structurally-
      decreasing measure over the instruction list (it evaluates the SAME `body` again), which is
      exactly why the pre-fuel-conversion group had to be `partial`. `fuel` is what makes this
      total: each re-entry consumes at least one unit (via the nested `evalInstrs fuel body st
      hostCall` call, itself fuel-metered), so a loop that never reaches its own exit condition
      now terminates by returning `.error` (fuel exhausted) rather than diverging -- an
      OBSERVABLE, distinct outcome (see `WasmRunResult`'s docstring), never silently reported as
      if the loop had returned normally. This is also the natural inner half of the inner/outer
      split docs/EQUIVALENCE_PROOFS.md#11-the-definition-of-observation-canonical-equivalence-standard
      calls for on non-terminating programs: THIS function proves nothing about whether a real
      infinite loop eventually does useful work (that is an outer progress/liveness obligation,
      stated separately, e.g. against a `VerifiedReactiveProgram`-style contract), it only makes
      "run the deterministic body up to N iterations and compare" a well-typed, provable question
      in the first place -- which it was not at all while `evalLoop` was opaque. -/
  def evalLoop (fuel : Nat) (body : List WasmInstr) (st : WasmMachineState)
      (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal) : WasmRunResult :=
    match fuel with
    | 0 => .error st
    | fuel + 1 =>
      match evalInstrs fuel body st hostCall with
      | .error st' => .error st'
      | .ok (st', sig) =>
        match sig with
        | .next => .ok (st', .next)
        | .br 0 => evalLoop fuel body st' hostCall
        | .br (d + 1) => .ok (st', .br d)
        | .ret => .ok (st', .ret)
end

private theorem evalInstrsContinuation_external_input_frame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (fuel : Nat) (rest : List WasmInstr) (result : WasmRunResult)
    (stdin : ByteArray) (requests : List ByteArray)
    (hrest : ∀ state,
      evalInstrs fuel rest (state.withExternalInputs stdin requests) hostCall =
        (evalInstrs fuel rest state hostCall).withExternalInputs stdin requests) :
    (match result.withExternalInputs stdin requests with
      | .error state => (Except.error state : WasmRunResult)
      | .ok (state, .next) => evalInstrs fuel rest state hostCall
      | .ok (state, signal) => (Except.ok (state, signal) : WasmRunResult)) =
    WasmRunResult.withExternalInputs stdin requests (match result with
      | .error state => (Except.error state : WasmRunResult)
      | .ok (state, .next) => evalInstrs fuel rest state hostCall
      | .ok (state, signal) => (Except.ok (state, signal) : WasmRunResult)) := by
  cases result with
  | error state => rfl
  | ok result =>
      rcases result with ⟨state, signal⟩
      cases signal with
      | next => exact hrest state
      | br depth => rfl
      | ret => rfl

private theorem evalLoopResult_external_input_frame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (fuel : Nat) (body : List WasmInstr) (result : WasmRunResult)
    (stdin : ByteArray) (requests : List ByteArray)
    (hloop : ∀ state,
      evalLoop fuel body (state.withExternalInputs stdin requests) hostCall =
        (evalLoop fuel body state hostCall).withExternalInputs stdin requests) :
    (match result.withExternalInputs stdin requests with
      | .error state => (Except.error state : WasmRunResult)
      | .ok (state, .next) => (Except.ok (state, .next) : WasmRunResult)
      | .ok (state, .br 0) => evalLoop fuel body state hostCall
      | .ok (state, .br (depth + 1)) => (Except.ok (state, .br depth) : WasmRunResult)
      | .ok (state, .ret) => (Except.ok (state, .ret) : WasmRunResult)) =
    WasmRunResult.withExternalInputs stdin requests (match result with
      | .error state => (Except.error state : WasmRunResult)
      | .ok (state, .next) => (Except.ok (state, .next) : WasmRunResult)
      | .ok (state, .br 0) => evalLoop fuel body state hostCall
      | .ok (state, .br (depth + 1)) => (Except.ok (state, .br depth) : WasmRunResult)
      | .ok (state, .ret) => (Except.ok (state, .ret) : WasmRunResult)) := by
  cases result with
  | error state => rfl
  | ok result =>
      rcases result with ⟨state, signal⟩
      cases signal with
      | next => rfl
      | ret => rfl
      | br depth =>
          cases depth with
          | zero => exact hloop state
          | succ depth => rfl

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Simultaneous fuel induction for structured instructions, instruction lists, and loops. The
    three interpreters are mutually recursive, so their frame laws are established together. -/
theorem eval_external_input_frames
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (hhost : WasmHostPreservesExternalInputFrame hostCall) (fuel : Nat) :
    (∀ instr state stdin requests,
      evalInstrMatch fuel instr (state.withExternalInputs stdin requests) hostCall =
        (evalInstrMatch fuel instr state hostCall).withExternalInputs stdin requests) ∧
    (∀ instrs state stdin requests,
      evalInstrs fuel instrs (state.withExternalInputs stdin requests) hostCall =
        (evalInstrs fuel instrs state hostCall).withExternalInputs stdin requests) ∧
    (∀ body state stdin requests,
      evalLoop fuel body (state.withExternalInputs stdin requests) hostCall =
        (evalLoop fuel body state hostCall).withExternalInputs stdin requests) := by
  induction fuel with
  | zero =>
      constructor
      · intros; rfl
      · constructor <;> intros <;> rfl
  | succ fuel ih =>
      rcases ih with ⟨hmatch, hinstrs, hloop⟩
      constructor
      · intro instr state stdin requests
        cases instr <;>
          simp [evalInstrMatch, hinstrs, hloop, evalLeafInstr_external_input_frame, hhost,
            popI32_external_input_frame, WasmRunResult.withExternalInputs]
        case block bodyType body =>
          change finishBlockResult
              ((evalInstrs fuel body state hostCall).withExternalInputs stdin requests) =
            (finishBlockResult (evalInstrs fuel body state hostCall)).withExternalInputs
              stdin requests
          exact finishBlockResult_external_input_frame _ _ _
        case if_else =>
          split
          · change finishBlockResult
                ((evalInstrs fuel _ (popI32 state).2 hostCall).withExternalInputs stdin requests) =
              (finishBlockResult
                (evalInstrs fuel _ (popI32 state).2 hostCall)).withExternalInputs stdin requests
            exact finishBlockResult_external_input_frame _ _ _
          · change finishBlockResult
                ((evalInstrs fuel _ (popI32 state).2 hostCall).withExternalInputs stdin requests) =
              (finishBlockResult
                (evalInstrs fuel _ (popI32 state).2 hostCall)).withExternalInputs stdin requests
            exact finishBlockResult_external_input_frame _ _ _
      · constructor
        · intro instrs state stdin requests
          cases instrs with
          | nil => rfl
          | cons instr rest =>
              simp only [evalInstrs, WasmMachineState.withExternalInputs_trapped,
                WasmMachineState.withExternalInputs_exitCode]
              by_cases hstopped : state.trapped || state.exitCode.isSome
              · simp [hstopped, hinstrs]
              · simp [hstopped]
                rw [hmatch]
                exact evalInstrsContinuation_external_input_frame hostCall fuel rest
                  (evalInstrMatch fuel instr state hostCall) stdin requests
                  (fun next => hinstrs rest next stdin requests)
        · intro body state stdin requests
          simp only [evalLoop]
          rw [hinstrs]
          generalize hresult : evalInstrs fuel body state hostCall = result
          cases result with
          | error failedState => rfl
          | ok result =>
              rcases result with ⟨next, signal⟩
              cases signal with
              | next => rfl
              | ret => rfl
              | br depth =>
                  cases depth with
                  | zero => exact hloop body next stdin requests
                  | succ depth => rfl

theorem evalInstrMatch_external_input_frame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (hhost : WasmHostPreservesExternalInputFrame hostCall)
    (fuel : Nat) (instr : WasmInstr) (state : WasmMachineState)
    (stdin : ByteArray) (requests : List ByteArray) :
    evalInstrMatch fuel instr (state.withExternalInputs stdin requests) hostCall =
      (evalInstrMatch fuel instr state hostCall).withExternalInputs stdin requests :=
  (eval_external_input_frames hostCall hhost fuel).1 instr state stdin requests

theorem evalInstrs_external_input_frame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (hhost : WasmHostPreservesExternalInputFrame hostCall)
    (fuel : Nat) (instrs : List WasmInstr) (state : WasmMachineState)
    (stdin : ByteArray) (requests : List ByteArray) :
    evalInstrs fuel instrs (state.withExternalInputs stdin requests) hostCall =
      (evalInstrs fuel instrs state hostCall).withExternalInputs stdin requests :=
  (eval_external_input_frames hostCall hhost fuel).2.1 instrs state stdin requests

theorem evalLoop_external_input_frame
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (hhost : WasmHostPreservesExternalInputFrame hostCall)
    (fuel : Nat) (body : List WasmInstr) (state : WasmMachineState)
    (stdin : ByteArray) (requests : List ByteArray) :
    evalLoop fuel body (state.withExternalInputs stdin requests) hostCall =
      (evalLoop fuel body state hostCall).withExternalInputs stdin requests :=
  (eval_external_input_frames hostCall hhost fuel).2.2 body state stdin requests

/- REF: wasm-exec-instructions#instructions -/
/-- Collapses a `WasmRunResult` back to the pre-fuel-conversion unwrapped
    `WasmMachineState × ControlSignal` shape, for the legacy convenience wrappers below. `.ok`
    passes its pair through unchanged; `.error s` (fuel exhausted) becomes `({ s with
    fuelExhausted := true }, .next)` -- NOT indistinguishable from ordinary completion, since
    `fuelExhausted` is a dedicated field no other code path sets (see that field's own docstring
    on `WasmMachineState`), but ALSO not structurally forced on a caller the way matching a
    `WasmRunResult` directly is. Every load-bearing whole-program equivalence theorem in this
    codebase avoids this collapse entirely by going through `runWasiTraceState`
    (`Gasm/Targets/WASI/ABI.lean`), which returns the un-collapsed `WasmRunResult`. -/
def collapseWasmRunResult (r : WasmRunResult) : WasmMachineState × ControlSignal :=
  match r with
  | .ok p => p
  | .error s => ({ s with fuelExhausted := true }, .next)

/- REF: wasm-exec-instructions#instructions -/
/-- Public entry point for evaluating a single instruction: applies the trap/exit short-circuit
    guard, then delegates to `evalInstrMatch`'s per-instruction dispatch. Deliberately NOT part of
    the `mutual` group above -- this wrapper's own body is a single non-recursive `if`, so it is
    an ordinary total `def` with a real equation Lean can unfold -- exactly what PA12's general
    trap short-circuit theorem (`evalInstr_trapped_next` in `SemanticsFuzzer.lean`) inducts on,
    without needing visibility into `evalInstrMatch`'s own body at all. Same external signature
    and identical behaviour (for any run that does not exhaust `fuel`) as the historical
    `evalInstr` from before the fuel conversion: `fuel` is a NEW trailing parameter with a
    generous default (`defaultWasmFuel`), so every pre-existing 3-argument call site
    (`evalInstr instr s hostCall`) still compiles and still behaves identically, confirmed by the
    differential fuzzer suite below passing unchanged. See `collapseWasmRunResult`'s docstring for
    exactly what happens on the (for every real program in this codebase, proven never to occur)
    fuel-exhausted path. -/
def evalInstr (instr : WasmInstr) (s : WasmMachineState)
    (hostCall : Nat → WasmMachineState → WasmMachineState × ControlSignal)
    (fuel : Nat := defaultWasmFuel) :
    WasmMachineState × ControlSignal :=
  if s.trapped || s.exitCode.isSome then (s, .next)
  else collapseWasmRunResult (evalInstrMatch fuel instr s hostCall)

/- REF: wasm-exec-instructions#instructions -/
/-- Pure operational step evaluation for single instruction. `fuel` is a new trailing parameter
    with a generous default (`defaultWasmFuel`), so every pre-existing 2-argument call site
    (`stepWasm instr s`) still compiles unchanged; see `evalInstr`'s docstring for what "unchanged"
    means precisely across the fuel conversion. -/
def stepWasm (instr : WasmInstr) (s : WasmMachineState) (fuel : Nat := defaultWasmFuel) : WasmMachineState :=
  (evalInstr instr s (fun _ st => (st, .next)) fuel).1

/- REF: wasm-exec-instructions#function-calls -/
/-- Evaluates an entire sequence of structured WebAssembly instructions starting from initial
    locals. `fuel` is a new trailing parameter with a generous default (`defaultWasmFuel`), so
    every pre-existing 2-argument call site (`runWasmFunction body locals`) still compiles
    unchanged. -/
def runWasmFunction (body : List WasmInstr) (locals : List WasmVal) (fuel : Nat := defaultWasmFuel) : WasmMachineState :=
  let s : WasmMachineState := { locals := locals }
  (evalInstr (WasmInstr.block .empty body) s (fun _ st => (st, .next)) fuel).1

/- REF: docs/TARGETS/WASM.md#1-webassembly-machine-model -/
/-- Architecture tag for WebAssembly target. -/
structure WasmArch where

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
/-- TargetArch instance for WebAssembly. -/
instance : TargetArch WasmArch where
  wordWidth := 32
  MachineState := WasmMachineState
  Instruction := ULift WasmInstr
  stepPure pkg s := stepWasm pkg.down s

end Gasm.Targets.Wasm

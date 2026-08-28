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
import Gasm.Core.Types
import Gasm.Core.Rng
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Semantics
import Gasm.Targets.Wasm.Fuzzable
import Gasm.Targets.Wasm.HostOracle

namespace Gasm.Targets.Wasm.SemanticsFuzzer

open Gasm.Core
open Gasm.Targets.Wasm
open Gasm.Targets.Wasm.Fuzzable
open Gasm.Targets.Wasm.HostOracle

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#5-differential-case-result-type -/
/-- Result structure for Wasm instruction validation against host engine. `skipped` marks the
zero-vector case (no fuzzable host states, whether because `canFuzzWasmRuntime` excludes the
underlying instruction or state generation otherwise yielded nothing): distinct from `passed`,
since a skip means "verified nothing" rather than "verified and matched" (TCB.md T11-b vacuity;
docs/REVIEW.md Law 8, Law 13 — a zero-vector case auto-reporting PASS is exactly the "mock
verification" facade those laws prohibit). -/
structure WasmInstructionDiffResult where
  passed       : Bool
  mnemonic     : String
  totalTested  : Nat
  failedCount  : Nat
  errorMessage : Option String := none
  skipped      : Bool := false
  deriving Inhabited

/- REF: wasm-syntax-instructions#instructions -/
/-- A single differentially-fuzzed unit under test: either a leaf instruction or a compound
    structured control-flow instruction. Both shapes reduce to the same thing - one `WasmInstr`
    to run, a way to decide its declared Wasm result type *for a given state* (leaf instructions
    such as `select_op` / `local_get` / `local_tee` have a type that depends on the fuzzed state,
    not just the opcode; control-flow cases supply a constant function instead), an optional way
    to reconstruct setup instructions the state implies (leaf instructions replay a captured
    operand stack; control-flow cases need none, since they drive everything through locals), and
    a dedicated fuzzed-state generator. Folding both suites into one case shape means the
    validation/comparison logic against the host oracle - including the fail-closed handling of
    `OracleFailure` - is written and fixed in exactly one place (`verifyWasmDiffCase`). -/
structure WasmDiffCase where
  name           : String
  instr          : WasmInstr
  resultTypesFor : WasmMachineState → List ValType
  preInstrsFor   : WasmMachineState → List WasmInstr := fun _ => []
  genStates      : FuzzerRng → Nat → Prod (List WasmMachineState) FuzzerRng
  -- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#9-out-of-bounds-and-memory-limit-fuzz-coverage --
  -- the declared `Limits.max` (in pages) the synthesized host module should be built with
  -- (forwarded to `buildTestWasmModuleForResults`'s `memoryMaxPages` in `verifyWasmDiffCase`
  -- below), so a case fuzzing `memory.grow` against a maximum can make the host module and the
  -- model's fuzzed `WasmMachineState.memMax` agree on the same bound. `none` (the default)
  -- matches every existing case, which declares no maximum.
  memoryMaxPages : Option UInt32 := none

/- REF: wasm-syntax-instructions#instructions -/
/-- Wraps a single leaf instruction as a `WasmDiffCase`: its declared result type and setup
    instructions are derived per-state from `inferLeafResultTypes` / `stackSetupInstrs` (mirroring
    what the old single-instruction builder used to compute inline), and its fuzzed states come
    from `generateWasmFuzzStates`, or the empty list for instructions `canFuzzWasmRuntime` excludes
    (e.g. `unreachable`, `call`), which - as before - auto-passes with zero vectors tested. -/
def mkLeafCase (instr : WasmInstr) : WasmDiffCase :=
  { name := ((repr instr).pretty.replace "Gasm.Targets.Wasm.WasmInstr." "").take 25 |>.toString
    instr := instr
    resultTypesFor := fun s => inferLeafResultTypes instr s.stack s.locals
    preInstrsFor := fun s => stackSetupInstrs s.stack
    genStates := fun rng cnt => if canFuzzWasmRuntime instr then generateWasmFuzzStates instr rng cnt else ([], rng) }

/- REF: wasm-syntax-instructions#instructions -/
/-- Comprehensive list of all supported leaf WebAssembly instructions (arithmetic, comparisons,
    conversions, parametric/variable, memory, constants). -/
def allSupportedWasmSuite : List WasmInstr := [
  -- 1. 32-bit Numeric Arithmetic & Bitwise
  .i32_add,
  .i32_sub,
  .i32_mul,
  .i32_div_u,
  .i32_rem_u,
  .i32_and,
  .i32_or,
  .i32_xor,
  .i32_shl,
  .i32_shr_u,

  -- 2. 32-bit Integer Comparisons
  .i32_eqz,
  .i32_eq,
  .i32_ne,
  .i32_lt_u,
  .i32_gt_u,
  .i32_le_u,
  .i32_ge_u,

  -- 3. 64-bit Numeric Arithmetic & Bitwise
  .i64_add,
  .i64_sub,
  .i64_mul,
  .i64_div_u,
  .i64_rem_u,
  .i64_and,
  .i64_or,
  .i64_xor,
  .i64_shl,
  .i64_shr_u,

  -- 4. 64-bit Integer Comparisons
  .i64_eqz,
  .i64_eq,
  .i64_ne,
  .i64_lt_u,
  .i64_gt_u,
  .i64_le_u,
  .i64_ge_u,

  -- 5. Conversions
  .i32_wrap_i64,
  .i64_extend_i32_u,

  -- 6. Parametric & Variables
  .drop,
  .select_op,
  .local_get 0,
  .local_set 0,
  .local_tee 0,

  -- 7. Memory Operations
  .i32_load 2 0,
  .i64_load 3 0,
  .i32_store 2 0,
  .i64_store 3 0,
  .i32_store8 0 0,
  .memory_size,
  .memory_grow,

  -- 8. Constants
  .i32_const 42,
  .i64_const 0x123456789ABCDEF0
]

/- REF: wasm-syntax-instructions#instructions -/
/-- The leaf-instruction suite, each wrapped as a `WasmDiffCase` via `mkLeafCase`. -/
def allLeafDiffCases : List WasmDiffCase := allSupportedWasmSuite.map mkLeafCase

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: `block` computing `local0 + local1` then unconditionally branching out at
    depth 0 with the arithmetic result already on the stack, exercising the `block`/`br`/arithmetic
    interaction described in `evalInstr`'s `.block` case. -/
def cfBlockArithBr0 : WasmDiffCase :=
  { name := "block_arith_br0"
    instr := .block (.val .i32) [.local_get 0, .local_get 1, .i32_add, .br 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v1 in curated32BitValues.take 6 do
        for v2 in curated32BitValues.take 6 do
          states := states ++ [{ locals := [WasmVal.i32 v1, WasmVal.i32 v2] }]
      for _ in [0:randCount] do
        let (u1, r1) := curRng.nextUInt32
        let (u2, r2) := r1.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u1, WasmVal.i32 u2] }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: 64-bit variant of `cfBlockArithBr0`, verifying that `block`/`br` signal
    handling is agnostic to the operand-stack value width. -/
def cfBlockArithBr0I64 : WasmDiffCase :=
  { name := "block_arith_br0_i64"
    instr := .block (.val .i64) [.local_get 0, .local_get 1, .i64_add, .br 0]
    resultTypesFor := fun _ => [ValType.i64]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v1 in curated64BitValues.take 5 do
        for v2 in curated64BitValues.take 5 do
          states := states ++ [{ locals := [WasmVal.i64 v1, WasmVal.i64 v2] }]
      for _ in [0:randCount] do
        let (u1, r1) := curRng.next
        let (u2, r2) := r1.next
        states := states ++ [{ locals := [WasmVal.i64 u1, WasmVal.i64 u2] }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: `block` producing `local0`, then unconditionally `br 0` past dead trailing
    code (`local1` would otherwise be added in). Verifies both that `ControlSignal.br 0` is
    consumed at its own immediately-enclosing block and that code following a taken branch is
    skipped, per `evalInstrs`'s short-circuit on any non-`.next` signal. Paired with
    `cfLoopReentersViaBrZero` below: a `block`'s `br 0` always exits after exactly one pass,
    whereas a `loop`'s `br 0` re-enters - an interpreter where `.loop` were wrongly evaluated
    identically to `.block` would still pass this case (it only ever runs once) but fail that one. -/
def cfBrDepth0 : WasmDiffCase :=
  { name := "br_depth0_skip"
    instr := .block (.val .i32) [.local_get 0, .br 0, .local_get 1, .i32_add]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v1 in curated32BitValues do
        for v2 in curated32BitValues.take 4 do
          states := states ++ [{ locals := [WasmVal.i32 v1, WasmVal.i32 v2] }]
      for _ in [0:randCount] do
        let (u1, r1) := curRng.nextUInt32
        let (u2, r2) := r1.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u1, WasmVal.i32 u2] }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: `br 1` from inside a nested `block` targets the middle block directly,
    exercising the `.br (d + 1) => .br d` depth-decrement propagation through one intervening
    level in both the inner and middle `block`'s `evalInstr` cases. All three blocks are typed
    `(result i32)`: the innermost block becomes statically unreachable at the `br 1` (which is
    *inside* it), so it hands off its declared result type to the middle block regardless of what
    its own (dead) fallthrough would have produced - an innermost block typed `(result)` (`.empty`)
    here would hand off zero values instead, and V8 rejects the middle block's own fallthrough
    arity check ("expected 1 elements on the stack for fallthru, found 0"); this was caught for
    real by this fix cycle's adversarial review (see `runMandatoryOracleControls`'s negative
    control, which pins this exact class of bug down permanently).
    The outermost wrapping block and its trailing `i32.const 1, i32.add` are load-bearing for
    DISCRIMINATION, not just validity: `stepWasm` discards whatever `ControlSignal` remains once
    the top-level instruction finishes (`(evalInstr instr s hostCall).1`), so if the middle block's
    `.br (d + 1) => .br d` decrement were silently dropped (i.e. it forwarded the *undecremented*
    signal instead of `.br 0`), the earlier version of this case - `block[ block[ local.get 0,
    br 1 ] ]` with nothing above the target - produced the identical final stack either way,
    because there was no further code whose execution-or-skip could reveal the difference. A
    re-review of this fix cycle found that mutation-testing a faithful interpreter mirror with the
    decrement removed still passed all 65 vectors under that shape. With an outer frame's trailing
    arithmetic present, an under-decremented signal instead escapes past the middle block's own
    `.br 0` consumption, propagates out to the outermost block, and causes its `evalInstrs` to
    short-circuit *before* reaching `i32.const 1, i32.add` - so the correct model returns
    `local0 + 1` while the mutated one returns `local0` alone. Verified by temporarily changing
    `evalInstr`'s `.block` case in Semantics.lean from `| .br (d + 1) => (s', .br d)` to
    `| .br (d + 1) => (s', .br (d + 1))` (decrement dropped): this case failed with
    `Result mismatch! Model=Gasm.Targets.Wasm.WasmVal.i32 0, Host=Gasm.Targets.Wasm.WasmVal.i32 1`
    for `local0 = 0` (and likewise for every other vector), then passed again once reverted. -/
def cfBrDepth1 : WasmDiffCase :=
  { name := "br_depth1_nested"
    instr := .block (.val .i32)
      [ .block (.val .i32)
          [ .block (.val .i32) [.local_get 0, .br 1] ]
      , .i32_const 1
      , .i32_add ]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v] }]
      for _ in [0:randCount] do
        let (u, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u] }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: `br 2` from three levels of nesting targets the third-innermost block,
    exercising the depth-decrement chain (`.br 2 -> .br 1 -> .br 0`) across two intervening
    `block` levels, all typed `(result i32)` for the same reason as `cfBrDepth1` (the value
    genuinely flows outward hop by hop, not vacuously past the first one). Wrapped in exactly the
    same way as `cfBrDepth1` - one more enclosing `(result i32)` block with a trailing
    `i32.const 1, i32.add` - so that an incompletely-decremented signal at *any* of the two
    intervening levels escapes past this outermost wrapper and is observable as a skipped
    increment (`local0` instead of `local0 + 1`), rather than being silently absorbed by
    `stepWasm`'s discarded final `ControlSignal` the way the pre-review version of this case was.
    Verified with the same `.block` decrement mutation as `cfBrDepth1`: this case failed with
    `Model=Gasm.Targets.Wasm.WasmVal.i32 0, Host=Gasm.Targets.Wasm.WasmVal.i32 1` for `local0 = 0`,
    then passed again once reverted. -/
def cfBrDepth2 : WasmDiffCase :=
  { name := "br_depth2_nested"
    instr := .block (.val .i32)
      [ .block (.val .i32)
          [ .block (.val .i32) [ .block (.val .i32) [.local_get 0, .br 2] ] ]
      , .i32_const 1
      , .i32_add ]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v] }]
      for _ in [0:randCount] do
        let (u, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u] }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: `if_else` with arms that are distinguishable by result value, verifying
    condition-based branch selection in `evalInstr`'s `.if_else` case (both the `then` and `else`
    arm are exercised via curated zero / non-zero condition values). -/
def cfIfElseArms : WasmDiffCase :=
  { name := "if_else_arms"
    instr := .block (.val .i32) [.local_get 0, .if_else (.val .i32) [.local_get 1] [.local_get 2]]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for cond in curated32BitValues.take 6 do
        for v1 in curated32BitValues.take 3 do
          for v2 in curated32BitValues.take 3 do
            states := states ++ [{ locals := [WasmVal.i32 cond, WasmVal.i32 v1, WasmVal.i32 v2] }]
      for _ in [0:randCount] do
        let (c, r1) := curRng.nextUInt32
        let (v1, r2) := r1.nextUInt32
        let (v2, r3) := r2.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 c, WasmVal.i32 v1, WasmVal.i32 v2] }]
        curRng := r3
      (states, curRng) }

/- REF: wasm-exec-instructions#control-instructions -/
/-- Control-flow case: `br_if 0` taken (condition non-zero) exits the block immediately with
    `local0`; not taken falls through, drops `local0`, and produces `local2` instead. Verifies
    both branches of `evalInstr`'s `.br_if` case (the condition pop and the `.br` vs `.next`
    signal split) against the same host module. -/
def cfBrIfTakenNotTaken : WasmDiffCase :=
  { name := "br_if_taken_not_taken"
    instr := .block (.val .i32) [.local_get 0, .local_get 1, .br_if 0, .drop, .local_get 2]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for cond in curated32BitValues.take 6 do
        for v0 in curated32BitValues.take 3 do
          for v2 in curated32BitValues.take 3 do
            states := states ++ [{ locals := [WasmVal.i32 v0, WasmVal.i32 cond, WasmVal.i32 v2] }]
      for _ in [0:randCount] do
        let (cond, r1) := curRng.nextUInt32
        let (v0, r2) := r1.nextUInt32
        let (v2, r3) := r2.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 v0, WasmVal.i32 cond, WasmVal.i32 v2] }]
        curRng := r3
      (states, curRng) }

/- REF: wasm-exec-instructions#blocks -/
/-- Control-flow case: a `loop` accumulating `local0 + (local0 - 1) + ... + 1 + 0` into `local1`,
    exiting via `br_if 1` (out of the enclosing block) once the counter reaches zero and otherwise
    re-entering the loop via the unconditional `br 0`. Exercises `evalLoop`'s re-entry on `.br 0`
    and its propagation of `.br (d + 1)` out of the loop entirely. The trip count is drawn from
    `curatedLoopBoundValues` (and a `% 21`-bounded random draw) so both the Lean model and the
    host oracle are guaranteed to terminate. The trailing `.unreachable` after the loop is load-
    bearing for V8's *static* validation, not for runtime behaviour: the loop only ever exits via
    the `br_if 1` (which bypasses the trailing instruction entirely at runtime, exactly like real
    compiler-emitted Wasm for this idiom), but the loop's own declared type is `.empty` (a `loop`'s
    branch target is always its parameter types, not its results), so on the never-taken "loop body
    fell off the end normally" path the outer `(result i32)` block would statically appear to
    receive zero values instead of one; `unreachable` tells the validator that path is dead. -/
def cfLoopBoundedSum : WasmDiffCase :=
  { name := "loop_bounded_sum_brif"
    -- locals: 0 = countdown counter, 1 = running accumulator
    instr := .block (.val .i32)
      [ .loop .empty
          [ .local_get 1
          , .local_get 0
          , .i32_eqz
          , .br_if 1
          , .drop
          , .local_get 1
          , .local_get 0
          , .i32_add
          , .local_set 1
          , .local_get 0
          , .i32_const 1
          , .i32_sub
          , .local_set 0
          , .br 0 ]
      , .unreachable ]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for counter in curatedLoopBoundValues do
        for accSeed in [(0 : UInt32), 100, 0xFFFFFFFF] do
          states := states ++ [{ locals := [WasmVal.i32 counter, WasmVal.i32 accSeed] }]
      for _ in [0:randCount] do
        let (c, r1) := curRng.nextNat 21
        let (accSeed, r2) := r1.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 (UInt32.ofNat c), WasmVal.i32 accSeed] }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#blocks -/
/-- Control-flow case: a minimal companion to `cfLoopBoundedSum` that counts *how many times the
    loop body actually ran* rather than accumulating a sum, making the loop-vs-block distinction
    from `cfBrDepth0`'s docstring concrete and directly observable: the expected result is exactly
    the starting counter value. If `.loop`'s `br 0` were (incorrectly) handled the same way as a
    `block`'s `br 0` - i.e. exiting instead of re-entering `evalLoop` - this case would return 1
    for every counter greater than 1, diverging from the host's genuinely-repeated count, while
    `cfBrDepth0`/`cfBlockArithBr0` (pure `block`, no `loop` involved) would be unaffected either
    way. Same trailing-`unreachable` typing rationale as `cfLoopBoundedSum`. -/
def cfLoopReentersViaBrZero : WasmDiffCase :=
  { name := "loop_brzero_reenters_not_exits"
    -- locals: 0 = countdown counter, 1 = number of passes actually executed
    instr := .block (.val .i32)
      [ .loop .empty
          [ .local_get 1
          , .local_get 0
          , .i32_eqz
          , .br_if 1
          , .drop
          , .local_get 1
          , .i32_const 1
          , .i32_add
          , .local_set 1
          , .local_get 0
          , .i32_const 1
          , .i32_sub
          , .local_set 0
          , .br 0 ]
      , .unreachable ]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for counter in curatedLoopBoundValues do
        states := states ++ [{ locals := [WasmVal.i32 counter, WasmVal.i32 0] }]
      for _ in [0:randCount] do
        let (c, r) := curRng.nextNat 21
        states := states ++ [{ locals := [WasmVal.i32 (UInt32.ofNat c), WasmVal.i32 0] }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#blocks -/
/-- Control-flow case: `br 2` taken from *inside a loop* escapes past an intervening `block` and
    the loop's own re-entry mechanism entirely, landing directly in the "target" block - distinct
    from `cfLoopBoundedSum`'s `br_if 1` (loop -> immediately-enclosing block) in that here the
    branch also passes through one extra `block` frame that itself contributes nothing on this
    path. That middle block stays `.empty` (it genuinely, normally receives zero values from the
    loop's own declared type - it is not the frame containing the divergent instruction, so it is
    not statically unreachable at its own end); the target block gets the trailing `.unreachable`
    instead, since *it* is the one whose normal-completion arity (0, via the middle block) would
    otherwise mismatch its declared `(result i32)`.
    As with `cfBrDepth1`/`cfBrDepth2`, this whole construct is further wrapped in one more
    `(result i32)` block with a trailing `i32.const 1, i32.add`: without it, an under-decremented
    signal from either `evalLoop`'s `.br (d + 1) => .br d` or the target block's own decrement
    would still be silently absorbed by `stepWasm`'s discarded final signal, since there is
    otherwise no code left to observe whether it escaped one level too far or too few.
    Verified both ways: mutating `evalInstr`'s `.block` decrement (as in `cfBrDepth1`) OR
    `evalLoop`'s `.br (d + 1) => (st', .br d)` (dropping to `.br (d + 1)`) each independently made
    this case fail with `Model=Gasm.Targets.Wasm.WasmVal.i32 0, Host=Gasm.Targets.Wasm.WasmVal.i32 1`
    for `local0 = 0`; both passed again once reverted. -/
def cfBrEscapesLoopDepth2 : WasmDiffCase :=
  { name := "br_escapes_loop_depth2"
    instr := .block (.val .i32)
      [ .block (.val .i32)
          [ .block .empty
              [ .loop .empty [ .local_get 0, .br 2 ] ]
          , .unreachable ]
      , .i32_const 1
      , .i32_add ]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v] }]
      for _ in [0:randCount] do
        let (u, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u] }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#blocks -/
/-- Control-flow case: `br 1` from inside a `loop` targets the loop's *immediately enclosing*
    block directly (the simplest possible loop-escape - one hop, no intervening frame), pinning
    `evalLoop`'s own `.br (d + 1) => .br d` decrement (Semantics.lean) specifically, as distinct
    from `cfBrEscapesLoopDepth2` above (which additionally exercises a `.block`'s decrement one
    level further out) and from `cfLoopBoundedSum`/`cfLoopReentersViaBrZero` (whose `br_if 1`
    targets depth 1 directly with no decrement chain at all, since a loop's own label is always
    depth 0). Wrapped in the same outer-block-plus-trailing-arithmetic shape as `cfBrDepth1`/
    `cfBrDepth2`/`cfBrEscapesLoopDepth2`, for the identical reason: without an enclosing frame
    whose trailing code can be skipped, an under-decremented signal from `evalLoop` alone is
    unobservable once it reaches the top and `stepWasm` discards it. Verified: mutating
    `evalLoop`'s `.br (d + 1) => (st', .br d)` to `.br (d + 1) => (st', .br (d + 1))` made this
    case fail with `Model=Gasm.Targets.Wasm.WasmVal.i32 0, Host=Gasm.Targets.Wasm.WasmVal.i32 1`
    for `local0 = 0`; passed again once reverted. The same `.block`-decrement mutation used for
    `cfBrDepth1`/`cfBrDepth2` does *not* affect this case, since `evalLoop`'s own (unmutated)
    decrement already reduces the escaping signal to exactly `.br 0` before the target block ever
    sees it - confirming this case isolates `evalLoop`'s decrement specifically. -/
def cfLoopBrOneEscapesToBlock : WasmDiffCase :=
  { name := "loop_br1_escapes_to_block"
    instr := .block (.val .i32)
      [ .block (.val .i32)
          [ .loop .empty [.local_get 0, .br 1]
          , .unreachable ]
      , .i32_const 1
      , .i32_add ]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v] }]
      for _ in [0:randCount] do
        let (u, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u] }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#returning-from-a-function -/
/-- Control-flow case: `return_op` from inside a nested `.empty`-typed block unwinds past the
    dead trailing `local1` and out of the outer block entirely, leaving `local0` as the result.
    Verifies that `ControlSignal.ret` propagates unchanged through every enclosing `block`'s
    `evalInstr` case (the `other => (s', other)` fallthrough), unlike `.br` which is consumed or
    decremented at each level. Unlike `cfBrDepth1`, the inner block here stays `.empty`: `return`
    validates against the *function's* result type directly (irrespective of any block types in
    between), so the inner block's own declared type is irrelevant to validity - it is simply
    never reached normally, and V8 accepts arbitrary polymorphic code after a divergent `return`. -/
def cfReturnFromNesting : WasmDiffCase :=
  { name := "return_op_from_nesting"
    instr := .block (.val .i32) [.block .empty [.local_get 0, .return_op], .local_get 1]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v1 in curated32BitValues do
        for v2 in curated32BitValues.take 3 do
          states := states ++ [{ locals := [WasmVal.i32 v1, WasmVal.i32 v2] }]
      for _ in [0:randCount] do
        let (u1, r1) := curRng.nextUInt32
        let (u2, r2) := r1.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 u1, WasmVal.i32 u2] }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-runtime#administrative-instructions -/
/-- Control-flow case: `i32_div_u` by a (sometimes zero) divisor two `block` levels deep, fuzzing
    trap propagation through nested frames. `curated32BitValues.take 5` includes `0`, so the
    cartesian product deliberately covers both a genuine runtime trap (divisor `0`, both engines
    must trap) and ordinary division (divisor non-zero, both engines must agree on the quotient) -
    a single case exercising both arms of `evalInstr`'s `if v2 == 0 then trapped else ...` check
    from underneath two `evalInstr`/`evalInstrs` frame boundaries. Validity is unconditional here
    (no branch/unreachable involved): Wasm validation is static and does not care that a
    particular *input* will trap at runtime. -/
def cfTrapInsideNestedBlocks : WasmDiffCase :=
  { name := "trap_propagates_through_nested_blocks"
    instr := .block (.val .i32) [.block (.val .i32) [.local_get 0, .local_get 1, .i32_div_u]]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for dividend in curated32BitValues.take 5 do
        for divisor in curated32BitValues.take 5 do
          states := states ++ [{ locals := [WasmVal.i32 dividend, WasmVal.i32 divisor] }]
      for _ in [0:randCount] do
        let (dividend, r1) := curRng.nextUInt32
        let (divisorRaw, r2) := r1.nextUInt32
        -- Bias roughly 1-in-4 draws to a literal zero divisor so the random tail keeps exercising
        -- the trap path too, not just curated combinations.
        let divisor := if divisorRaw % 4 == 0 then (0 : UInt32) else divisorRaw
        states := states ++ [{ locals := [WasmVal.i32 dividend, WasmVal.i32 divisor] }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Control-flow case: store a fuzzed i32 value to linear memory and immediately load it back,
    so the comparison actually observes memory content rather than the unchecked `[]` result type
    the leaf `i32_store` suite entry declares (a bare store's return value is `void`, so nothing
    about *what got written* was ever previously compared). -/
def cfStoreLoadRoundTrip32 : WasmDiffCase :=
  { name := "store_load_roundtrip_i32"
    instr := .block (.val .i32) [.i32_const 16, .local_get 0, .i32_store 2 0, .i32_const 16, .i32_load 2 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v], memory := mem }]
      for _ in [0:randCount] do
        let (v, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 v], memory := mem }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- 64-bit variant of `cfStoreLoadRoundTrip32`. -/
def cfStoreLoadRoundTrip64 : WasmDiffCase :=
  { name := "store_load_roundtrip_i64"
    instr := .block (.val .i64) [.i32_const 16, .local_get 0, .i64_store 3 0, .i32_const 16, .i64_load 3 0]
    resultTypesFor := fun _ => [ValType.i64]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated64BitValues do
        states := states ++ [{ locals := [WasmVal.i64 v], memory := mem }]
      for _ in [0:randCount] do
        let (v, r) := curRng.next
        states := states ++ [{ locals := [WasmVal.i64 v], memory := mem }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Byte-store variant of `cfStoreLoadRoundTrip32`: stores the low byte of a fuzzed i32 value and
    reads it back unsigned, so the result is `local0 &&& 0xFF` on both sides - checked
    differentially, not by asserting the mask ourselves. -/
def cfStore8LoadRoundTrip : WasmDiffCase :=
  { name := "store8_load_roundtrip"
    instr := .block (.val .i32) [.i32_const 16, .local_get 0, .i32_store8 0 0, .i32_const 16, .i32_load8_u 0 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v], memory := mem }]
      for _ in [0:randCount] do
        let (v, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 v], memory := mem }]
        curRng := r
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Endianness-pinning case: `i32.store` a full 4-byte value, then read back only its lowest byte
    via `i32.load8_u` at the *same* address. `cfStoreLoadRoundTrip32` alone cannot catch a byte
    order bug: writing and reading with the same (wrong) convention still round-trips correctly
    (`read(write(x)) = x` regardless of which endianness both sides agree on), since a full-width
    store followed by a full-width load at matching widths is symmetric. Reading back only the
    first byte breaks that symmetry - on a genuinely little-endian implementation (the Wasm spec's
    requirement, `writeMem32`/`readMem8` in Semantics.lean), the result is `local0 &&& 0xFF`; a
    implementation that silently swapped byte order in `writeMem32` (or `readMem8`) would instead
    surface the high byte for values whose low and high bytes differ, which the curated values
    (`0x100`, `0x7FFF`, `0x8000`, ...) are chosen to guarantee. -/
def cfStoreI32ThenLoadByte0Endianness : WasmDiffCase :=
  { name := "store_i32_load_byte0_endianness"
    instr := .block (.val .i32) [.i32_const 16, .local_get 0, .i32_store 2 0, .i32_const 16, .i32_load8_u 0 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      for v in curated32BitValues do
        states := states ++ [{ locals := [WasmVal.i32 v], memory := mem }]
      for _ in [0:randCount] do
        let (v, r) := curRng.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 v], memory := mem }]
        curRng := r
      (states, curRng) }

-- ================================================================================================
-- B7/B8 (MODEL_DEBT.md, docs/tasks/B7-wasm-oob-trap-and-limits.md): out-of-bounds memory access
-- and `memory.grow`/`Limits.max` fuzz coverage. `Semantics.lean`'s `writeMem8` used to silently
-- zero-pad and grow linear memory on an out-of-bounds write instead of trapping, and
-- `memory_grow` never consulted `Limits.max` or failed at all -- and the pre-fix fuzzer generated
-- addresses only from a small statically in-bounds set (`Fuzzable.lean`'s `.i32_store`/`.i32_load`
-- states use address 16 or 64 into a full 65536-byte page), making both bugs structurally
-- invisible to differential testing. The cases below deliberately generate boundary-straddling,
-- far-out-of-bounds, and `UInt32.max` (2^32 - 1) addresses so the host oracle and the (now
-- trapping) Lean model are compared on exactly the accesses the old fuzzer could never produce.
-- ================================================================================================

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `i32.load8_u` at and around the exact end of a one-page (65536-byte) linear memory: valid
    addresses `0`/`65535` (the very last in-bounds byte, i.e. "at the limit") must succeed on both
    engines, while `65536` ("one past the limit"), `65537`, `100000` ("far past it"), and
    `0xFFFFFFFF` (`2^32 - 1`) must all genuinely TRAP on both -- pinning `evalInstr`'s
    `.i32_load8_u` bounds check (`a + 1 > s1.memory.size`) against the spec's `t.load` reduction
    rule (`wasm-exec-instructions#memory-instructions`: "If `i + ao.offset + N/8 >
    |mems[x].bytes|`, then: Trap."), which the pre-B7 model violated by returning `0` instead. -/
def oobLoad8AtBoundary : WasmDiffCase :=
  { name := "oob_load8_at_boundary"
    instr := .block (.val .i32) [.local_get 0, .i32_load8_u 0 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0x5A : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      let addrs : List UInt32 := [0, 1, 65534, 65535, 65536, 65537, 65538, 100000, 0xFFFFFFFF]
      for a in addrs do
        states := states ++ [{ locals := [WasmVal.i32 a], memory := mem }]
      for _ in [0:randCount] do
        let (bucket, r1) := curRng.nextNat 3
        let (raw, r2) := r1.nextUInt32
        let addr : UInt32 :=
          if bucket == 0 then UInt32.ofNat (65536 + (raw.toNat % 8))
          else if bucket == 1 then UInt32.ofNat (65528 + (raw.toNat % 16))
          else (0xFFFFFFFF : UInt32) - UInt32.ofNat (raw.toNat % 8)
        states := states ++ [{ locals := [WasmVal.i32 addr], memory := mem }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `i32.store8` then immediate `i32.load8_u` at the SAME fuzzed address: for an in-bounds address
    the round trip must return exactly the stored byte (masked to 0xFF) on both engines, exercising
    correctness right at the boundary (`65534`/`65535`, "at the limit") in addition to the pure
    trap check; for an out-of-bounds address (`65536` upward, or `0xFFFFFFFF`) the STORE itself
    must trap immediately, so the trailing `local.get`/`load` never execute (`evalInstr`'s trap
    short-circuit, `trapShortCircuitGuard_inst`) and both engines must report a trap, never a
    value. Pins `evalInstr`'s `.i32_store8` bounds check (`a + 1 > s2.memory.size`). -/
def oobStore8LoadRoundTripBoundary : WasmDiffCase :=
  { name := "oob_store8_load_roundtrip_boundary"
    instr := .block (.val .i32)
      [.local_get 0, .local_get 1, .i32_store8 0 0, .local_get 0, .i32_load8_u 0 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      let addrs : List UInt32 := [0, 1, 65534, 65535, 65536, 65537, 65538, 100000, 0xFFFFFFFF]
      for a in addrs do
        for v in [(0x00 : UInt32), 0xAB, 0xFF] do
          states := states ++ [{ locals := [WasmVal.i32 a, WasmVal.i32 v], memory := mem }]
      for _ in [0:randCount] do
        let (bucket, r1) := curRng.nextNat 3
        let (raw, r2) := r1.nextUInt32
        let addr : UInt32 :=
          if bucket == 0 then UInt32.ofNat (65536 + (raw.toNat % 8))
          else if bucket == 1 then UInt32.ofNat (65528 + (raw.toNat % 16))
          else (0xFFFFFFFF : UInt32) - UInt32.ofNat (raw.toNat % 8)
        let (v, r3) := r2.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 addr, WasmVal.i32 v], memory := mem }]
        curRng := r3
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `i32.load` (4-byte width) straddling the exact end of a one-page memory: `65532` is the last
    address whose full 4-byte read stays in-bounds ("at the limit", `65532 + 4 = 65536 =`
    memory size); `65533`/`65534`/`65535` each straddle the boundary by reading 1-3 bytes past the
    end ("unaligned near the boundary" -- the read WOULD start in-bounds but overrun) and must
    trap; `65536` (fully past) and `0xFFFFFFFF` (`2^32 - 1`) must also trap. This specifically
    exercises `evalInstr`'s width-aware check (`a + 4 > s1.memory.size`, not merely `a >=
    s1.memory.size`) -- a model that only checked the start address would wrongly accept
    `65533..65535`. -/
def oobLoad32StraddleBoundary : WasmDiffCase :=
  { name := "oob_load32_straddle_boundary"
    instr := .block (.val .i32) [.local_get 0, .i32_load 2 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0x7A : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      let addrs : List UInt32 := [65530, 65531, 65532, 65533, 65534, 65535, 65536, 100000, 0xFFFFFFFC, 0xFFFFFFFF]
      for a in addrs do
        states := states ++ [{ locals := [WasmVal.i32 a], memory := mem }]
      for _ in [0:randCount] do
        let (bucket, r1) := curRng.nextNat 3
        let (raw, r2) := r1.nextUInt32
        let addr : UInt32 :=
          if bucket == 0 then UInt32.ofNat (65524 + (raw.toNat % 20))
          else if bucket == 1 then UInt32.ofNat (65536 + (raw.toNat % 16))
          else (0xFFFFFFFF : UInt32) - UInt32.ofNat (raw.toNat % 8)
        states := states ++ [{ locals := [WasmVal.i32 addr], memory := mem }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `i32.store` then immediate `i32.load` round trip at a straddling/boundary address, the 4-byte
    analogue of `oobStore8LoadRoundTripBoundary`: valid boundary addresses (`65532`, "at the
    limit") must round-trip the exact stored value; anything straddling or past the boundary
    (`65533..65535`, `65536`, `0xFFFFFFFF`) must have the STORE trap before the load ever runs. -/
def oobStore32LoadRoundTripBoundary : WasmDiffCase :=
  { name := "oob_store32_load_roundtrip_boundary"
    instr := .block (.val .i32)
      [.local_get 0, .local_get 1, .i32_store 2 0, .local_get 0, .i32_load 2 0]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      let addrs : List UInt32 := [65530, 65531, 65532, 65533, 65534, 65535, 65536, 100000, 0xFFFFFFFC, 0xFFFFFFFF]
      for a in addrs do
        for v in curated32BitValues.take 3 do
          states := states ++ [{ locals := [WasmVal.i32 a, WasmVal.i32 v], memory := mem }]
      for _ in [0:randCount] do
        let (bucket, r1) := curRng.nextNat 3
        let (raw, r2) := r1.nextUInt32
        let addr : UInt32 :=
          if bucket == 0 then UInt32.ofNat (65524 + (raw.toNat % 20))
          else if bucket == 1 then UInt32.ofNat (65536 + (raw.toNat % 16))
          else (0xFFFFFFFF : UInt32) - UInt32.ofNat (raw.toNat % 8)
        let (v, r3) := r2.nextUInt32
        states := states ++ [{ locals := [WasmVal.i32 addr, WasmVal.i32 v], memory := mem }]
        curRng := r3
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `i64.load` (8-byte width) straddling the boundary: `65528` is the last address whose full
    8-byte read stays in-bounds ("at the limit", `65528 + 8 = 65536`); `65529..65535` each
    straddle by 1-7 bytes ("unaligned near the boundary") and must trap; `65536` and `0xFFFFFFFF`
    must also trap. 64-bit analogue of `oobLoad32StraddleBoundary`, pinning the `a + 8 >
    s1.memory.size` check in `evalInstr`'s `.i64_load` case. -/
def oobLoad64StraddleBoundary : WasmDiffCase :=
  { name := "oob_load64_straddle_boundary"
    instr := .block (.val .i64) [.local_get 0, .i64_load 3 0]
    resultTypesFor := fun _ => [ValType.i64]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0xC3 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      let addrs : List UInt32 := [65526, 65527, 65528, 65529, 65530, 65531, 65535, 65536, 100000, 0xFFFFFFF8, 0xFFFFFFFF]
      for a in addrs do
        states := states ++ [{ locals := [WasmVal.i32 a], memory := mem }]
      for _ in [0:randCount] do
        let (bucket, r1) := curRng.nextNat 3
        let (raw, r2) := r1.nextUInt32
        let addr : UInt32 :=
          if bucket == 0 then UInt32.ofNat (65520 + (raw.toNat % 24))
          else if bucket == 1 then UInt32.ofNat (65536 + (raw.toNat % 16))
          else (0xFFFFFFFF : UInt32) - UInt32.ofNat (raw.toNat % 8)
        states := states ++ [{ locals := [WasmVal.i32 addr], memory := mem }]
        curRng := r2
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `i64.store` then immediate `i64.load` round trip at a straddling/boundary address, the 64-bit
    analogue of `oobStore32LoadRoundTripBoundary`. -/
def oobStore64LoadRoundTripBoundary : WasmDiffCase :=
  { name := "oob_store64_load_roundtrip_boundary"
    instr := .block (.val .i64)
      [.local_get 0, .local_get 1, .i64_store 3 0, .local_get 0, .i64_load 3 0]
    resultTypesFor := fun _ => [ValType.i64]
    genStates := fun rng randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      let mut curRng := rng
      let addrs : List UInt32 := [65526, 65527, 65528, 65529, 65530, 65531, 65535, 65536, 100000, 0xFFFFFFF8, 0xFFFFFFFF]
      for a in addrs do
        for v in curated64BitValues.take 3 do
          states := states ++ [{ locals := [WasmVal.i32 a, WasmVal.i64 v], memory := mem }]
      for _ in [0:randCount] do
        let (bucket, r1) := curRng.nextNat 3
        let (raw, r2) := r1.nextUInt32
        let addr : UInt32 :=
          if bucket == 0 then UInt32.ofNat (65520 + (raw.toNat % 24))
          else if bucket == 1 then UInt32.ofNat (65536 + (raw.toNat % 16))
          else (0xFFFFFFFF : UInt32) - UInt32.ofNat (raw.toNat % 8)
        let (v, r3) := r2.next
        states := states ++ [{ locals := [WasmVal.i32 addr, WasmVal.i64 v], memory := mem }]
        curRng := r3
      (states, curRng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `memory.grow` followed by `memory.size`, against a module (and matching model `memMax`)
    declaring `Limits.max = 4` pages starting from 1 page: growing by `0..3` pages stays within the
    declared maximum and must succeed on both engines, with `memory.size` afterward reflecting the
    actual growth (`1 + delta`). Paired with `memoryGrowExceedsDeclaredMax` below as the POSITIVE
    control proving this case's fuzzed vectors can genuinely distinguish success from failure,
    not just always trap or always succeed. -/
def memoryGrowWithinDeclaredMax : WasmDiffCase :=
  { name := "memory_grow_within_declared_max"
    instr := .block (.val .i32) [.local_get 0, .memory_grow, .drop, .memory_size]
    resultTypesFor := fun _ => [ValType.i32]
    memoryMaxPages := some 4
    genStates := fun rng _randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      for delta in [(0 : UInt32), 1, 2, 3] do
        states := states ++ [{ locals := [WasmVal.i32 delta], memory := mem, memMax := some 4 }]
      (states, rng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `memory.grow` requesting more pages than the module's declared `Limits.max` of `4` (starting
    from 1 page): the spec's non-determinism note ("Failure MUST occur if the referenced memory
    instance has a maximum size defined that would be exceeded") makes this the one `memory.grow`
    outcome that is NOT a free choice of the embedder -- both the model and the host MUST fail
    (push `-1`) and MUST NOT grow memory at all, so `memory.size` afterward must still read `1`
    (B8: the pre-fix model always grew unconditionally and could never produce this outcome). -/
def memoryGrowExceedsDeclaredMax : WasmDiffCase :=
  { name := "memory_grow_exceeds_declared_max"
    instr := .block (.val .i32) [.local_get 0, .memory_grow, .drop, .memory_size]
    resultTypesFor := fun _ => [ValType.i32]
    memoryMaxPages := some 4
    genStates := fun rng _randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let mut states : List WasmMachineState := []
      for delta in [(4 : UInt32), 5, 10, 1000] do
        states := states ++ [{ locals := [WasmVal.i32 delta], memory := mem, memMax := some 4 }]
      (states, rng) }

/- REF: wasm-exec-instructions#memory-instructions -/
/-- `memory.grow` requesting a delta so large (`~4 billion` pages, representable in an `i32` but
    utterly unaddressable) that it must fail even with NO declared `Limits.max` at all (`memMax :=
    none` on the model side, `memoryMaxPages := none` on the host module) -- this is the Wasm32
    address-space ceiling (2^16 pages / 4 GiB) that every 32-bit linear memory is implicitly bound
    by, independent of any author-declared maximum. Deliberately does NOT attempt to grow all the
    way to exactly `2^16` pages on either engine (a genuine ~4 GiB allocation would be slow, and
    environment-dependent, for a differential fuzz vector); this case only pins the "obviously over
    the ceiling" side of that boundary, which both engines reject before attempting any real
    allocation. The exact-ceiling boundary itself is intentionally left unexercised here -- see
    docs/TARGETS/WASM_ORACLE_HARNESS.md#9-out-of-bounds-and-memory-limit-fuzz-coverage. -/
def memoryGrowExceedsHardCeilingNoDeclaredMax : WasmDiffCase :=
  { name := "memory_grow_exceeds_hard_ceiling"
    instr := .block (.val .i32) [.local_get 0, .memory_grow, .drop, .memory_size]
    resultTypesFor := fun _ => [ValType.i32]
    genStates := fun rng _randCount => Id.run do
      let mem := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
      let states : List WasmMachineState :=
        [ { locals := [WasmVal.i32 (4000000000 : UInt32)], memory := mem }
        , { locals := [WasmVal.i32 (0xFFFFFFFF : UInt32)], memory := mem }
        , { locals := [WasmVal.i32 (70000 : UInt32)], memory := mem } ]
      (states, rng) }

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#9-out-of-bounds-and-memory-limit-fuzz-coverage -/
/-- The B7/B8 out-of-bounds-access and memory-limit fuzz suite: OOB load/store at, one past, and
    far past the boundary of a one-page memory (8/32/64-bit widths, including straddling and
    `0xFFFFFFFF` addresses), plus `memory.grow` against a declared `Limits.max` (both the success
    and the mandatory-failure side) and against the implicit Wasm32 page-count ceiling with no
    declared maximum at all. -/
def allMemoryLimitCases : List WasmDiffCase := [
  oobLoad8AtBoundary,
  oobStore8LoadRoundTripBoundary,
  oobLoad32StraddleBoundary,
  oobStore32LoadRoundTripBoundary,
  oobLoad64StraddleBoundary,
  oobStore64LoadRoundTripBoundary,
  memoryGrowWithinDeclaredMax,
  memoryGrowExceedsDeclaredMax,
  memoryGrowExceedsHardCeilingNoDeclaredMax
]

/- REF: wasm-exec-instructions#control-instructions -/
/-- Comprehensive suite of structured control-flow test cases (block/loop/if_else nesting
    br/br_if/return_op), differentially validated against the host Wasm engine. -/
def allControlFlowCases : List WasmDiffCase := [
  cfBlockArithBr0,
  cfBlockArithBr0I64,
  cfBrDepth0,
  cfBrDepth1,
  cfBrDepth2,
  cfIfElseArms,
  cfBrIfTakenNotTaken,
  cfLoopBoundedSum,
  cfLoopReentersViaBrZero,
  cfBrEscapesLoopDepth2,
  cfLoopBrOneEscapesToBlock,
  cfReturnFromNesting,
  cfTrapInsideNestedBlocks,
  cfStoreLoadRoundTrip32,
  cfStoreLoadRoundTrip64,
  cfStore8LoadRoundTrip,
  cfStoreI32ThenLoadByte0Endianness
]

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#6-mandatory-oracle-sanity-controls -/
/-- Runs three mandatory sanity checks against the host oracle before any real fuzz vector is
    allowed to count, and ABORTS the entire fuzz session (via `IO.userError`, uncaught) if any of
    them fails - an oracle that cannot be trusted must not be allowed to silently report a green
    suite. (1) POSITIVE: `i32.const 42` must run and return exactly `42` - this is what fails if
    `node` is missing from PATH entirely (the spawn fails, `runWasmHostExecution` reports
    `OracleFailure.processError`, which can never equal the expected `WasmRunOutcome.ran`). (2)
    NEGATIVE: a module declaring one i32 result whose body is `nop` (which produces none) must be
    rejected as `OracleFailure.invalidModule` - this is the exact "fallthru arity" class that
    silently reported PASS before this fix cycle for `br_depth1_nested`, `br_depth2_nested`,
    `loop_bounded_sum_brif`, and the pre-existing `local_tee` case. (3) TRAP: `1 / 0` (`i32.div_u`)
    must be reported as a genuine `WasmRunOutcome.trapped`, not conflated with either of the above. -/
def runMandatoryOracleControls : IO Unit := do
  let posModule := buildTestWasmModuleForResults (.i32_const 42) [ValType.i32]
  let posOutcome ← runWasmHostExecution posModule
  match posOutcome with
  | .ok (.ran [WasmVal.i32 42]) => pure ()
  | other =>
    throw <| IO.userError s!"MANDATORY POSITIVE CONTROL FAILED: expected the host to run `i32.const 42` and return 42, got [{describeOracleResult other}]. The host oracle (node) cannot be trusted - is `node` on PATH? Aborting the entire fuzz session rather than report a possibly-fake result."

  let negModule := buildTestWasmModuleForResults .nop [ValType.i32]
  let negOutcome ← runWasmHostExecution negModule
  match negOutcome with
  | .error (.invalidModule _) => pure ()
  | other =>
    throw <| IO.userError s!"MANDATORY NEGATIVE CONTROL FAILED: a deliberately ill-typed module (declares one i32 result, body is `nop` and produces none) was NOT rejected as invalid by the host - got [{describeOracleResult other}]. The oracle can no longer distinguish a rejected module from a real answer. Aborting."

  let trapModule := buildTestWasmModuleForResults .i32_div_u [ValType.i32] [] none [.i32_const 1, .i32_const 0]
  let trapOutcome ← runWasmHostExecution trapModule
  match trapOutcome with
  | .ok (.trapped _) => pure ()
  | other =>
    throw <| IO.userError s!"MANDATORY TRAP CONTROL FAILED: `1 / 0` (i32.div_u) was expected to genuinely trap at runtime, got [{describeOracleResult other}]. The oracle can no longer distinguish a real trap from module rejection or any other outcome. Aborting."

  IO.println "  [CONTROL] positive / negative / trap host-oracle sanity checks passed"
  IO.println "--------------------------------------------------------------------------------"

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#6-mandatory-oracle-sanity-controls -/
/-- Per-process memo of whether `runMandatoryOracleControls` has already run. Backs
    `ensureOracleControlsRan` below; not meant to be read or written from anywhere else. -/
initialize oracleControlsRanRef : IO.Ref Bool ← IO.mkRef false

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#6-mandatory-oracle-sanity-controls -/
/-- Runs `runMandatoryOracleControls` exactly once per process, memoized via
    `oracleControlsRanRef`. `verifyWasmDiffCase` calls this itself (see below) so that testing a
    single case is *structurally* incapable of skipping the controls - there is no visibility
    modifier that would stop a caller in this same file from invoking `verifyWasmDiffCase`
    directly, bypassing `runWasmSemanticsFuzzerSuite`, so the guarantee is placed on the callee
    instead of relied upon at only one call site. -/
def ensureOracleControlsRan : IO Unit := do
  let alreadyRan ← oracleControlsRanRef.get
  if !alreadyRan then
    runMandatoryOracleControls
    oracleControlsRanRef.set true

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#7-per-case-verification-and-reporting -/
/-- Verifies a single `WasmDiffCase` against the host Wasm runtime oracle. Runs a pre-module
    sanity assert first (the case's declared `resultTypesFor` must match what the Lean model
    itself actually produced, when it didn't trap) so an authoring bug in a case is reported as
    such directly rather than only surfacing as a downstream host mismatch. The host comparison
    then matches exhaustively on `WasmOracleResult`: `OracleFailure.invalidModule` and
    `OracleFailure.processError` are ALWAYS hard failures of the vector (there is no arm that lets
    either fall through as a pass), `WasmRunOutcome.trapped` is compared against the model's own
    `trapped` flag, and `WasmRunOutcome.ran` is compared value-for-value against the model's
    stack. Always begins by calling `ensureOracleControlsRan` (a once-per-process memoized call to
    `runMandatoryOracleControls`), so a case can never be verified against an oracle that has not
    itself been sanity-checked, regardless of what calls this function or in what order. -/
def verifyWasmDiffCase (tc : WasmDiffCase) (rng : FuzzerRng) (maxStates : Nat := 50) : IO (WasmInstructionDiffResult × FuzzerRng) := do
  ensureOracleControlsRan
  let (allStates, nextRng) := tc.genStates rng maxStates
  let statesToTest := allStates.take maxStates
  -- TC17 (TCB.md T11-b; docs/REVIEW.md Law 13): 0 fuzzable states — whether `canFuzzWasmRuntime`
  -- excludes the instruction or generation otherwise yielded nothing — is a zero-vector case and
  -- must report SKIP, never PASS. `reportWasmDiffResult` relies on `skipped` to keep it out of
  -- both `totalInstrsPassed` and the printed [PASS] line.
  if statesToTest.isEmpty then
    return (WasmInstructionDiffResult.mk false tc.name 0 0 (some "SKIP: 0 fuzzable host states for this case (0 vectors tested, not a pass)") true, nextRng)

  let mut failed := 0
  let mut firstErr : Option String := none

  for i in [0:statesToTest.length] do
    let initS := statesToTest[i]!
    let modelS := stepWasm tc.instr initS
    let resultTypes := tc.resultTypesFor initS

    let mut skipHost := false
    if !modelS.trapped then
      let stackTypes := modelS.stack.map (fun v => match v with | WasmVal.i32 _ => ValType.i32 | WasmVal.i64 _ => ValType.i64)
      if stackTypes != resultTypes then
        failed := failed + 1
        skipHost := true
        if firstErr.isNone then
          firstErr := some s!"Case '{tc.name}' vector {i+1}: AUTHORING BUG - declared resultTypesFor {repr resultTypes} but the Lean model itself produced stack {repr modelS.stack}. Fix the case before trusting any host comparison."

    if !skipHost then
      let preInstrs := tc.preInstrsFor initS
      let m := buildTestWasmModuleForResults tc.instr resultTypes initS.locals (some initS.memory) preInstrs tc.memoryMaxPages
      let hostOutcome ← runWasmHostExecution m

      match hostOutcome with
      | .error (.invalidModule msg) =>
        failed := failed + 1
        if firstErr.isNone then
          firstErr := some s!"Case '{tc.name}' vector {i+1}: HOST REJECTED THE MODULE AS INVALID (a Wasm validation error, not a runtime trap) - {msg}"
      | .error (.processError msg) =>
        failed := failed + 1
        if firstErr.isNone then
          firstErr := some s!"Case '{tc.name}' vector {i+1}: ORACLE FAILURE (no trustworthy host answer obtained) - {msg}"
      | .ok (.trapped hostMsg) =>
        if !modelS.trapped then
          failed := failed + 1
          if firstErr.isNone then
            firstErr := some s!"Case '{tc.name}' vector {i+1}: Model expected success, but host genuinely trapped - {hostMsg}"
      | .ok (.ran hostResults) =>
        if modelS.trapped then
          failed := failed + 1
          if firstErr.isNone then
            firstErr := some s!"Case '{tc.name}' vector {i+1}: Model expected TRAP, but host runtime succeeded with {repr hostResults}."
        else
          match hostResults, modelS.stack with
          | [hostVal], [modelVal] =>
            if hostVal != modelVal then
              failed := failed + 1
              if firstErr.isNone then
                firstErr := some s!"Case '{tc.name}' vector {i+1}: Result mismatch! Model={(repr modelVal).pretty}, Host={(repr hostVal).pretty}"
          | [], [] => pure ()
          | _, _ =>
            failed := failed + 1
            if firstErr.isNone then
              firstErr := some s!"Case '{tc.name}' vector {i+1}: Stack count mismatch! Model={(repr modelS.stack).pretty}, Host={(repr hostResults).pretty}"

  let passed := failed == 0
  pure (WasmInstructionDiffResult.mk passed tc.name statesToTest.length failed firstErr false, nextRng)

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#7-per-case-verification-and-reporting -/
/-- Prints one case's PASS/FAIL/SKIP line and folds it into the running totals. A `skipped`
result (see `WasmInstructionDiffResult`) is reported distinctly from both PASS and FAIL and never
increments `passedCount` — TC17 (TCB.md T11-b; docs/REVIEW.md Law 13): a zero-vector case must
never read as a clean pass. -/
def reportWasmDiffResult (res : WasmInstructionDiffResult) (passedCount failedCount skippedCount vectorsTested : Nat) : IO (Nat × Nat × Nat × Nat) := do
  let vectorsTested' := vectorsTested + res.totalTested
  if res.skipped then
    let padLen := 32 - min 32 res.mnemonic.length
    let skipReason := res.errorMessage.getD "no fuzzable host states"
    IO.println s!"  [SKIP] {res.mnemonic.pushn ' ' padLen} (0 test vectors — {skipReason})"
    pure (passedCount, failedCount, skippedCount + 1, vectorsTested')
  else if res.passed then
    let padLen := 32 - min 32 res.mnemonic.length
    IO.println s!"  [PASS] {res.mnemonic.pushn ' ' padLen} ({res.totalTested} test vectors verified exact)"
    pure (passedCount + 1, failedCount, skippedCount, vectorsTested')
  else
    let errStr := res.errorMessage.getD "Unknown failure"
    IO.println s!"  [FAIL] {res.mnemonic}:\n{errStr}"
    pure (passedCount, failedCount + 1, skippedCount, vectorsTested')

/- REF: docs/VISION.md#32-the-models-must-be-faithful-to-reality -/
/-- The number of distinct host Wasm engines this build's oracle actually executed against.
Currently exactly one: the `node` runtime spawned by `runWasmHostExecution`. Surfacing this
number keeps a green run's evidentiary scope visible rather than implied
(docs/VISION.md#32-the-models-must-be-faithful-to-reality; TCB.md T11). -/
def enginesValidated : Nat := 1

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Runs the comprehensive WebAssembly differential semantics fuzzer across all instruction and
    control-flow models. Begins with `ensureOracleControlsRan` for an immediate, up-front
    `[CONTROL]` line; `verifyWasmDiffCase` also calls it per-case (a no-op after the first time),
    so the controls gate is enforced regardless of entry point, not just here.

    TC17 nonzero-vector floor (TCB.md T11-b; docs/REVIEW.md Law 13, Findings Become Gates): a run
    that exercises zero host-engine test vectors — whether because every candidate's
    `canFuzzWasmRuntime` is false, an `--instruction` filter matched nothing, or the candidate
    suite itself is empty — must hard-fail rather than report a clean summary. The floor fires
    unconditionally, even when the zero-vector state is reached through a legitimate
    precondition — detect-and-fail, not detect-and-explain. -/
def runWasmSemanticsFuzzerSuite (iterationsPerInstr : Nat := 50) (initialSeed : UInt64 := 88172645463325252) (instrFilter : Option String := none) : IO (Nat × Nat × Nat) := do
  IO.println "================================================================================"
  IO.println "  Gasm WebAssembly Differential Semantic Fuzzer (Host Engine vs Lean Model)"
  IO.println "================================================================================"

  ensureOracleControlsRan

  let mut curRng : FuzzerRng := FuzzerRng.mk initialSeed
  let mut totalInstrsPassed := 0
  let mut totalInstrsFailed := 0
  let mut totalInstrsSkipped := 0
  let mut totalVectorsTested := 0

  let candidateLeafCases := match instrFilter with
    | some filterStr => allLeafDiffCases.filter (fun (c : WasmDiffCase) => c.name.toLower.contains filterStr.toLower)
    | none => allLeafDiffCases

  for tc in candidateLeafCases do
    let (res, nextRng) ← verifyWasmDiffCase tc curRng iterationsPerInstr
    curRng := nextRng
    let (p, f, s, v) ← reportWasmDiffResult res totalInstrsPassed totalInstrsFailed totalInstrsSkipped totalVectorsTested
    totalInstrsPassed := p
    totalInstrsFailed := f
    totalInstrsSkipped := s
    totalVectorsTested := v

  let candidateControlFlowCases := match instrFilter with
    | some filterStr => allControlFlowCases.filter (fun (c : WasmDiffCase) => c.name.toLower.contains filterStr.toLower)
    | none => allControlFlowCases

  if !candidateControlFlowCases.isEmpty then
    IO.println "--------------------------------------------------------------------------------"
    IO.println "  Structured Control Flow (block / loop / if_else / br / br_if / return)"
    IO.println "--------------------------------------------------------------------------------"

  for tc in candidateControlFlowCases do
    let (res, nextRng) ← verifyWasmDiffCase tc curRng iterationsPerInstr
    curRng := nextRng
    let (p, f, s, v) ← reportWasmDiffResult res totalInstrsPassed totalInstrsFailed totalInstrsSkipped totalVectorsTested
    totalInstrsPassed := p
    totalInstrsFailed := f
    totalInstrsSkipped := s
    totalVectorsTested := v

  let candidateMemoryLimitCases := match instrFilter with
    | some filterStr => allMemoryLimitCases.filter (fun (c : WasmDiffCase) => c.name.toLower.contains filterStr.toLower)
    | none => allMemoryLimitCases

  if !candidateMemoryLimitCases.isEmpty then
    IO.println "--------------------------------------------------------------------------------"
    IO.println "  Out-of-Bounds Access & Memory-Limit Coverage (B7/B8)"
    IO.println "--------------------------------------------------------------------------------"

  for tc in candidateMemoryLimitCases do
    let (res, nextRng) ← verifyWasmDiffCase tc curRng iterationsPerInstr
    curRng := nextRng
    let (p, f, s, v) ← reportWasmDiffResult res totalInstrsPassed totalInstrsFailed totalInstrsSkipped totalVectorsTested
    totalInstrsPassed := p
    totalInstrsFailed := f
    totalInstrsSkipped := s
    totalVectorsTested := v

  let candidateCount := candidateLeafCases.length + candidateControlFlowCases.length + candidateMemoryLimitCases.length
  IO.println "--------------------------------------------------------------------------------"
  -- TC17 vacuity floor: 0 vectors exercised is a hard failure, never a clean summary.
  if totalVectorsTested == 0 then
    IO.println s!"[VACUITY FLOOR TRIPPED] 0 host-engine test vectors were exercised across {candidateCount} candidate case(s) ({totalInstrsSkipped} skipped, {totalInstrsPassed} fuzzed-and-passed, {totalInstrsFailed} fuzzed-and-failed)."
    IO.println "A fuzzer run that exercises zero vectors has verified nothing — this is a hard FAIL, not a clean PASS (TCB.md T11-b; docs/REVIEW.md Law 13)."
    IO.println "================================================================================"
    return (totalInstrsPassed, max 1 (totalInstrsFailed + totalInstrsSkipped), totalVectorsTested)
  IO.println s!"Summary: {totalInstrsPassed} passed, {totalInstrsFailed} failed, {totalInstrsSkipped} skipped ({totalVectorsTested} total test vectors)"
  IO.println s!"[Evidentiary Scope] Validated on exactly {enginesValidated} host engine(s) (Node.js WebAssembly runtime)."
  IO.println "================================================================================"
  pure (totalInstrsPassed, totalInstrsFailed, totalVectorsTested)

/- REF: wasm-exec-runtime#administrative-instructions -/
/-- Pins `evalInstr`'s trap short-circuit guard (Semantics.lean: `if s.trapped || s.exitCode.isSome
    then (s, .next) else ...`) directly against the Lean model, independent of the host oracle:
    once `i32_div_u` traps on `5 / 0`, no trailing instruction may mutate the operand stack
    further, so the two instructions after the trap (`i32.const 999, i32.add`) must be no-ops and
    the final stack must be empty. Checked here rather than via a `WasmDiffCase` because a real
    trap aborts the exported function's call before it ever returns to the host - no engine can
    report what the operand stack "would have been" after a trap (`test_fn()` simply throws in
    JS), so this specific invariant is unobservable through the black-box host comparison every
    case above relies on, and must be pinned against the model directly instead.

    This is a GROUND INSTANCE on one fixed instruction sequence and one fixed initial state, not a
    proposition universally quantified over a domain - per Law 8's `*_inst` convention it is named
    and suffixed accordingly, and is NOT presented as a general soundness theorem. It uses
    `native_decide` rather than `decide`: `evalInstr`/`evalInstrs`/`evalLoop` are `partial def`s
    (matching this codebase's existing Equivalence.lean spikes), and `decide` was confirmed by
    hand to get stuck attempting to unfold them ("did not reduce to `isTrue` or `isFalse`"),
    whereas `native_decide` compiles and executes the check directly. Per Law 10, this
    single-instance `native_decide` use needs an axiom-level-gate allowlist entry at merge time.

    Mutation-tested by hand: temporarily deleting the `s.trapped ||` guard in Semantics.lean's
    `evalInstr` makes this fail to close (the mutated model instead leaves `[.i32 999]` on the
    stack, since `i32_add` pops the missing second operand as the interpreter's own default-zero
    fallback); reverted immediately after confirming the failure. -/
theorem trapShortCircuitGuard_inst :
    (stepWasm
      (.block (.val .i32) [.i32_const 5, .i32_const 0, .i32_div_u, .i32_const 999, .i32_add])
      {}).stack = [] := by native_decide

end Gasm.Targets.Wasm.SemanticsFuzzer

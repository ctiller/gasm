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
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Linker
import Gasm.Targets.Wasm.Semantics

namespace Gasm.Targets.Wasm.HostOracle

open Gasm.Core
open Gasm.Targets.Wasm

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#3-oracle-result-types -/
/-- The successful outcome of running a *validated* host module: it either produced a definite
    result value, or it genuinely trapped at runtime (e.g. `unreachable`, integer division by
    zero, an out-of-bounds memory access). Both are legitimate outcomes to compare against the
    Lean model. This type has no constructor for "the module didn't run" or "the output was
    unparseable" - an oracle malfunction is a different type entirely (`OracleFailure`), so a
    caller pattern-matching a `WasmRunOutcome` can never mistake a malfunction for a real answer. -/
inductive WasmRunOutcome where
  | ran     : List WasmVal → WasmRunOutcome
  | trapped : String → WasmRunOutcome
  deriving Repr, Inhabited

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#3-oracle-result-types -/
/-- A failure of the host oracle itself, as distinct from any real outcome of running the module
    under test: the synthesized module never validated (almost always a bug in the *test case*,
    not the interpreter under test - see `verifyWasmDiffCase`'s pre-module sanity check for the
    other half of that story), or the harness could not obtain a trustworthy answer at all (node
    could not be spawned, exited non-zero, hung past its timeout, or printed something the parser
    does not recognise). Every one of these is a hard failure of the corresponding fuzz vector;
    there is deliberately no path from `OracleFailure` back into `WasmRunOutcome`. -/
inductive OracleFailure where
  | invalidModule : String → OracleFailure
  | processError  : String → OracleFailure
  deriving Repr, Inhabited

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#3-oracle-result-types -/
/-- Outcome of attempting to run a synthesized test module on the host engine: either a definite
    `WasmRunOutcome` (a real answer, comparable against the Lean model) or an `OracleFailure` (the
    module didn't validate, or the harness itself malfunctioned). `Except` forces every caller to
    handle both arms explicitly - there is no default/`Inhabited`-style escape hatch that could
    turn a failure into a silently-accepted result. -/
abbrev WasmOracleResult := Except OracleFailure WasmRunOutcome

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#3-oracle-result-types -/
/-- Human-readable rendering of a `WasmOracleResult` for diagnostics, without depending on
    `Except` itself having a `Repr` instance. -/
def describeOracleResult : WasmOracleResult → String
  | .ok (.ran vs)          => s!"ran -> {repr vs}"
  | .ok (.trapped msg)     => s!"trapped -> {msg}"
  | .error (.invalidModule msg) => s!"invalidModule -> {msg}"
  | .error (.processError msg)  => s!"processError -> {msg}"

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#4-stack-reconstruction-for-synthesized-test-modules -/
/-- Reconstructs the instructions needed to push a captured operand stack (top-of-stack first)
    back onto an empty stack, bottom-up, so it can be replayed as the prefix of a test module's
    function body. -/
def stackSetupInstrs (initialStack : List WasmVal) : List WasmInstr :=
  initialStack.reverse.map fun v => match v with
    | WasmVal.i32 u => WasmInstr.i32_const u
    | WasmVal.i64 u => WasmInstr.i64_const u

/- REF: wasm-valid-instructions#instructions -/
/-- Infers the declared Wasm result type for a single *leaf* instruction given the state it is
    about to run against. The type can depend on the state itself - `select_op` and `local_get` /
    `local_tee` return whichever of i32/i64 the operands actually are - not just on the
    instruction's opcode, which is why this is a function of state rather than a static per-case
    field. This is the leaf-instruction half of `WasmDiffCase.resultTypesFor`; structured
    control-flow cases instead supply a state-independent result type directly, since their
    top-level instruction is already a self-contained compound construct. -/
def inferLeafResultTypes (instr : WasmInstr) (initialStack : List WasmVal) (initialLocals : List WasmVal) : List ValType :=
  match instr with
  | .i32_add | .i32_sub | .i32_mul | .i32_div_u | .i32_rem_u | .i32_and | .i32_or | .i32_xor
  | .i32_shl | .i32_shr_u | .i32_eqz | .i32_eq | .i32_ne | .i32_lt_u | .i32_gt_u | .i32_le_u | .i32_ge_u
  | .i32_load _ _ | .i32_load8_u _ _ | .i32_wrap_i64 | .i64_eqz | .i64_eq | .i64_ne | .i64_lt_u | .i64_gt_u | .i64_le_u | .i64_ge_u
  | .memory_size | .memory_grow => [ValType.i32]
  | .i64_add | .i64_sub | .i64_mul | .i64_div_u | .i64_rem_u | .i64_and | .i64_or | .i64_xor
  | .i64_shl | .i64_shr_u | .i64_load _ _ | .i64_extend_i32_u => [ValType.i64]
  | .select_op =>
    match initialStack with
    | _cond :: val1 :: _ => match val1 with | WasmVal.i32 _ => [ValType.i32] | WasmVal.i64 _ => [ValType.i64]
    | _ => [ValType.i32]
  | .local_get idx =>
    if let some (WasmVal.i64 _) := initialLocals[idx]? then [ValType.i64] else [ValType.i32]
  | .local_tee idx =>
    -- `local.tee` leaves its operand on the stack (unlike `local.set`, which consumes it and
    -- therefore correctly falls into the `[]` case below). A test module that omits this case
    -- declares zero results while the body leaves one value behind - an arity mismatch that V8
    -- rejects as invalid, which a `trapped`-only comparator then silently excuses (see the
    -- `local_tee` fix in `mkLeafCase` / the suite's mandatory negative control for exactly this
    -- class of bug).
    if let some (WasmVal.i64 _) := initialLocals[idx]? then [ValType.i64] else [ValType.i32]
  | .i32_const _ => [ValType.i32]
  | .i64_const _ => [ValType.i64]
  | _ => []

/- REF: wasm-syntax-modules#functions -/
/-- Synthesizes a test Wasm module: an exported zero-parameter function whose body first sets up
    the given locals, then runs `preInstrs` (e.g. reconstructing a captured operand stack via
    `stackSetupInstrs`), then runs the instruction under test, declared to produce exactly
    `resultTypes`. This is the single builder shared by the leaf-instruction suite (which derives
    `resultTypes` / `preInstrs` from the instruction and state via `inferLeafResultTypes` /
    `stackSetupInstrs`) and the structured control-flow suite (which supplies both directly, since
    its instruction is already compound and self-contained).

    `memoryMaxPages` (B7/B8, docs/TARGETS/WASM_ORACLE_HARNESS.md#9-out-of-bounds-and-memory-limit-fuzz-coverage)
    forwards straight into the built `WasmModule`'s own `memoryMaxPages` (`Linker.lean`), so a
    `WasmDiffCase` that fuzzes `memory.grow` against a declared `Limits.max` can declare the SAME
    maximum on the host module that the Lean model's fuzzed `WasmMachineState.memMax` uses --
    without this, the host engine would have no maximum at all and could never genuinely refuse a
    `memory.grow` the model is exercising the failure path for. `none` (the default) preserves
    the previous no-max encoding exactly for every case that doesn't pass this parameter. -/
def buildTestWasmModuleForResults (instr : WasmInstr) (resultTypes : List ValType)
    (initialLocals : List WasmVal := []) (initialMemory : Option ByteArray := none)
    (preInstrs : List WasmInstr := []) (memoryMaxPages : Option UInt32 := none) : WasmModule := Id.run do
  let localTypes : List ValType := initialLocals.map fun v => match v with | WasmVal.i32 _ => ValType.i32 | WasmVal.i64 _ => ValType.i64
  let mut localSetup : List WasmInstr := []
  for idx in [0:initialLocals.length] do
    let val := initialLocals[idx]!
    match val with
    | WasmVal.i32 u => localSetup := localSetup ++ [.i32_const u, .local_set idx]
    | WasmVal.i64 u => localSetup := localSetup ++ [.i64_const u, .local_set idx]

  let body := localSetup ++ preInstrs ++ [instr]

  let fn : WasmFunction := {
    name := "test_fn",
    exportName := some "test_fn",
    params := [],
    results := resultTypes,
    locals := localTypes,
    body := body
  }

  let memPages : Option UInt32 := match initialMemory with
    | some mem =>
      if mem.size > 0 then some (UInt32.ofNat ((mem.size + 65535) / 65536)) else some 1
    | none => none

  let dataSegments : List WasmDataSegment := match initialMemory with
    | some mem =>
      if mem.size > 0 && mem.data.any (fun b => b != 0) then
        [{ offset := 0, data := mem }]
      else []
    | none => []

  { functions := [fn], memoryPages := memPages, dataSegments := dataSegments, memoryMaxPages := memoryMaxPages }

/- REF: docs/TARGETS/WASM_ORACLE_HARNESS.md#2-host-oracle-process-model -/
/-- Executes a synthesized Wasm test module on the host Node.js engine and classifies the outcome.
    The generated node script validates the module (`new WebAssembly.Module(...)`) in a try/catch
    entirely separate from - and prior to - instantiation/execution, so a module V8 rejects is
    reported as `OracleFailure.invalidModule` and can never be confused with a genuine runtime
    trap (`WasmRunOutcome.trapped`) the way a single shared `catch` previously conflated the two.
    Every path that cannot produce a trustworthy `WasmRunOutcome` - a non-zero node exit, a hung
    process past `timeoutMs` (killed and reaped), unparseable stdout, or a spawn failure - produces
    `OracleFailure.processError` rather than defaulting to any `WasmRunOutcome` constructor. The
    temp `.wasm` file is named from the current process id and a monotonic timestamp so concurrent
    fuzzer invocations never contend for the same path, and is always removed before returning. -/
def runWasmHostExecution (m : WasmModule) (timeoutMs : Nat := 10000) : IO WasmOracleResult := do
  let typeSigs := collectTypeSignatures m

  let pid ← IO.Process.getPID
  let nowMs ← IO.monoMsNow
  let tmpWasmPath := s!".tmp_wasm_fuzzer_{pid}_{nowMs}.wasm"

  let result ← try
      -- `emitWasmBinary` is fail-closed (the Wasm fail-closed emission contract): a genuine type-index mismatch surfaces
      -- here as `Except.error` rather than silently encoding index 0. Matched explicitly (rather
      -- than `IO.ofExcept`) and folded into `OracleFailure.processError` so it stays inside this
      -- function's own no-escape-hatch `Except` discipline instead of escaping as an uncaught
      -- `IO` exception. `typeSigs` is derived from `m` itself via `collectTypeSignatures`, so in
      -- practice this path is unreachable for any module this fuzzer synthesizes; it is handled
      -- explicitly anyway rather than assumed.
      let bytes ← match emitWasmBinary m typeSigs with
        | .error e => throw (IO.userError s!"emitWasmBinary failed: {e}")
        | .ok bytes => pure bytes
      IO.FS.writeBinFile tmpWasmPath bytes

      let nodeScript :=
        "const fs = require('fs'); const wasm = fs.readFileSync('" ++ tmpWasmPath ++ "'); " ++
        "let mod; try { mod = new WebAssembly.Module(wasm); } catch (e) { console.log('INVALID:' + e.message); process.exit(0); } " ++
        "WebAssembly.instantiate(mod).then(instance => { " ++
        "  try { " ++
        "    const res = instance.exports.test_fn(); " ++
        "    if (typeof res === 'bigint') { console.log('I64:' + BigInt.asUintN(64, res).toString()); } " ++
        "    else if (typeof res === 'number') { console.log('I32:' + (res >>> 0).toString()); } " ++
        "    else { console.log('VOID'); } " ++
        "  } catch (e) { console.log('TRAP:' + e.message); } " ++
        "}).catch(e => console.log('TRAP:' + e.message));"

      let child ← IO.Process.spawn {
        cmd := "node"
        args := #["-e", nodeScript]
        stdout := .piped
        stderr := .piped
      }

      -- Poll for exit with a hard deadline instead of blocking on `wait` forever: a runaway
      -- process (e.g. a genuine interpreter/engine bug producing a real infinite loop) must fail
      -- the vector loudly, not hang the whole fuzzer session.
      let stepMs : UInt32 := 50
      let steps := (timeoutMs + 49) / 50
      let mut exitCode? : Option UInt32 := none
      for _ in [0:steps] do
        if exitCode?.isNone then
          match ← child.tryWait with
          | some code => exitCode? := some code
          | none => IO.sleep stepMs

      match exitCode? with
      | none =>
        child.kill
        let _ ← child.wait
        -- Drain (rather than ignore) whatever the killed process had already buffered, so the
        -- pipe is not left holding data and the handle can be released cleanly.
        let _ ← child.stdout.readToEnd
        let _ ← child.stderr.readToEnd
        pure (Except.error (OracleFailure.processError s!"node did not exit within {timeoutMs}ms (killed as a hang) while running a synthesized module"))
      | some exitCode =>
        let stdout ← child.stdout.readToEnd
        let stderr ← child.stderr.readToEnd
        if exitCode != 0 then
          pure (Except.error (OracleFailure.processError s!"node exited with code {exitCode}: {stderr}"))
        else
          let trimmed := stdout.trimAscii.toString
          if trimmed.startsWith "INVALID:" then
            pure (Except.error (OracleFailure.invalidModule (trimmed.drop 8).toString))
          else if trimmed.startsWith "I32:" then
            match (trimmed.drop 4).toNat? with
            | some n => pure (Except.ok (WasmRunOutcome.ran [WasmVal.i32 (UInt32.ofNat n)]))
            | none => pure (Except.error (OracleFailure.processError s!"unparseable I32 output: {trimmed}"))
          else if trimmed.startsWith "I64:" then
            match (trimmed.drop 4).toNat? with
            | some n => pure (Except.ok (WasmRunOutcome.ran [WasmVal.i64 (UInt64.ofNat n)]))
            | none => pure (Except.error (OracleFailure.processError s!"unparseable I64 output: {trimmed}"))
          else if trimmed.startsWith "TRAP:" then
            pure (Except.ok (WasmRunOutcome.trapped (trimmed.drop 5).toString))
          else if trimmed == "VOID" then
            pure (Except.ok (WasmRunOutcome.ran []))
          else
            pure (Except.error (OracleFailure.processError s!"unexpected runtime output: {trimmed}"))
    catch e =>
      pure (Except.error (OracleFailure.processError s!"host runner error: {e}"))

  (try IO.FS.removeFile tmpWasmPath catch _ => pure ())
  pure result

end Gasm.Targets.Wasm.HostOracle

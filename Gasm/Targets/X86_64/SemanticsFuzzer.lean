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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Imul
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Test
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Neg
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Cmov
import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.HardwareHarness
import Gasm.Targets.X86_64.Registry

namespace Gasm.Targets.X86_64.SemanticsFuzzer

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.HardwareHarness
open Gasm.Targets.X86_64.Registry

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- All 15 general-purpose registers tested for ALU operations (excluding stack pointer). -/
def allRegs64 : List Reg64 := [
  .rax, .rcx, .rdx, .rbx, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15
]

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- All 16 32-bit general-purpose sub-registers. -/
def allRegs32 : List Reg32 := [
  .eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi,
  .r8d, .r9d, .r10d, .r11d, .r12d, .r13d, .r14d, .r15d
]

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Result structure for instruction semantic verification against CPU hardware. `skipped` is
    true only for instructions whose `canFuzzHardware` is false (e.g. RSP-relative operations
    that cannot be safely executed in-place on the host thread's own stack) — these are never
    actually fuzzed against hardware and must be reported distinctly from a genuine pass, not
    folded into the same "passed" count with 0 vectors tested. -/
structure InstructionDiffResult where
  passed       : Bool
  mnemonic     : String
  totalTested  : Nat
  failedCount  : Nat
  errorMessage : Option String := none
  skipped      : Bool := false
  deriving Inhabited

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Formats flag differences between Lean model and hardware. -/
def formatFlagDiff (modelFlags hwFlags : UInt64) : String :=
  let cfM := (modelFlags &&& 1) != 0
  let cfH := (hwFlags &&& 1) != 0
  let pfM := (modelFlags &&& 4) != 0
  let pfH := (hwFlags &&& 4) != 0
  let afM := (modelFlags &&& 16) != 0
  let afH := (hwFlags &&& 16) != 0
  let zfM := (modelFlags &&& 64) != 0
  let zfH := (hwFlags &&& 64) != 0
  let sfM := (modelFlags &&& 128) != 0
  let sfH := (hwFlags &&& 128) != 0
  let ofM := (modelFlags &&& 2048) != 0
  let ofH := (hwFlags &&& 2048) != 0
  let mStr := formatHex64 modelFlags
  let hStr := formatHex64 hwFlags
  s!"Model: [CF={cfM}, PF={pfM}, AF={afM}, ZF={zfM}, SF={sfM}, OF={ofM}] (raw: {mStr})\n  HW:    [CF={cfH}, PF={pfH}, AF={afH}, ZF={zfH}, SF={sfH}, OF={ofH}] (raw: {hStr})"

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Verifies an instruction instance across its typeclass-generated fuzz test states against CPU hardware. -/
def verifyInstructionSemantics (pkg : AnyX86_64Instruction) (rng : FuzzerRng) (maxStates : Nat := 150) : IO (InstructionDiffResult × FuzzerRng) := do
  let nasmStr := X86_64Instruction.toNASM pkg
  if !X86_64Instruction.canFuzzHardware pkg then
    return (InstructionDiffResult.mk true nasmStr 0 0 none true, rng)

  let (allStates, nextRng) := X86_64Instruction.generateFuzzStates pkg rng
  let statesToTest := allStates.take maxStates
  if statesToTest.isEmpty then
    return (InstructionDiffResult.mk true nasmStr 0 0 none false, nextRng)

  let instrBytes := X86_64Instruction.encode pkg
  let testPackets := statesToTest.map (fun s => (s, instrBytes))

  let hwResultsE ← runHardwareBatch testPackets
  let hwResults ←
    match hwResultsE with
    | .ok results => pure results
    | .error msg => throw (IO.userError s!"Hardware harness failure while testing '{nasmStr}': {msg}")

  let mut failed := 0
  let mut firstErr : Option String := none

  for i in [0:statesToTest.length] do
    let initS := statesToTest[i]!
    let hwRes := hwResults.getD i default
    let modelS := X86_64Instruction.step pkg initS

    -- Compare fault state
    if modelS.faulted != hwRes.faulted then
      failed := failed + 1
      if firstErr.isNone then
        firstErr := some s!"Instruction '{nasmStr}' fault status mismatch on test vector {i+1}: Model.faulted={modelS.faulted}, HW.faulted={hwRes.faulted}"
    else if !modelS.faulted then
      -- Compare all 16 GPRs
      let mut regMismatch := false
      let mut regDiffs : List String := []
      for r in allRegs64 do
        let mVal := modelS.gprs r
        let hVal := hwRes.gprs r
        if mVal != hVal then
          regMismatch := true
          regDiffs := regDiffs ++ [s!"{r}: Model={formatHex64 mVal}, HW={formatHex64 hVal}"]

      -- Compare arithmetic condition flags with undefined flags masked
      let undefMask := X86_64Instruction.undefinedFlagsMask pkg
      let compareMask := arithmeticStatusMask &&& (~~~undefMask)
      let mFlags := modelS.flags &&& compareMask
      let hFlags := hwRes.flags &&& compareMask
      let flagsMismatch := mFlags != hFlags

      if regMismatch || flagsMismatch then
        failed := failed + 1
        if firstErr.isNone then
          let diffDesc :=
            (if regMismatch then "Register Discrepancies:\n    " ++ String.intercalate "\n    " regDiffs ++ "\n" else "") ++
            (if flagsMismatch then "Flag Discrepancies (mask=" ++ formatHex64 compareMask ++ "):\n    " ++ formatFlagDiff mFlags hFlags ++ "\n" else "")
          firstErr := some s!"Instruction '{nasmStr}' mismatch on test vector {i+1}:\n  {diffDesc}"

  let passed := failed == 0
  pure (InstructionDiffResult.mk passed nasmStr statesToTest.length failed firstErr false, nextRng)

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Suite of all instruction instances safe to execute on real hardware, derived from
    `Registry.allEncodableInstructions` (every instruction family's `roundtripCases`) filtered by
    `canFuzzHardware` — instead of a hand-maintained literal list. The adversarial review that
    prompted the registry found this exact hand list had already drifted out of sync with what
    the decoder supports; deriving it from the single source of truth closes that drift class
    structurally, the same way the `RoundtripGate` theorems close decode-gap drift. -/
def allSupportedInstructionSuite : List AnyX86_64Instruction :=
  allEncodableInstructions.filter (X86_64Instruction.canFuzzHardware ·)

/- REF: docs/VISION.md#32-the-models-must-be-faithful-to-reality -/
/-- The number of distinct microarchitectures this build's hardware oracle actually executed
against. Currently exactly one: whatever CPU `runHardwareBatch` spawns the native PE runner on
(the sole silicon truth source per docs/VISION.md §3.2 — no cross-microarchitecture disclosure exists yet;
see T11's Linux/multi-silicon follow-on plan). Surfacing this number keeps a green run's
evidentiary scope visible rather than implied
(docs/VISION.md#32-the-models-must-be-faithful-to-reality). -/
def microarchitecturesValidated : Nat := 1

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Runs the comprehensive x86-64 differential semantics fuzzer across all supported instruction
    models. Returns (fuzzed-and-passed count, skipped count, failed count, total vectors).

    Nonzero-vector floor (`docs/REVIEW.md` Law 13, Findings Become Gates): a run
    that exercises zero hardware test vectors — whether because every candidate's
    `canFuzzHardware` is false, an `--instruction` filter matched nothing, or the candidate suite
    itself is empty — is a distinct failure mode from an oracle that silently no-ops, and must
    hard-fail rather than report a clean summary. The floor fires unconditionally, even when the
    zero-vector state is reached through a legitimate precondition — detect-and-fail, not
    detect-and-explain, per the validation contract. This is layered on top of the pre-existing
    `[SKIP]`/`skipped` machinery and `verifyHardwareOracleControls` gate above; neither of those
    catches the case where the *entire* candidate suite nets zero vectors. -/
def runX86SemanticsFuzzerSuite (iterationsPerInstr : Nat := 150) (initialSeed : UInt64 := 88172645463325252) (instrFilter : Option String := none) : IO (Nat × Nat × Nat × Nat) := do
  IO.println "================================================================================"
  IO.println "  Gasm x86-64 Differential Semantic Fuzzer (Hardware vs Pure Lean Model)"
  IO.println "================================================================================"

  -- Mandatory, unskippable oracle world-sanity gate: aborts the entire run before a single
  -- real vector is tested if the hardware harness cannot execute a known-answer positive
  -- control or detect a known-fault negative control.
  verifyHardwareOracleControls
  IO.println "  [CONTROL] Hardware oracle sanity check passed (positive + negative controls)."

  let mut curRng : FuzzerRng := FuzzerRng.mk initialSeed
  let mut totalInstrsPassed := 0
  let mut totalInstrsSkipped := 0
  let mut totalInstrsFailed := 0
  let mut totalVectorsTested := 0

  let candidateSuite := match instrFilter with
    | some filterStr => allSupportedInstructionSuite.filter (fun i => (X86_64Instruction.toNASM i).toLower.contains filterStr.toLower)
    | none => allSupportedInstructionSuite

  for instr in candidateSuite do
    let (res, nextRng) ← verifyInstructionSemantics instr curRng iterationsPerInstr
    curRng := nextRng
    totalVectorsTested := totalVectorsTested + res.totalTested

    if res.skipped then
      totalInstrsSkipped := totalInstrsSkipped + 1
      let padLen := 32 - min 32 res.mnemonic.length
      IO.println s!"  [SKIP] {res.mnemonic.pushn ' ' padLen} (cannot be safely fuzzed on host hardware, not counted as tested)"
    else if res.passed then
      totalInstrsPassed := totalInstrsPassed + 1
      let padLen := 32 - min 32 res.mnemonic.length
      IO.println s!"  [PASS] {res.mnemonic.pushn ' ' padLen} ({res.totalTested} test vectors verified bit-exact)"
    else
      totalInstrsFailed := totalInstrsFailed + 1
      let errStr := res.errorMessage.getD "Unknown failure"
      IO.println s!"  [FAIL] {res.mnemonic}:\n{errStr}"

  IO.println "--------------------------------------------------------------------------------"
  -- TC17 vacuity floor: 0 vectors exercised (all candidates skipped, filter matched nothing, or
  -- an empty suite) is a hard failure, never a clean summary — regardless of totalInstrsFailed.
  if totalVectorsTested == 0 then
    IO.println s!"[VACUITY FLOOR TRIPPED] 0 hardware test vectors were exercised across {candidateSuite.length} candidate instruction instance(s) ({totalInstrsSkipped} skipped, {totalInstrsPassed} fuzzed-and-passed, {totalInstrsFailed} fuzzed-and-failed)."
    IO.println "A fuzzer run that exercises zero vectors has verified nothing — this is a hard FAIL, not a clean PASS (docs/REVIEW.md Law 13)."
    IO.println "================================================================================"
    return (totalInstrsPassed, totalInstrsSkipped, max 1 totalInstrsFailed, totalVectorsTested)
  IO.println s!"Summary: {totalInstrsPassed} fuzzed + {totalInstrsSkipped} skipped, {totalInstrsFailed} failed ({totalVectorsTested} total test vectors)"
  IO.println s!"[Evidentiary Scope] Validated on exactly {microarchitecturesValidated} microarchitecture(s) (host CPU only)."
  IO.println "================================================================================"
  pure (totalInstrsPassed, totalInstrsSkipped, totalInstrsFailed, totalVectorsTested)

end Gasm.Targets.X86_64.SemanticsFuzzer

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

import Gasm.Compiler.Word.StructuredStraightLineAArch64

namespace Gasm.Compiler.Word.StructuredStraightLineAArch64

open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#differential-aarch64-body-replacement -/
/-- A property-relative delta from one compiler-produced body to an exact replacement body.

    The only handwritten semantic burden in this first delta is equality of the selected result
    observation. Frame, fallthrough, clobber, instruction-wrapper, and byte facts are regenerated
    structurally from the replacement's admitted macro instructions. This is local evidence, not
    execution, layout, artifact, export, or `VerifiedProgram` authority. -/
structure FunctionalDelta {source : Structured.WordFunction}
    {selected : WordOnly (source := source.body)} {fits : Fits (compile selected)}
    (baseline : LocalCertificate source selected fits) where
  code : List Instruction
  resultEq : ∀ state,
    (runLocalSteps code state).gprs x0 =
      (runLocalSteps baseline.code state).gprs x0

/- REF: docs/MACRO_ASSEMBLER.md#differential-aarch64-body-replacement -/
/-- The exact local target realization selected after differential replacement. -/
structure BodyRealization (source : Structured.WordFunction) where
  code : List Instruction
  instructions : List AnyAArch64Instruction
  codeBytes : ByteArray
  instructions_eq : instructions = code.map Instruction.emit
  codeBytes_eq : codeBytes = serialize code
  emittedBytes_eq : codeBytes = serializeEmitted instructions
  localResult : ∀ state,
    (runLocalSteps code state).gprs x0 = source.fn (argsOfState state)
  preservesMemory : ∀ state, (runLocalSteps code state).memory = state.memory
  preservesSp : ∀ state, (runLocalSteps code state).sp = state.sp
  preservesNzcv : ∀ state, (runLocalSteps code state).nzcv = state.nzcv
  preservesFault : ∀ state, (runLocalSteps code state).fault = state.fault
  preservesTerminated : ∀ state,
    (runLocalSteps code state).terminated = state.terminated
  pcAdvance : ∀ state,
    (runLocalSteps code state).pc = state.pc + localCodeSize code
  clobberedGprs : List Gpr
  clobberedGprs_eq : clobberedGprs = code.flatMap Instruction.clobberedGprs
  preservesGpr : ∀ state register, register ∉ clobberedGprs →
    (runLocalSteps code state).gprs register = state.gprs register
  controlFlowFree : ∀ instruction ∈ instructions, ControlFlowFree instruction

/- REF: docs/MACRO_ASSEMBLER.md#differential-aarch64-body-replacement -/
/-- Transport the compiler's source-result theorem through a selected functional delta and
    regenerate every target-structural fact for the replacement. -/
def FunctionalDelta.realize {source : Structured.WordFunction}
    {selected : WordOnly (source := source.body)} {fits : Fits (compile selected)}
    {baseline : LocalCertificate source selected fits}
    (delta : FunctionalDelta baseline) : BodyRealization source where
  code := delta.code
  instructions := delta.code.map Instruction.emit
  codeBytes := serialize delta.code
  instructions_eq := rfl
  codeBytes_eq := rfl
  emittedBytes_eq := serialize_eq_serializeEmitted delta.code
  localResult := by
    intro state
    rw [delta.resultEq state]
    exact baseline.localResult state
  preservesMemory := runLocalSteps_preservesMemory delta.code
  preservesSp := runLocalSteps_preservesSp delta.code
  preservesNzcv := runLocalSteps_preservesNzcv delta.code
  preservesFault := runLocalSteps_preservesFault delta.code
  preservesTerminated := runLocalSteps_preservesTerminated delta.code
  pcAdvance := runLocalSteps_pc delta.code
  clobberedGprs := delta.code.flatMap Instruction.clobberedGprs
  clobberedGprs_eq := rfl
  preservesGpr := by
    intro state register preserved
    exact runLocalSteps_preservesGpr delta.code state register preserved
  controlFlowFree := by
    intro instruction member
    simp only [List.mem_map] at member
    obtain ⟨selectedInstruction, _, rfl⟩ := member
    exact selectedInstruction.controlFlowFree

end Gasm.Compiler.Word.StructuredStraightLineAArch64

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

import Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry

namespace Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry

open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#differential-microsoft-x64-body-replacement -/
/-- A property-relative delta from a compiler-produced process-entry body to one exact macro
    segment. Larger replacements use `Segment.then` before constructing the delta.

    This first delta transports only the selected RAX result observation. Memory preservation is
    required explicitly, while fallthrough, fault, clobber, instruction, and byte facts are
    regenerated from the replacement segment. Input-register preservation is intentionally not
    inherited from the baseline. This is local evidence, not execution, placement, artifact,
    export, callable ABI, or `VerifiedProgram` authority. -/
structure FunctionalDelta {source : Structured.WordFunction}
    {selected : WordOnly (source := source.body)} {fits : Fits (compile selected)}
    (baseline : LocalCertificate source selected fits) where
  replacement : Segment
  memoryPreserved : replacement.contract.memory = .preserved
  resultEq : ∀ state,
    (runLocalSteps replacement.code state).gprs resultRegister =
      (runLocalSteps baseline.instructions state).gprs resultRegister

/- REF: docs/MACRO_ASSEMBLER.md#differential-microsoft-x64-body-replacement -/
/-- The exact local target realization selected after differential replacement. -/
structure BodyRealization (source : Structured.WordFunction) where
  segment : Segment
  instructions : List X86_64Instr
  codeBytes : ByteArray
  instructions_eq : instructions = segment.code
  codeBytes_eq : codeBytes =
    Gasm.Targets.X86_64.Assembler.serializeInstructions instructions
  localResult : ∀ state,
    (runLocalSteps instructions state).gprs resultRegister = source.fn (argsOfState state)
  preservesMemory : ∀ state,
    (runLocalSteps instructions state).memory = state.memory
  preservesFault : ∀ state,
    (runLocalSteps instructions state).fault = state.fault
  ripAdvance : ∀ state,
    (runLocalSteps instructions state).rip = state.rip + instructionSpan instructions
  clobberedGprs : List Reg64
  clobberedGprs_eq : clobberedGprs = segment.contract.clobberedGprs
  preservesGpr : ∀ state register, register ∉ clobberedGprs →
    (runLocalSteps instructions state).gprs register = state.gprs register
  controlFlowFree : ∀ instruction ∈ instructions, ControlFlowFree instruction

/- REF: docs/MACRO_ASSEMBLER.md#differential-microsoft-x64-body-replacement -/
/-- Transport the compiler's source-result theorem through a selected functional delta and
    regenerate every target-structural fact admitted by the replacement segment. -/
def FunctionalDelta.realize {source : Structured.WordFunction}
    {selected : WordOnly (source := source.body)} {fits : Fits (compile selected)}
    {baseline : LocalCertificate source selected fits}
    (delta : FunctionalDelta baseline) : BodyRealization source where
  segment := delta.replacement
  instructions := delta.replacement.code
  codeBytes := Gasm.Targets.X86_64.Assembler.serializeInstructions delta.replacement.code
  instructions_eq := rfl
  codeBytes_eq := rfl
  localResult := by
    intro state
    rw [delta.resultEq state]
    exact baseline.localResult state
  preservesMemory := delta.replacement.preservesMemory delta.memoryPreserved
  preservesFault := runLocalSteps_fault_eq _ delta.replacement.controlFlowFree
  ripAdvance := runLocalSteps_rip_eq _ delta.replacement.controlFlowFree
  clobberedGprs := delta.replacement.contract.clobberedGprs
  clobberedGprs_eq := rfl
  preservesGpr := delta.replacement.preservesGpr
  controlFlowFree := delta.replacement.controlFlowFree

end Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry

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

import Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFG

namespace Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFG.Controls

open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

private def source : Structured.Expr InputContext .word := .wordLit 42

private def selected : WordOnly (source := source) := .wordLit 42

private theorem fits : Fits (compile selected) := by
  change 0 ≤ 7
  omega

private def generatedCertificate : LocalCertificate (leafFunction source) selected fits :=
  lowerFunction (leafFunction source) selected fits

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
def generated : Body source := Body.ofGenerated generatedCertificate

private def replacementSegment : Segment := loadImm resultRegister 42

private def replacementDelta : FunctionalDelta generatedCertificate where
  replacement := replacementSegment
  memoryPreserved := rfl
  resultEq := by
    intro state
    calc
      (runLocalSteps replacementSegment.code state).gprs resultRegister = 42 :=
        replacementSegment.localSound state trivial
      _ = (runLocalSteps generatedCertificate.instructions state).gprs resultRegister := by
        rw [generatedCertificate.localResult]
        rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
def handwritten : Body source := Body.ofReplacement replacementDelta.realize

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
theorem handwritten_isOneInstruction : handwritten.instructions.length = 1 := rfl

end Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFG.Controls

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

import Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry

namespace Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry.Controls

open Gasm.Compiler.Word.Structured
open Gasm.Targets.X86_64

private def a0 : Structured.Expr InputContext .word := .var InputContext.a0
private def a1 : Structured.Expr InputContext .word := .var InputContext.a1

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
example : (select (.eq a0 a1)).isSome = true := by
  simp [select, a0, a1]

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
example : (select (.ult a0 a1)).isSome = true := by
  simp [select, a0, a1]

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
example : (lower (.notEq InputContext.a0 InputContext.a1)).kind = .notEqual := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
example : (lower (.notUlt InputContext.a0 InputContext.a1)).kind = .aboveOrEqual := rfl

private def literalComparison : Structured.Expr InputContext .bool :=
  .eq (.wordLit 0) a0

private def arithmeticComparison : Structured.Expr InputContext .bool :=
  .ult (.add a0 a1) a1

private def nestedNegation : Structured.Expr InputContext .bool :=
  .not (.not (.eq a0 a1))

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
theorem unsupportedConditionsRejected :
    (select literalComparison).isNone = true ∧
    (select arithmeticComparison).isNone = true ∧
    (select nestedNegation).isNone = true := by
  simp [literalComparison, arithmeticComparison, nestedNegation, select, a0, a1]

end Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry.Controls

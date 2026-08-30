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

import Gasm.Compiler.Word.StructuredStraightLine

namespace Gasm.Compiler.Word.StructuredStraightLine.Controls

open Gasm.Compiler.Word.Structured

private def a0 : Structured.Expr InputContext .word := .var InputContext.a0
private def a1 : Structured.Expr InputContext .word := .var InputContext.a1
private def a2 : Structured.Expr InputContext .word := .var InputContext.a2
private def a3 : Structured.Expr InputContext .word := .var InputContext.a3

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
def nestedLets : Structured.Expr InputContext .word :=
  .letE (.add a0 a1)
    (.letE (.bitAnd (.var .zero) (.wordLit 255))
      (.sub (.var .zero) (.var (.succ (.succ InputContext.a3)))))

private def nestedLetsSelected : WordOnly (source := nestedLets) :=
  .letE (.add (.var _) (.var _))
    (.letE (.bitAnd (.var _) (.wordLit _)) (.sub (.var _) (.var _)))

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
theorem nestedLets_emitThreeInstructions :
    (compile nestedLetsSelected).instructionCount = 3 := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
theorem nestedLets_correct (args : Args) :
    (compile nestedLetsSelected).runClosed args = nestedLets.eval (InputContext.env args) :=
  compile_correct nestedLetsSelected args

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
example : (select nestedLets).isSome = true := by
  simp [nestedLets, select, a0, a1]

private def branch : Structured.Expr InputContext .word :=
  .ite (.ult a0 a1) a2 a3

private def boolBinding : Structured.Expr InputContext .word :=
  .letE (.ult a0 a1) (.var (.succ InputContext.a2))

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
theorem unsupportedControlRejected :
    (select branch).isNone = true ∧ (select boolBinding).isNone = true := by
  simp [branch, boolBinding, select]

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
theorem subtractionOrderRetained :
    (compile (.sub (.var InputContext.a0) (.var InputContext.a1))).runClosed
        { a0 := 3, a1 := 5, a2 := 0, a3 := 0 } = 18446744073709551614 := by
  rfl

end Gasm.Compiler.Word.StructuredStraightLine.Controls

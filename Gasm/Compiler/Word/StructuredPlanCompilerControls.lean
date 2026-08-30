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

import Gasm.Compiler.Word.StructuredPlanCompiler

namespace Gasm.Compiler.Word.StructuredPlanCompiler.Controls

open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG

private def a0 : Structured.Expr InputContext .word := .var InputContext.a0
private def a1 : Structured.Expr InputContext .word := .var InputContext.a1
private def a2 : Structured.Expr InputContext .word := .var InputContext.a2
private def a3 : Structured.Expr InputContext .word := .var InputContext.a3

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
def nestedTree : Structured.Expr InputContext .word :=
  .ite (.ult a0 a1)
    (.add a0 a2)
    (.ite (.eq a2 a3) (.sub a3 a0) (.bitAnd a1 a2))

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
example : (recognize nestedTree).isSome = true := by
  simp [nestedTree, recognize, branchFree?, a0, a1, a2, a3]

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
theorem generated_roles_unique {source : Structured.Expr InputContext .word}
    (tree : DecisionTree source) : (compile tree).roles.Nodup :=
  (compile tree).plan.uniqueRoles

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
theorem generated_root_selected {source : Structured.Expr InputContext .word}
    (tree : DecisionTree source) : (compile tree).root ∈ (compile tree).roles :=
  (compile tree).plan.root_mem

private def hiddenBranchUnderLet : Structured.Expr InputContext .word :=
  .letE (.ite (.ult a0 a1) a2 a3) (.var .zero)

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
example : (recognize hiddenBranchUnderLet).isNone = true := by
  simp [hiddenBranchUnderLet, recognize, branchFree?, a0, a1, a2, a3]

private def branchInsideCondition : Structured.Expr InputContext .word :=
  .ite (.ite (.eq a0 a1) (.boolLit true) (.boolLit false)) a2 a3

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
example : (recognize branchInsideCondition).isNone = true := by
  simp [branchInsideCondition, recognize, branchFree?, a0, a1, a2, a3]

end Gasm.Compiler.Word.StructuredPlanCompiler.Controls

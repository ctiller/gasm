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

import Gasm.Compiler.Word.StructuredMicrosoftX64CFG
import Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFGControls

namespace Gasm.Compiler.Word.StructuredMicrosoftX64CFG.Controls

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG
open Gasm.Compiler.Word.StructuredMicrosoftX64CFG
open Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry
open Gasm.Targets.X86_64

private abbrev Scope := Fin 3
private def falseRole : NodeId Scope := ⟨0⟩
private def trueRole : NodeId Scope := ⟨1⟩
private def branchRole : NodeId Scope := ⟨2⟩

private def leafSource : Structured.Expr InputContext .word := .wordLit 42
private def condition : Structured.Expr InputContext .bool :=
  .eq (.var InputContext.a0) (.var InputContext.a1)
private def source : Structured.Expr InputContext .word :=
  .ite condition leafSource leafSource

private def falsePlan : Plan Scope leafSource [falseRole] falseRole :=
  .leaf falseRole .wordLit

private def truePlan : Plan Scope leafSource [trueRole] trueRole :=
  .leaf trueRole .wordLit

private theorem roleDisjoint :
    ∀ falseNode ∈ [falseRole], ∀ trueNode ∈ [trueRole], falseNode ≠ trueNode := by
  simp [falseRole, trueRole]

private theorem roleFresh : branchRole ∉ [falseRole] ++ [trueRole] := by
  simp [branchRole, falseRole, trueRole]

private def plan : Plan Scope source
    ([falseRole] ++ [trueRole] ++ [branchRole]) branchRole :=
  .branch branchRole (.eq .var .var) truePlan falsePlan roleDisjoint roleFresh

private def entry (role : NodeId Scope) : BlockEntry X86_64 (NodeId Scope) where
  State := PUnit
  id := role
  expectedDepth := 0
  accepts := fun state => state.stackDepth = 0 ∧ state.obligations = []

private def terminal (body : StructuredLeafMicrosoftX64CFG.Body leafSource)
    (role : NodeId Scope) : StructuredLeafMicrosoftX64CFG.Terminal body (entry role) where
  terminator := fun state accepted => .halt (by
    intro obligation member
    change obligation ∈ state.obligations at member
    rw [accepted.2] at member
    simp at member)
  targetFree := by simp [StructuredCFG.TargetFree]

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
def trueSelected : Selected truePlan :=
  .leaf StructuredLeafMicrosoftX64CFG.Controls.generated (entry trueRole) rfl
    (terminal StructuredLeafMicrosoftX64CFG.Controls.generated trueRole)

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
def falseSelected : Selected falsePlan :=
  .leaf StructuredLeafMicrosoftX64CFG.Controls.handwritten (entry falseRole) rfl
    (terminal StructuredLeafMicrosoftX64CFG.Controls.handwritten falseRole)

private def lowered : LoweredCondition condition := lower (.eq InputContext.a0 InputContext.a1)

private def edgeTo (role : NodeId Scope)
    (state : ComposedState X86_64 PUnit)
    (accepted : (entry branchRole).accepts state) (enabled : Prop) :
    ConditionalBlockEdge (BlockId := NodeId Scope)
      (StructuredConditionMicrosoftX64CFG.afterCondition lowered state) enabled where
  target := entry role
  targetState := StructuredConditionMicrosoftX64CFG.afterCondition lowered state
  framePreserved := JumpFramePreserved.refl _
  depthEstablished := by
    simpa [entry, StructuredConditionMicrosoftX64CFG.afterCondition_stackDepth] using accepted.1.symm
  entryEstablished := by
    intro _
    constructor
    · simpa [entry, StructuredConditionMicrosoftX64CFG.afterCondition_stackDepth] using accepted.1
    · simpa [entry, StructuredConditionMicrosoftX64CFG.afterCondition_obligations] using accepted.2

private def successors : StructuredConditionMicrosoftX64CFG.Successors lowered
    (entry branchRole) trueSelected.rootBlock falseSelected.rootBlock where
  trueEdge := fun state accepted => edgeTo trueRole state accepted _
  trueExact := by intro state accepted; rfl
  falseEdge := fun state accepted => edgeTo falseRole state accepted _
  falseExact := by intro state accepted; rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
/-- A concrete three-block plan mixes a generated true leaf with a one-instruction handwritten
    false leaf, while the stable source plan and branch polarity remain unchanged. -/
def selected : Selected plan :=
  .branch trueSelected falseSelected lowered (entry branchRole) rfl successors

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem selected_block_ids :
    (selected.blocks.map fun block => block.entry.id) =
      [falseRole] ++ [trueRole] ++ [branchRole] :=
  selected.idsExact

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem selected_ids_unique :
    (selected.blocks.map fun block => block.entry.id).Nodup :=
  selected.assignment.ids_nodup

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem selected_graph_exact :
    selected.lower.graph.blocks = selected.blocks.map DirectBlock.toBasicBlock :=
  selected.lower_graph_blocks

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly
   Swapping the true and false implementations does not typecheck: their exact symbolic plan
   indices, nominal roots, and condition-successor orientation differ. -/
/-- error: Application type mismatch: The argument
  falseSelected
has type
  Selected falsePlan
but is expected to have type
  Selected truePlan
in the application
  falseSelected.branch -/
#guard_msgs(error) in
example : Selected plan :=
  .branch falseSelected trueSelected lowered (entry branchRole) rfl successors

private def foreignRole : NodeId (Fin 4) := ⟨0⟩
private def foreignPlan : Plan (Fin 4) leafSource [foreignRole] foreignRole :=
  .leaf foreignRole .wordLit

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly
   A foreign nominal scope cannot be inserted into this plan assignment. -/
/-- error: Type mismatch
  foreign
has type
  Selected foreignPlan
but is expected to have type
  Selected truePlan -/
#guard_msgs(error) in
example (foreign : Selected foreignPlan) : Selected truePlan := foreign

end Gasm.Compiler.Word.StructuredMicrosoftX64CFG.Controls

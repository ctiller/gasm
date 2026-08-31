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

import Gasm.Compiler.Word.StructuredConditionMicrosoftX64CFG
import Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFG
import Gasm.Compiler.Word.StructuredPlanCompiler

namespace Gasm.Compiler.Word.StructuredMicrosoftX64CFG

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG
open Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry
open Gasm.Targets.X86_64

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
/-- One exact Microsoft x64 implementation of a stable symbolic decision plan. Symbolic node IDs
    are also the nominal block IDs, so implementation uniqueness is derived from the plan rather
    than requested again from callers. Generated and handwritten leaf bodies inhabit the same
    package through `StructuredLeafMicrosoftX64CFG.Body`.

    This structure contains only the existing typed assignment and realization evidence. It does
    not assert instruction layout, native execution, artifact identity, ABI publication, or whole
    program correctness. -/
structure Selected {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    (plan : Plan Scope source roles root) where
  blocks : List (DirectBlock X86_64 (NodeId Scope))
  rootBlock : DirectBlock X86_64 (NodeId Scope)
  assignment : Assignment X86_64 (NodeId Scope) plan blocks rootBlock
  realizes : Realizes plan assignment
  idsExact : (blocks.map fun block => block.entry.id) = roles
  rootIdExact : rootBlock.entry.id = root

namespace Selected

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
/-- Select one exact generated or handwritten target-free implementation for a symbolic leaf. -/
def leaf {Scope : Type} {role : NodeId Scope}
    {source : Structured.Expr InputContext .word} {sourceNoIte : NoIte source}
    (body : StructuredLeafMicrosoftX64CFG.Body source)
    (entry : BlockEntry X86_64 (NodeId Scope)) (entryId : entry.id = role)
    (terminal : StructuredLeafMicrosoftX64CFG.Terminal body entry) :
    Selected (.leaf role sourceNoIte) := by
  let block := StructuredLeafMicrosoftX64CFG.block body entry terminal
  exact {
    blocks := [block]
    rootBlock := block
    assignment := .leaf block
    realizes := .leaf (StructuredLeafMicrosoftX64CFG.realizes body entry terminal)
    idsExact := by simp [block, entryId]
    rootIdExact := by simpa [block] using entryId
  }

private theorem childIdsDisjoint {Scope : Type}
    {falseRoles trueRoles : List (NodeId Scope)}
    {falseSource trueSource : Structured.Expr InputContext .word}
    {falseRoot trueRoot : NodeId Scope}
    {falsePlan : Plan Scope falseSource falseRoles falseRoot}
    {truePlan : Plan Scope trueSource trueRoles trueRoot}
    (falseSelected : Selected falsePlan) (trueSelected : Selected truePlan)
    (rolesDisjoint : ∀ falseRole ∈ falseRoles, ∀ trueRole ∈ trueRoles,
      falseRole ≠ trueRole) :
    ∀ falseBlock ∈ falseSelected.blocks, ∀ trueBlock ∈ trueSelected.blocks,
      falseBlock.entry.id ≠ trueBlock.entry.id := by
  intro falseBlock falseMember trueBlock trueMember
  apply rolesDisjoint falseBlock.entry.id
  · rw [← falseSelected.idsExact]
    exact List.mem_map.mpr ⟨falseBlock, falseMember, rfl⟩
  · rw [← trueSelected.idsExact]
    exact List.mem_map.mpr ⟨trueBlock, trueMember, rfl⟩

private theorem parentIdFresh {Scope : Type}
    {ifTrue ifFalse : Structured.Expr InputContext .word}
    {trueRoles falseRoles : List (NodeId Scope)}
    {trueRoot falseRoot role : NodeId Scope}
    {truePlan : Plan Scope ifTrue trueRoles trueRoot}
    {falsePlan : Plan Scope ifFalse falseRoles falseRoot}
    (trueSelected : Selected truePlan) (falseSelected : Selected falsePlan)
    (entry : BlockEntry X86_64 (NodeId Scope)) (entryId : entry.id = role)
    (roleFresh : role ∉ falseRoles ++ trueRoles)
    (block : DirectBlock X86_64 (NodeId Scope)) (blockEntry : block.entry = entry) :
    block.entry.id ∉
      (falseSelected.blocks ++ trueSelected.blocks).map (fun child => child.entry.id) := by
  intro member
  apply roleFresh
  have member' : block.entry.id ∈ falseRoles ++ trueRoles := by
    rw [← falseSelected.idsExact, ← trueSelected.idsExact, ← List.map_append]
    exact member
  rw [blockEntry, entryId] at member'
  exact member'

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
/-- Select one exact comparison block above two already selected subplans. The plan's nominal role
    separation derives block-ID disjointness and parent freshness. Both target contracts remain
    caller/target-owned in `successors`; this constructor creates no edge evidence. -/
def branch {Scope : Type} {role : NodeId Scope}
    {condition : Structured.Expr InputContext .bool} {conditionNoIte : NoIte condition}
    {ifTrue ifFalse : Structured.Expr InputContext .word}
    {trueRoles falseRoles : List (NodeId Scope)}
    {trueRoot falseRoot : NodeId Scope}
    {truePlan : Plan Scope ifTrue trueRoles trueRoot}
    {falsePlan : Plan Scope ifFalse falseRoles falseRoot}
    {roleDisjoint : ∀ falseRole ∈ falseRoles, ∀ trueRole ∈ trueRoles,
      falseRole ≠ trueRole}
    {roleFresh : role ∉ falseRoles ++ trueRoles}
    (trueSelected : Selected truePlan) (falseSelected : Selected falsePlan)
    (lowered : LoweredCondition condition)
    (entry : BlockEntry X86_64 (NodeId Scope)) (entryId : entry.id = role)
    (successors : StructuredConditionMicrosoftX64CFG.Successors lowered entry
      trueSelected.rootBlock falseSelected.rootBlock) :
    Selected (.branch role conditionNoIte truePlan falsePlan roleDisjoint roleFresh) := by
  let block := StructuredConditionMicrosoftX64CFG.block lowered entry
    trueSelected.rootBlock falseSelected.rootBlock successors
  have disjointIds := childIdsDisjoint falseSelected trueSelected roleDisjoint
  have freshId := parentIdFresh trueSelected falseSelected entry entryId roleFresh block (by rfl)
  let assignment : Assignment X86_64 (NodeId Scope)
      (.branch role conditionNoIte truePlan falsePlan roleDisjoint roleFresh)
      (falseSelected.blocks ++ trueSelected.blocks ++ [block]) block :=
    .branch trueSelected.assignment falseSelected.assignment block disjointIds freshId
  let realizes : Realizes
      (.branch role conditionNoIte truePlan falsePlan roleDisjoint roleFresh) assignment :=
    .branch trueSelected.realizes falseSelected.realizes
      (StructuredConditionMicrosoftX64CFG.realizes lowered entry
        trueSelected.rootBlock falseSelected.rootBlock successors)
  exact {
    blocks := falseSelected.blocks ++ trueSelected.blocks ++ [block]
    rootBlock := block
    assignment
    realizes
    idsExact := by
      simp only [List.map_append, List.map_singleton]
      rw [falseSelected.idsExact, trueSelected.idsExact]
      simp [block, entryId]
    rootIdExact := by simpa [block] using entryId
  }

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
/-- Finalize a selected implementation only through the existing acyclic CFG lowering. -/
noncomputable def lower {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    {plan : Plan Scope source roles root} (selected : Selected plan) :
    Realizes.Lowered selected.blocks selected.rootBlock :=
  selected.realizes.lower

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
/-- Consume the plan produced by the automatic structured frontend without changing its private
    nominal role scope. The selected implementation remains an explicit, replaceable argument. -/
noncomputable def lowerCompiled {source : Structured.Expr InputContext .word}
    (compiled : StructuredPlanCompiler.Compiled source)
    (selected : Selected compiled.plan) :
    Realizes.Lowered selected.blocks selected.rootBlock :=
  selected.lower

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem lower_graph_blocks {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    {plan : Plan Scope source roles root} (selected : Selected plan) :
    selected.lower.graph.blocks = selected.blocks.map DirectBlock.toBasicBlock :=
  selected.realizes.lower_graph_blocks

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem lower_graph_entry {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    {plan : Plan Scope source roles root} (selected : Selected plan) :
    selected.lower.graph.entry = selected.rootBlock.entry :=
  selected.realizes.lower_graph_entry

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem lower_graph_entry_id {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    {plan : Plan Scope source roles root} (selected : Selected plan) :
    selected.lower.graph.entry.id = root := by
  rw [selected.lower_graph_entry]
  exact selected.rootIdExact

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-plan-assembly -/
theorem lowerCompiled_graph_entry_id {source : Structured.Expr InputContext .word}
    (compiled : StructuredPlanCompiler.Compiled source)
    (selected : Selected compiled.plan) :
    (lowerCompiled compiled selected).graph.entry.id = compiled.root :=
  selected.lower_graph_entry_id

end Selected

end Gasm.Compiler.Word.StructuredMicrosoftX64CFG

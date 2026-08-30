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

import Gasm.Compiler.Word.Structured
import Gasm.Core.CFGBuilder

namespace Gasm.Compiler.Word.StructuredCFG

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Compiler.Word.Structured

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Structural evidence that an expression contains no selected conditional. A `letE` is admitted
    only when both its value and body are branch-free, so an `ite` cannot hide under a binding. -/
inductive NoIte : {context : List ValueSort} → {kind : ValueSort} →
    Structured.Expr context kind → Prop where
  | var : NoIte (.var ref)
  | wordLit : NoIte (.wordLit value)
  | boolLit : NoIte (.boolLit value)
  | add : NoIte lhs → NoIte rhs → NoIte (.add lhs rhs)
  | sub : NoIte lhs → NoIte rhs → NoIte (.sub lhs rhs)
  | bitAnd : NoIte lhs → NoIte rhs → NoIte (.bitAnd lhs rhs)
  | eq : NoIte lhs → NoIte rhs → NoIte (.eq lhs rhs)
  | ult : NoIte lhs → NoIte rhs → NoIte (.ult lhs rhs)
  | not : NoIte value → NoIte (.not value)
  | letE : NoIte value → NoIte body → NoIte (.letE value body)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem noIte_not_ite (condition : Structured.Expr context .bool)
    (ifTrue ifFalse : Structured.Expr context kind) :
    ¬NoIte (.ite condition ifTrue ifFalse) := by
  intro impossible
  cases impossible

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Stable nominal identity for one symbolic decision-tree role. Human-readable names are not proof
    identity; independent components obtain collision-free scopes by choosing distinct scope types. -/
structure NodeId (Scope : Type) where
  value : Scope
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- A source-indexed symbolic decision tree. It contains source expressions, nominal roles, and
    true/false topology only—never an instruction, block body, or target address. -/
inductive Plan (Scope : Type) : Structured.Expr InputContext .word →
    List (NodeId Scope) → NodeId Scope → Type where
  | leaf (role : NodeId Scope) {source : Structured.Expr InputContext .word}
      (sourceNoIte : NoIte source) : Plan Scope source [role] role
  | branch (role : NodeId Scope) {condition : Structured.Expr InputContext .bool}
      (conditionNoIte : NoIte condition)
      {ifTrue ifFalse : Structured.Expr InputContext .word}
      {trueRoles falseRoles : List (NodeId Scope)} {trueRoot falseRoot : NodeId Scope}
      (truePlan : Plan Scope ifTrue trueRoles trueRoot)
      (falsePlan : Plan Scope ifFalse falseRoles falseRoot)
      (disjoint : ∀ falseRole ∈ falseRoles, ∀ trueRole ∈ trueRoles,
        falseRole ≠ trueRole)
      (fresh : role ∉ falseRoles ++ trueRoles) :
      Plan Scope (.ite condition ifTrue ifFalse)
        (falseRoles ++ trueRoles ++ [role]) role

namespace Plan

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Symbolic postorder roles are unique independently of any selected implementation. -/
theorem uniqueRoles {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    (plan : Plan Scope source roles root) : roles.Nodup := by
  induction plan with
  | leaf => simp
  | @branch role condition conditionNoIte ifTrue ifFalse trueRoles falseRoles
      trueRoot falseRoot truePlan falsePlan disjoint fresh trueIH falseIH =>
      rw [List.nodup_append]
      refine ⟨?_, by simp, ?_⟩
      · rw [List.nodup_append]
        exact ⟨falseIH, trueIH, disjoint⟩
      · intro node member same sameMember equal
        simp only [List.mem_singleton] at sameMember
        subst same
        subst node
        exact fresh member

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- The stable root role is last in symbolic postorder. -/
theorem root_mem {Scope : Type} {source : Structured.Expr InputContext .word}
    {roles : List (NodeId Scope)} {root : NodeId Scope}
    (plan : Plan Scope source roles root) : root ∈ roles := by
  cases plan <;> simp

end Plan

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Replaceable implementations aligned exactly with the finite selected plan. The indices retain
    the exact postorder block table and root definition. Roles outside the plan have no assignment,
    block ID, or proof obligation. -/
inductive Assignment (Arch BlockId : Type) [TargetArch Arch] {Scope : Type} :
    {source : Structured.Expr InputContext .word} →
    {roles : List (NodeId Scope)} → {root : NodeId Scope} →
    (plan : Plan Scope source roles root) →
    List (DirectBlock Arch BlockId) → DirectBlock Arch BlockId → Type 1 where
  | leaf {role : NodeId Scope} {source : Structured.Expr InputContext .word}
      {sourceNoIte : NoIte source} (block : DirectBlock Arch BlockId) :
      Assignment Arch BlockId (.leaf role sourceNoIte) [block] block
  | branch {role : NodeId Scope} {condition : Structured.Expr InputContext .bool}
      {conditionNoIte : NoIte condition}
      {ifTrue ifFalse : Structured.Expr InputContext .word}
      {trueRoles falseRoles : List (NodeId Scope)}
      {trueRoot falseRoot : NodeId Scope}
      {truePlan : Plan Scope ifTrue trueRoles trueRoot}
      {falsePlan : Plan Scope ifFalse falseRoles falseRoot}
      {roleDisjoint : ∀ falseRole ∈ falseRoles, ∀ trueRole ∈ trueRoles,
        falseRole ≠ trueRole}
      {roleFresh : role ∉ falseRoles ++ trueRoles}
      {trueBlocks falseBlocks : List (DirectBlock Arch BlockId)}
      {trueRootBlock falseRootBlock : DirectBlock Arch BlockId}
      (trueAssignment : Assignment Arch BlockId truePlan trueBlocks trueRootBlock)
      (falseAssignment : Assignment Arch BlockId falsePlan falseBlocks falseRootBlock)
      (block : DirectBlock Arch BlockId)
      (disjointIds : ∀ falseBlock ∈ falseBlocks, ∀ trueBlock ∈ trueBlocks,
        falseBlock.entry.id ≠ trueBlock.entry.id)
      (freshId : block.entry.id ∉
        (falseBlocks ++ trueBlocks).map (fun child => child.entry.id)) :
      Assignment Arch BlockId
        (.branch role conditionNoIte truePlan falsePlan roleDisjoint roleFresh)
        (falseBlocks ++ trueBlocks ++ [block]) block

namespace Assignment

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Only selected implementation IDs are required to be unique. -/
theorem ids_nodup {Arch BlockId Scope : Type} [TargetArch Arch]
    {source roles root} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    (assignment : Assignment Arch BlockId plan blocks rootBlock) :
    (blocks.map fun block => block.entry.id).Nodup := by
  induction assignment with
  | leaf => simp
  | @branch role condition conditionNoIte ifTrue ifFalse trueRoles falseRoles
      trueRoot falseRoot truePlan falsePlan roleDisjoint roleFresh
      trueBlocks falseBlocks trueRootBlock falseRootBlock trueAssignment falseAssignment
      block disjointIds freshId trueIH falseIH =>
      rw [List.map_append, List.map_append, List.nodup_append]
      refine ⟨?_, by simp, ?_⟩
      · rw [List.nodup_append]
        refine ⟨falseIH, trueIH, ?_⟩
        intro falseId falseMember trueId trueMember
        rcases List.mem_map.mp falseMember with ⟨falseBlock, falseBlockMember, rfl⟩
        rcases List.mem_map.mp trueMember with ⟨trueBlock, trueBlockMember, rfl⟩
        exact disjointIds falseBlock falseBlockMember trueBlock trueBlockMember
      · intro id member same sameMember equal
        simp only [List.map_singleton, List.mem_singleton] at sameMember
        subst same
        subst id
        exact freshId (by simpa [List.map_append] using member)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- The assigned root definition occurs last in its exact postorder table. -/
theorem root_mem {Arch BlockId Scope : Type} [TargetArch Arch]
    {source roles root} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    (assignment : Assignment Arch BlockId plan blocks rootBlock) : rootBlock ∈ blocks := by
  cases assignment <;> simp

end Assignment

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Exhaustive target-free classification for selected leaves. Direct and conditional jumps are
    rejected. CALL and indirect forms have no `DirectTerminator` constructor and cannot hide here. -/
def TargetFree {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} : DirectTerminator (BlockId := BlockId) exit → Prop
  | .ret .. | .sysExit .. | .halt .. => True
  | .jmp .. | .jcc .. => False

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem targetFree_targetsInterned {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} {terminator : DirectTerminator (BlockId := BlockId) exit}
    (targetFree : TargetFree terminator) (blocks : List (BasicBlock Arch BlockId)) :
    terminator.TargetsInterned blocks := by
  cases terminator <;>
    simp_all [TargetFree, Gasm.Core.CFGBuilder.DirectTerminator.TargetsInterned]

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Exact true/false implementation definitions carried by an actual JCC terminator. -/
def TargetsExact {Arch BlockId : Type} [TargetArch Arch]
    (targetTrue targetFalse : DirectBlock Arch BlockId) {S : Type}
    {exit : ComposedState Arch S} : DirectTerminator (BlockId := BlockId) exit → Prop
  | .jcc _ trueRef _ _ falseRef _ _ =>
      trueRef.definition = targetTrue.toBasicBlock ∧
        falseRef.definition = targetFalse.toBasicBlock
  | _ => False

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Target-owned agreement between the condition on the actual JCC and portable Bool evaluation.
    The relation does not derive flags or instruction semantics. -/
def ConditionAgrees {Arch BlockId : Type} [TargetArch Arch]
    (source : Structured.Expr InputContext .bool) (args : Args) {S : Type}
    (exit : ComposedState Arch S) : DirectTerminator (BlockId := BlockId) exit → Prop
  | .jcc condition _ _ _ _ _ _ =>
      (condition.holds exit.machine ↔ source.eval (InputContext.env args) = true)
  | _ => False

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Pointwise logical premise for a selected leaf assignment. `Evidence` may be a target-local
    certificate; the generic adapter consumes only the evidence and the laws stated here. -/
structure RealizesLeaf {Arch BlockId Evidence : Type} [TargetArch Arch]
    (block : DirectBlock Arch BlockId) (source : Structured.Expr InputContext .word) where
  evidence : Evidence
  entryRelation : Args → ComposedState Arch block.entry.State → Prop
  exitRelation : UInt64 → (ExitState : Type) → ComposedState Arch ExitState → Prop
  realizes : ∀ (args : Args)
    (state : ComposedState Arch block.entry.State)
    (accepted : block.entry.accepts state),
    entryRelation args state →
      let result := block.body state accepted
      exitRelation (source.eval (InputContext.env args)) result.1 result.2.1
  targetFree : ∀ (state : ComposedState Arch block.entry.State)
    (accepted : block.entry.accepts state),
    let result := block.body state accepted
    TargetFree result.2.2

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Pointwise logical and exact-definition premises for a selected branch assignment. Both static
    successors are exact; condition applicability remains tied to the runtime-selected proposition. -/
structure RealizesCondition {Arch BlockId Evidence : Type} [TargetArch Arch]
    (block : DirectBlock Arch BlockId) (source : Structured.Expr InputContext .bool)
    (targetTrue targetFalse : DirectBlock Arch BlockId) where
  evidence : Evidence
  entryRelation : Args → ComposedState Arch block.entry.State → Prop
  targetsExact : ∀ (state : ComposedState Arch block.entry.State)
    (accepted : block.entry.accepts state),
    let result := block.body state accepted
    TargetsExact targetTrue targetFalse result.2.2
  conditionAgrees : ∀ (args : Args)
    (state : ComposedState Arch block.entry.State)
    (accepted : block.entry.accepts state),
    entryRelation args state →
      let result := block.body state accepted
      ConditionAgrees source args result.2.1 result.2.2

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Pointwise realization of one stable symbolic plan by one replaceable exact assignment. -/
inductive Realizes {Arch BlockId Scope : Type} [TargetArch Arch] :
    {source : Structured.Expr InputContext .word} →
    {roles : List (NodeId Scope)} → {root : NodeId Scope} →
    (plan : Plan Scope source roles root) →
    {blocks : List (DirectBlock Arch BlockId)} →
    {rootBlock : DirectBlock Arch BlockId} →
    Assignment Arch BlockId plan blocks rootBlock → Type 1 where
  | leaf {role : NodeId Scope} {source : Structured.Expr InputContext .word}
      {sourceNoIte : NoIte source} {block : DirectBlock Arch BlockId} {Evidence : Type}
      (realization : RealizesLeaf (Evidence := Evidence) block source) :
      Realizes (.leaf role sourceNoIte) (.leaf block)
  | branch {role : NodeId Scope}
      {condition : Structured.Expr InputContext .bool}
      {conditionNoIte : NoIte condition}
      {ifTrue ifFalse : Structured.Expr InputContext .word}
      {trueRoles falseRoles : List (NodeId Scope)}
      {trueRoot falseRoot : NodeId Scope}
      {truePlan : Plan Scope ifTrue trueRoles trueRoot}
      {falsePlan : Plan Scope ifFalse falseRoles falseRoot}
      {disjoint : ∀ falseRole ∈ falseRoles, ∀ trueRole ∈ trueRoles,
        falseRole ≠ trueRole}
      {fresh : role ∉ falseRoles ++ trueRoles}
      {trueBlocks falseBlocks : List (DirectBlock Arch BlockId)}
      {trueRootBlock falseRootBlock block : DirectBlock Arch BlockId}
      {trueAssignment : Assignment Arch BlockId truePlan trueBlocks trueRootBlock}
      {falseAssignment : Assignment Arch BlockId falsePlan falseBlocks falseRootBlock}
      {disjointIds : ∀ falseBlock ∈ falseBlocks, ∀ trueBlock ∈ trueBlocks,
        falseBlock.entry.id ≠ trueBlock.entry.id}
      {freshId : block.entry.id ∉
        (falseBlocks ++ trueBlocks).map (fun child => child.entry.id)}
      (trueRealizes : Realizes truePlan trueAssignment)
      (falseRealizes : Realizes falsePlan falseAssignment)
      {Evidence : Type}
      (realization : RealizesCondition (Evidence := Evidence)
        block condition trueRootBlock falseRootBlock) :
      Realizes (.branch role conditionNoIte truePlan falsePlan disjoint fresh)
        (.branch trueAssignment falseAssignment block disjointIds freshId)

namespace Realizes

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Result of combining a stable plan with one exact implementation assignment. -/
structure Lowered {Arch BlockId : Type} [TargetArch Arch]
    (blocks : List (DirectBlock Arch BlockId)) (rootBlock : DirectBlock Arch BlockId) where
  builder : Builder Arch BlockId
  blocksExact : builder.blocks = blocks
  rootRef : BlockRef Arch BlockId
  rootExact : rootRef.definition = rootBlock.toBasicBlock
  rootInterned : rootRef.Interned (builder.blocks.map DirectBlock.toBasicBlock)

namespace Lowered

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def graph {Arch BlockId : Type} [TargetArch Arch]
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    (lowered : Lowered blocks rootBlock) :
    TypedControlFlowGraph Arch BlockId :=
  Builder.finalize lowered.builder lowered.rootRef lowered.rootInterned

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem graph_blocks {Arch BlockId : Type} [TargetArch Arch]
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    (lowered : Lowered blocks rootBlock) :
    lowered.graph.blocks = blocks.map DirectBlock.toBasicBlock := by
  simp only [graph, Builder.finalize]
  rw [lowered.blocksExact]

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem graph_entry {Arch BlockId : Type} [TargetArch Arch]
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    (lowered : Lowered blocks rootBlock) :
    lowered.graph.entry = rootBlock.entry := by
  simp only [graph, Builder.finalize, BlockRef.entry]
  rw [lowered.rootExact]
  rfl

end Lowered

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Postorder structural lowering through the existing acyclic `CFGBuilder`. All logical and target
    facts come from `Realizes`; lowering creates no edge, world, flag, or execution evidence. -/
noncomputable def lower {Arch BlockId Scope : Type} [TargetArch Arch]
    {source : Structured.Expr InputContext .word} {roles : List (NodeId Scope)}
    {root : NodeId Scope} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    {assignment : Assignment Arch BlockId plan blocks rootBlock}
    (realizes : Realizes plan assignment) : Lowered blocks rootBlock :=
  match realizes with
  | .leaf (block := block) realization => by
      let interned := Builder.intern (Builder.empty Arch BlockId) block
        (by simp [Builder.empty]) (by
          intro state accepted
          exact targetFree_targetsInterned (realization.targetFree state accepted) [])
      exact {
        builder := interned.builder
        blocksExact := by rfl
        rootRef := interned.ref
        rootExact := interned.definition
        rootInterned := interned.interned
      }
  | .branch (role := role) (trueRoles := trueRoles) (falseRoles := falseRoles)
      (trueRoot := trueRoot) (falseRoot := falseRoot) (truePlan := truePlan)
      (falsePlan := falsePlan) (disjoint := disjoint) (fresh := fresh)
      (trueBlocks := trueBlocks) (falseBlocks := falseBlocks)
      (trueRootBlock := trueRootBlock) (falseRootBlock := falseRootBlock)
      (block := block) (trueAssignment := trueAssignment)
      (falseAssignment := falseAssignment) (disjointIds := disjointIds)
      (freshId := freshId)
      trueRealizes falseRealizes realization => by
      let trueLowered := lower trueRealizes
      let falseLowered := lower falseRealizes
      let children := Builder.append falseLowered.builder trueLowered.builder (by
        intro falseId falseMember trueId trueMember
        rw [falseLowered.blocksExact] at falseMember
        rw [trueLowered.blocksExact] at trueMember
        rcases List.mem_map.mp falseMember with ⟨falseBlock, falseBlockMember, rfl⟩
        rcases List.mem_map.mp trueMember with ⟨trueBlock, trueBlockMember, rfl⟩
        exact disjointIds falseBlock falseBlockMember trueBlock trueBlockMember)
      let parent := Builder.intern children block (by
        intro member
        simp only [children, Builder.append, falseLowered.blocksExact,
          trueLowered.blocksExact, List.map_append] at member
        exact freshId (by simpa [List.map_append] using member)) (by
        intro state accepted
        have exactTargets := realization.targetsExact state accepted
        rcases resultEq : block.body state accepted with
          ⟨ExitState, exit, terminator⟩
        rw [resultEq] at exactTargets
        simp only at exactTargets
        cases terminator with
        | jmp => exact exactTargets.elim
        | jcc selected trueRef edgeTrue trueExact falseRef edgeFalse falseExact =>
            rcases exactTargets with ⟨trueDefinition, falseDefinition⟩
            constructor
            · change trueRef.definition ∈ children.blocks.map DirectBlock.toBasicBlock
              rw [trueDefinition]
              apply List.mem_map.mpr
              refine ⟨trueRootBlock, ?_, rfl⟩
              simp only [children, Builder.append]
              apply List.mem_append_right
              rw [trueLowered.blocksExact]
              exact trueAssignment.root_mem
            · change falseRef.definition ∈ children.blocks.map DirectBlock.toBasicBlock
              rw [falseDefinition]
              apply List.mem_map.mpr
              refine ⟨falseRootBlock, ?_, rfl⟩
              simp only [children, Builder.append]
              apply List.mem_append_left
              rw [falseLowered.blocksExact]
              exact falseAssignment.root_mem
        | ret => exact exactTargets.elim
        | sysExit => exact exactTargets.elim
        | halt => exact exactTargets.elim)
      exact {
        builder := parent.builder
        blocksExact := by
          change children.blocks ++ [block] = falseBlocks ++ trueBlocks ++ [block]
          simp [children, Builder.append, falseLowered.blocksExact,
            trueLowered.blocksExact]
        rootRef := parent.ref
        rootExact := parent.definition
        rootInterned := parent.interned
      }

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem lower_graph_blocks {Arch BlockId Scope : Type} [TargetArch Arch]
    {source : Structured.Expr InputContext .word} {roles : List (NodeId Scope)}
    {root : NodeId Scope} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    {assignment : Assignment Arch BlockId plan blocks rootBlock}
    (realizes : Realizes plan assignment) :
    realizes.lower.graph.blocks = blocks.map DirectBlock.toBasicBlock :=
  realizes.lower.graph_blocks

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem lower_graph_entry {Arch BlockId Scope : Type} [TargetArch Arch]
    {source : Structured.Expr InputContext .word} {roles : List (NodeId Scope)}
    {root : NodeId Scope} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    {assignment : Assignment Arch BlockId plan blocks rootBlock}
    (realizes : Realizes plan assignment) :
    realizes.lower.graph.entry = rootBlock.entry :=
  realizes.lower.graph_entry

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem lower_definition_mem {Arch BlockId Scope : Type} [TargetArch Arch]
    {source : Structured.Expr InputContext .word} {roles : List (NodeId Scope)}
    {root : NodeId Scope} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock block : DirectBlock Arch BlockId}
    {assignment : Assignment Arch BlockId plan blocks rootBlock}
    (realizes : Realizes plan assignment) (member : block ∈ blocks) :
    block.toBasicBlock ∈ realizes.lower.graph.blocks := by
  rw [realizes.lower.graph_blocks]
  apply List.mem_map.mpr
  exact ⟨block, member, rfl⟩

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
theorem lower_buildHistory {Arch BlockId Scope : Type} [TargetArch Arch]
    {source : Structured.Expr InputContext .word} {roles : List (NodeId Scope)}
    {root : NodeId Scope} {plan : Plan Scope source roles root}
    {blocks : List (DirectBlock Arch BlockId)} {rootBlock : DirectBlock Arch BlockId}
    {assignment : Assignment Arch BlockId plan blocks rootBlock}
    (realizes : Realizes plan assignment) :
    BuildHistory realizes.lower.builder.blocks :=
  realizes.lower.builder.history

end Realizes

end Gasm.Compiler.Word.StructuredCFG

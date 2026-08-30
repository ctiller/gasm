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

import Gasm.Core.CFGBuilder

namespace Gasm.Core.RecursiveCFGBuilder

open Gasm.Core.CFGBuilder

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- A finite declaration scope exists before any body. `indices` enumerates every declaration
    exactly once, while `entry` carries its full dependent entry contract. -/
structure Scope (Arch BlockId Index : Type) [TargetArch Arch] where
  indices : List Index
  complete : ∀ index, index ∈ indices
  uniqueIndices : indices.Nodup
  entry : Index → BlockEntry Arch BlockId
  idInjective : Function.Injective (fun index => (entry index).id)

namespace Scope

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Canonical finite generated scope. -/
def fin {Arch BlockId : Type} [TargetArch Arch] (size : Nat)
    (entry : Fin size → BlockEntry Arch BlockId)
    (idInjective : Function.Injective (fun index => (entry index).id)) :
    Scope Arch BlockId (Fin size) where
  indices := List.finRange size
  complete := List.mem_finRange
  uniqueIndices := List.nodup_finRange size
  entry := entry
  idInjective := idInjective

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Remap nominal block identity without changing the finite declaration identity or contracts. -/
def mapBlockId {Arch OldId NewId Index : Type} [TargetArch Arch]
    (scope : Scope Arch OldId Index) (embedding : Builder.IdEmbedding OldId NewId) :
    Scope Arch NewId Index where
  indices := scope.indices
  complete := scope.complete
  uniqueIndices := scope.uniqueIndices
  entry := fun index => mapEntryId embedding.toFun (scope.entry index)
  idInjective := by
    intro left right same
    apply scope.idInjective
    apply embedding.injective
    exact same

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Combine already independent declaration scopes. New definitions authored against this combined
    scope may form cross-component recursion; composing definitions authored earlier cannot. -/
def sum {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    (left : Scope Arch LeftId LeftIndex) (right : Scope Arch RightId RightIndex) :
    Scope Arch (Sum LeftId RightId) (Sum LeftIndex RightIndex) where
  indices := left.indices.map Sum.inl ++ right.indices.map Sum.inr
  complete := by
    intro index
    cases index with
    | inl leftIndex =>
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨leftIndex, left.complete leftIndex, rfl⟩
    | inr rightIndex =>
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨rightIndex, right.complete rightIndex, rfl⟩
  uniqueIndices := by
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (Builder.IdEmbedding.sumLeft LeftIndex RightIndex).map_nodup left.uniqueIndices
    · exact (Builder.IdEmbedding.sumRight LeftIndex RightIndex).map_nodup right.uniqueIndices
    · intro leftIndex leftMember rightIndex rightMember
      rcases List.mem_map.mp leftMember with ⟨leftValue, _, rfl⟩
      rcases List.mem_map.mp rightMember with ⟨rightValue, _, rfl⟩
      exact Builder.IdEmbedding.sum_disjoint leftValue rightValue
  entry
    | .inl index => mapEntryId Sum.inl (left.entry index)
    | .inr index => mapEntryId Sum.inr (right.entry index)
  idInjective := by
    intro first second same
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            simp only [mapEntryId_id, Sum.inl.injEq] at same
            exact congrArg Sum.inl (left.idInjective same)
        | inr second => simp at same
    | inr first =>
        cases second with
        | inl second => simp at same
        | inr second =>
            simp only [mapEntryId_id, Sum.inr.injEq] at same
            exact congrArg Sum.inr (right.idInjective same)

end Scope

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Pre-seal reference to one declaration in one exact scope. It is intentionally distinct from
    `BlockRef`: no block definition exists yet. -/
structure DeclRef {Arch BlockId Index : Type} [TargetArch Arch]
    (scope : Scope Arch BlockId Index) where
  index : Index

namespace DeclRef

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def entry {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (ref : DeclRef scope) : BlockEntry Arch BlockId :=
  scope.entry ref.index

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def mapBlockId {Arch OldId NewId Index : Type} [TargetArch Arch]
    {scope : Scope Arch OldId Index} (embedding : Builder.IdEmbedding OldId NewId)
    (ref : DeclRef scope) : DeclRef (scope.mapBlockId embedding) :=
  ⟨ref.index⟩

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def sumLeft {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {left : Scope Arch LeftId LeftIndex} {right : Scope Arch RightId RightIndex}
    (ref : DeclRef left) : DeclRef (left.sum right) :=
  ⟨.inl ref.index⟩

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def sumRight {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {left : Scope Arch LeftId LeftIndex} {right : Scope Arch RightId RightIndex}
    (ref : DeclRef right) : DeclRef (left.sum right) :=
  ⟨.inr ref.index⟩

end DeclRef

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
private def mapEdge {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {source : ComposedState Arch S}
    (edge : BlockEdge (BlockId := OldId) source) : BlockEdge (BlockId := NewId) source where
  target := mapEntryId map edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
private def mapConditionalEdge {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {source : ComposedState Arch S} {enabled : Prop}
    (edge : ConditionalBlockEdge (BlockId := OldId) source enabled) :
    ConditionalBlockEdge (BlockId := NewId) source enabled where
  target := mapEntryId map edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Recursive authoring terminator. Every selected static target is a declaration reference from the
    same scope and retains the existing typed edge contract. -/
inductive RecursiveTerminator {Arch BlockId Index : Type} [TargetArch Arch]
    (scope : Scope Arch BlockId Index) {S : Type} (exit : ComposedState Arch S) where
  | jmp (target : DeclRef scope) (edge : BlockEdge (BlockId := BlockId) exit)
      (targetExact : edge.target = target.entry) : RecursiveTerminator scope exit
  | jcc (condition : ConditionCode Arch)
      (targetTrue : DeclRef scope)
      (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
        (condition.holds exit.machine))
      (trueExact : edgeTrue.target = targetTrue.entry)
      (targetFalse : DeclRef scope)
      (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
        (¬ condition.holds exit.machine))
      (falseExact : edgeFalse.target = targetFalse.entry) : RecursiveTerminator scope exit
  | ret (exportedObligations : List ObligationToken) (bytesToPop : UInt16 := 0)
      (stackClean : exit.stackDepth = 0)
      (obligationsMatch : exit.obligations = exportedObligations)
      (callee : CalleeDiscipline Arch exit) : RecursiveTerminator scope exit
  | sysExit (exitCode : UInt8)
      (droppable : ∀ obligation ∈ exit.obligations, obligation.isDroppableOnExit) :
      RecursiveTerminator scope exit
  | halt (droppable : ∀ obligation ∈ exit.obligations, obligation.isDroppableOnExit) :
      RecursiveTerminator scope exit

namespace RecursiveTerminator

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Erase declaration references into the sole core terminator family. -/
def toCpu {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} {S : Type} {exit : ComposedState Arch S} :
    RecursiveTerminator scope exit → CpuTerminator Arch BlockId exit
  | .jmp _ edge _ => .jmp edge
  | .jcc condition _ edgeTrue _ _ edgeFalse _ => .jcc condition edgeTrue edgeFalse
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Transport a recursive body through an injective nominal BlockId embedding. -/
def mapBlockId {Arch OldId NewId Index : Type} [TargetArch Arch]
    {scope : Scope Arch OldId Index} (embedding : Builder.IdEmbedding OldId NewId)
    {S : Type} {exit : ComposedState Arch S} :
    RecursiveTerminator scope exit → RecursiveTerminator (scope.mapBlockId embedding) exit
  | .jmp target edge targetExact =>
      .jmp (target.mapBlockId embedding) (mapEdge embedding.toFun edge)
        (congrArg (mapEntryId embedding.toFun) targetExact)
  | .jcc condition targetTrue edgeTrue trueExact targetFalse edgeFalse falseExact =>
      .jcc condition (targetTrue.mapBlockId embedding)
        (mapConditionalEdge embedding.toFun edgeTrue)
        (congrArg (mapEntryId embedding.toFun) trueExact)
        (targetFalse.mapBlockId embedding)
        (mapConditionalEdge embedding.toFun edgeFalse)
        (congrArg (mapEntryId embedding.toFun) falseExact)
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Embed a closed left-component terminator into a combined declaration scope. This cannot create
    a new cross-component edge: every retained target is still `Sum.inl` of an old declaration. -/
def sumLeft {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {left : Scope Arch LeftId LeftIndex} {right : Scope Arch RightId RightIndex}
    {S : Type} {exit : ComposedState Arch S} :
    RecursiveTerminator left exit → RecursiveTerminator (left.sum right) exit
  | .jmp target edge targetExact =>
      .jmp target.sumLeft (mapEdge Sum.inl edge)
        (congrArg (mapEntryId Sum.inl) targetExact)
  | .jcc condition targetTrue edgeTrue trueExact targetFalse edgeFalse falseExact =>
      .jcc condition targetTrue.sumLeft (mapConditionalEdge Sum.inl edgeTrue)
        (congrArg (mapEntryId Sum.inl) trueExact)
        targetFalse.sumLeft (mapConditionalEdge Sum.inl edgeFalse)
        (congrArg (mapEntryId Sum.inl) falseExact)
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Embed a closed right-component terminator into a combined declaration scope. -/
def sumRight {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {left : Scope Arch LeftId LeftIndex} {right : Scope Arch RightId RightIndex}
    {S : Type} {exit : ComposedState Arch S} :
    RecursiveTerminator right exit → RecursiveTerminator (left.sum right) exit
  | .jmp target edge targetExact =>
      .jmp target.sumRight (mapEdge Sum.inr edge)
        (congrArg (mapEntryId Sum.inr) targetExact)
  | .jcc condition targetTrue edgeTrue trueExact targetFalse edgeFalse falseExact =>
      .jcc condition targetTrue.sumRight (mapConditionalEdge Sum.inr edgeTrue)
        (congrArg (mapEntryId Sum.inr) trueExact)
        targetFalse.sumRight (mapConditionalEdge Sum.inr edgeFalse)
        (congrArg (mapEntryId Sum.inr) falseExact)
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

end RecursiveTerminator

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Total dependent body table. Exactly one definition is supplied for every declaration by
    construction; there is no partial list or caller-proved “defined once” ledger. -/
structure Definitions {Arch BlockId Index : Type} [TargetArch Arch]
    (scope : Scope Arch BlockId Index) where
  body : (index : Index) →
    (state : ComposedState Arch (scope.entry index).State) →
    (scope.entry index).accepts state →
    Σ (ExitState : Type), Σ (exit : ComposedState Arch ExitState),
      RecursiveTerminator scope exit

namespace Definitions

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Reuse every total body and edge proof across an injective nominal BlockId remapping. -/
def mapBlockId {Arch OldId NewId Index : Type} [TargetArch Arch]
    {scope : Scope Arch OldId Index} (definitions : Definitions scope)
    (embedding : Builder.IdEmbedding OldId NewId) :
    Definitions (scope.mapBlockId embedding) where
  body := fun index state accepted =>
    let result := definitions.body index state accepted
    ⟨result.1, result.2.1, result.2.2.mapBlockId embedding⟩

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Compose definitions already authored independently. Their targets remain on their original side;
    cross-component mutual recursion requires authoring a new total table against `Scope.sum`. -/
def sum {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {leftScope : Scope Arch LeftId LeftIndex} {rightScope : Scope Arch RightId RightIndex}
    (left : Definitions leftScope) (right : Definitions rightScope) :
    Definitions (leftScope.sum rightScope) where
  body := fun index state accepted =>
    match index with
    | .inl leftIndex =>
        let result := left.body leftIndex state accepted
        ⟨result.1, result.2.1, result.2.2.sumLeft⟩
    | .inr rightIndex =>
        let result := right.body rightIndex state accepted
        ⟨result.1, result.2.1, result.2.2.sumRight⟩

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Generate the one core block definition belonging to a declaration index. -/
def block {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope)
    (index : Index) : BasicBlock Arch BlockId where
  entry := scope.entry index
  body := fun state accepted =>
    let result := definitions.body index state accepted
    ⟨result.1, result.2.1, result.2.2.toCpu⟩

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Nominal remapping preserves the exact generated block definition, including its body. -/
theorem mapBlockId_block {Arch OldId NewId Index : Type} [TargetArch Arch]
    {scope : Scope Arch OldId Index} (definitions : Definitions scope)
    (embedding : Builder.IdEmbedding OldId NewId) (index : Index) :
    mapBasicBlockId embedding.toFun (definitions.block index) =
      (definitions.mapBlockId embedding).block index := by
  simp only [block, mapBasicBlockId, Definitions.mapBlockId]
  congr
  funext state accepted
  rcases result : definitions.body index state accepted with
    ⟨ExitState, exit, terminator⟩
  cases terminator <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Left component definitions survive collision-free composition exactly, modulo `Sum.inl` ID
    remapping. -/
theorem sum_block_left {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {leftScope : Scope Arch LeftId LeftIndex} {rightScope : Scope Arch RightId RightIndex}
    (left : Definitions leftScope) (right : Definitions rightScope) (index : LeftIndex) :
    mapBasicBlockId (Sum.inl : LeftId → Sum LeftId RightId) (left.block index) =
      (left.sum right).block (.inl index) := by
  simp only [block, mapBasicBlockId, Definitions.sum]
  congr
  funext state accepted
  rcases result : left.body index state accepted with ⟨ExitState, exit, terminator⟩
  cases terminator <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Right component definitions survive collision-free composition exactly, modulo `Sum.inr`. -/
theorem sum_block_right {Arch LeftId RightId LeftIndex RightIndex : Type} [TargetArch Arch]
    {leftScope : Scope Arch LeftId LeftIndex} {rightScope : Scope Arch RightId RightIndex}
    (left : Definitions leftScope) (right : Definitions rightScope) (index : RightIndex) :
    mapBasicBlockId (Sum.inr : RightId → Sum LeftId RightId) (right.block index) =
      (left.sum right).block (.inr index) := by
  simp only [block, mapBasicBlockId, Definitions.sum]
  congr
  funext state accepted
  rcases result : right.body index state accepted with ⟨ExitState, exit, terminator⟩
  cases terminator <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Closed generated definition table in declaration order. -/
def blocks {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope) :
    List (BasicBlock Arch BlockId) :=
  scope.indices.map definitions.block

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
theorem block_mem {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope) (index : Index) :
    definitions.block index ∈ definitions.blocks := by
  exact List.mem_map.mpr ⟨index, scope.complete index, rfl⟩

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
theorem uniqueBlockIds {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope) :
    (definitions.blocks.map (·.entry.id)).Nodup := by
  let embedding : Builder.IdEmbedding Index BlockId := {
    toFun := fun index => (scope.entry index).id
    injective := scope.idInjective
  }
  have unique := embedding.map_nodup scope.uniqueIndices
  simp only [blocks, List.map_map]
  have functions : ((fun block => block.entry.id) ∘ definitions.block) =
      embedding.toFun := by
    funext index
    rfl
  rw [functions]
  exact unique

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Seal the total table directly into the existing closed typed CFG. Self and mutual references
    close because every declaration index has a generated definition in the same finite table. -/
def toGraph {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope)
    (entry : DeclRef scope) : TypedControlFlowGraph Arch BlockId where
  blocks := definitions.blocks
  entry := entry.entry
  entryInGraph := ⟨definitions.block entry.index, definitions.block_mem entry.index, rfl⟩
  uniqueIds := definitions.uniqueBlockIds
  targetsInGraph := by
    intro source sourceMember state accepted
    rcases List.mem_map.mp sourceMember with ⟨index, indexMember, sourceExact⟩
    subst source
    rcases result : definitions.body index state accepted with
      ⟨ExitState, exit, terminator⟩
    simp only [blocks, block]
    rw [result]
    simp only
    cases terminator with
    | jmp target edge targetExact =>
        exact ⟨definitions.block target.index, definitions.block_mem target.index,
          targetExact.symm⟩
    | jcc condition targetTrue edgeTrue trueExact targetFalse edgeFalse falseExact =>
        exact ⟨⟨definitions.block targetTrue.index, definitions.block_mem targetTrue.index,
          trueExact.symm⟩,
          definitions.block targetFalse.index, definitions.block_mem targetFalse.index,
          falseExact.symm⟩
    | ret | sysExit | halt => trivial

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Sealing result exposes only the existing core graph plus exact generated-definition references.
    It is frontend evidence, not an execution or emission authority. -/
structure Sealed {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope) where
  graph : TypedControlFlowGraph Arch BlockId
  graphBlocks : graph.blocks = definitions.blocks
  ref : Index → BlockRef Arch BlockId
  refExact : ∀ index, (ref index).definition = definitions.block index
  refInterned : ∀ index, (ref index).Interned graph.blocks

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def sealDefinitions {Arch BlockId Index : Type} [TargetArch Arch]
    {scope : Scope Arch BlockId Index} (definitions : Definitions scope)
    (entry : DeclRef scope) : Sealed definitions where
  graph := definitions.toGraph entry
  graphBlocks := rfl
  ref := fun index => BlockRef.ofBlock (definitions.block index)
  refExact := by intro index; rfl
  refInterned := by intro index; exact definitions.block_mem index

end Definitions

end Gasm.Core.RecursiveCFGBuilder

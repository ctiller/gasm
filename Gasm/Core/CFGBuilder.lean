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

import Gasm.Core.CFG

namespace Gasm.Core.CFGBuilder

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Change only nominal proof identity. Typestate, stack expectation, and entry predicate are
    definitionally unchanged. -/
def mapEntryId {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (entry : BlockEntry Arch OldId) : BlockEntry Arch NewId where
  State := entry.State
  id := map entry.id
  expectedDepth := entry.expectedDepth
  accepts := entry.accepts

@[simp] theorem mapEntryId_id {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (entry : BlockEntry Arch OldId) :
    (mapEntryId map entry).id = map entry.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Remap an exact core edge without changing its concrete or ghost-world transfer. -/
def mapEdgeId {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {source : ComposedState Arch S}
    (edge : BlockEdge (BlockId := OldId) source) : BlockEdge (BlockId := NewId) source where
  target := mapEntryId map edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished

private def mapConditionalEdgeId {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {source : ComposedState Arch S} {enabled : Prop}
    (edge : ConditionalBlockEdge (BlockId := OldId) source enabled) :
    ConditionalBlockEdge (BlockId := NewId) source enabled where
  target := mapEntryId map edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished

private def mapIndirectEdgeId {Arch OldId NewId : Type} [TargetArch Arch] {S TargetId : Type}
    (map : OldId → NewId) {source : ComposedState Arch S}
    (indirect : IndirectBlockEdge (BlockId := OldId) (TargetId := TargetId) source) :
    IndirectBlockEdge (BlockId := NewId) (TargetId := TargetId) source where
  decodeTarget := indirect.decodeTarget
  candidates := indirect.candidates.map (fun candidate =>
    (candidate.1, mapEntryId map candidate.2))
  uniqueTargetIds := by
    have sameKeys :
        (indirect.candidates.map (fun candidate =>
          (candidate.1, mapEntryId map candidate.2))).map Prod.fst =
          indirect.candidates.map Prod.fst := by
      simp
    rw [sameKeys]
    exact indirect.uniqueTargetIds
  edge := mapEdgeId map indirect.edge
  resolved := by
    rcases indirect.resolved with ⟨candidate, member, decoded, target⟩
    refine ⟨(candidate.1, mapEntryId map candidate.2), ?_, decoded, ?_⟩
    · exact List.mem_map.mpr ⟨candidate, member, rfl⟩
    · exact congrArg (mapEntryId map) target

private def mapCpuTerminatorId {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {exit : ComposedState Arch S} :
    CpuTerminator Arch OldId exit → CpuTerminator Arch NewId exit
  | .jmp edge => .jmp (mapEdgeId map edge)
  | .jmpIndirect edge => .jmpIndirect (mapIndirectEdgeId map edge)
  | .jcc cond targetTrue targetFalse =>
      .jcc cond (mapConditionalEdgeId map targetTrue) (mapConditionalEdgeId map targetFalse)
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Remap a complete core block definition. This is used only to transport exact symbolic
    definition identity across an injective component-ID embedding. -/
def mapBasicBlockId {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (block : BasicBlock Arch OldId) : BasicBlock Arch NewId where
  entry := mapEntryId map block.entry
  body := fun state accepted =>
    let result := block.body state accepted
    ⟨result.1, result.2.1, mapCpuTerminatorId map result.2.2⟩

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- A symbolic block reference retains the exact supplied core block definition. Its entry ID is
    nominal proof identity; no text label or machine address participates in reference equality.
    Exact definition membership prevents a different body with the same entry from satisfying the
    reference. -/
structure BlockRef (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  definition : BasicBlock Arch BlockId

namespace BlockRef

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Refer to the exact entry contract of a supplied target block. This shares the block definition;
    cloning requires constructing a block with a distinct nominal ID. -/
def ofBlock {Arch BlockId : Type} [TargetArch Arch]
    (block : BasicBlock Arch BlockId) : BlockRef Arch BlockId :=
  ⟨block⟩

def entry {Arch BlockId : Type} [TargetArch Arch]
    (ref : BlockRef Arch BlockId) : BlockEntry Arch BlockId :=
  ref.definition.entry

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
def mapId {Arch OldId NewId : Type} [TargetArch Arch] (map : OldId → NewId)
    (ref : BlockRef Arch OldId) : BlockRef Arch NewId :=
  ⟨mapBasicBlockId map ref.definition⟩

@[simp] theorem mapId_entry {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (ref : BlockRef Arch OldId) :
    (ref.mapId map).entry = mapEntryId map ref.entry := rfl

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- A reference is interned only when its exact supplied definition is published by the table. -/
def Interned {Arch BlockId : Type} [TargetArch Arch]
    (ref : BlockRef Arch BlockId) (blocks : List (BasicBlock Arch BlockId)) : Prop :=
  ref.definition ∈ blocks

theorem Interned.weakenRight {Arch BlockId : Type} [TargetArch Arch]
    {ref : BlockRef Arch BlockId} {before after : List (BasicBlock Arch BlockId)}
    (interned : ref.Interned before) : ref.Interned (before ++ after) := by
  exact List.mem_append_left _ interned

theorem Interned.weakenLeft {Arch BlockId : Type} [TargetArch Arch]
    {ref : BlockRef Arch BlockId} {before after : List (BasicBlock Arch BlockId)}
    (interned : ref.Interned after) : ref.Interned (before ++ after) := by
  exact List.mem_append_right _ interned

end BlockRef

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Authoring terminators for the first selected control-flow slice. Direct jumps retain the exact
    core `BlockEdge`; target-free terminators carry no artificial target-closure obligation. -/
inductive DirectTerminator {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    (exit : ComposedState Arch S) where
  | jmp (target : BlockRef Arch BlockId) (edge : BlockEdge (BlockId := BlockId) exit)
      (targetExact : edge.target = target.entry) : DirectTerminator exit
  | ret (exportedObligations : List ObligationToken) (bytesToPop : UInt16 := 0)
      (stackClean : exit.stackDepth = 0)
      (obligationsMatch : exit.obligations = exportedObligations)
      (callee : CalleeDiscipline Arch exit) : DirectTerminator exit
  | sysExit (exitCode : UInt8)
      (droppable : ∀ obligation ∈ exit.obligations, obligation.isDroppableOnExit) :
      DirectTerminator exit
  | halt (droppable : ∀ obligation ∈ exit.obligations, obligation.isDroppableOnExit) :
      DirectTerminator exit

namespace DirectTerminator

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Author a direct jump from the supplied target `BasicBlock` value. The block is referenced,
    never silently cloned; layout remains deferred. -/
def jmpToBlock {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} (target : BasicBlock Arch BlockId)
    (edge : BlockEdge (BlockId := BlockId) exit) (targetExact : edge.target = target.entry) :
    DirectTerminator (BlockId := BlockId) exit :=
  .jmp (BlockRef.ofBlock target) edge targetExact

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Nominal remapping preserves the selected terminator and all of its core contracts. -/
def mapId {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {exit : ComposedState Arch S} :
    DirectTerminator (BlockId := OldId) exit → DirectTerminator (BlockId := NewId) exit
  | .jmp target edge targetExact =>
      .jmp (target.mapId map) (mapEdgeId map edge)
        (congrArg (mapEntryId map) targetExact)
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Elaborate authoring syntax to the sole core terminator family. -/
def toCpu {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} : DirectTerminator (BlockId := BlockId) exit →
      CpuTerminator Arch BlockId exit
  | .jmp _ edge _ => .jmp edge
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Only a selected direct jump asks the builder for target membership. -/
def TargetsInterned {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} (blocks : List (BasicBlock Arch BlockId)) :
    DirectTerminator (BlockId := BlockId) exit → Prop
  | .jmp target _ _ => target.Interned blocks
  | .ret .. | .sysExit .. | .halt .. => True

theorem TargetsInterned.weakenRight {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} {before after : List (BasicBlock Arch BlockId)}
    {terminator : DirectTerminator (BlockId := BlockId) exit}
    (closed : terminator.TargetsInterned before) :
    terminator.TargetsInterned (before ++ after) := by
  cases terminator with
  | jmp => exact BlockRef.Interned.weakenRight closed
  | ret | sysExit | halt => trivial

theorem TargetsInterned.weakenLeft {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} {before after : List (BasicBlock Arch BlockId)}
    {terminator : DirectTerminator (BlockId := BlockId) exit}
    (closed : terminator.TargetsInterned after) :
    terminator.TargetsInterned (before ++ after) := by
  cases terminator with
  | jmp => exact BlockRef.Interned.weakenLeft closed
  | ret | sysExit | halt => trivial

end DirectTerminator

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- A block authored with only direct symbolic jumps and target-free terminators. -/
structure DirectBlock (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  entry : BlockEntry Arch BlockId
  body : (state : ComposedState Arch entry.State) → entry.accepts state →
    Σ (ExitState : Type), Σ (exit : ComposedState Arch ExitState),
      DirectTerminator (BlockId := BlockId) exit

namespace DirectBlock

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Remap one authored definition. The block body and every edge proof are reused. -/
def mapId {Arch OldId NewId : Type} [TargetArch Arch] (map : OldId → NewId)
    (block : DirectBlock Arch OldId) : DirectBlock Arch NewId where
  entry := mapEntryId map block.entry
  body := fun state accepted =>
    let result := block.body state accepted
    ⟨result.1, result.2.1, result.2.2.mapId map⟩

@[simp] theorem mapId_entry {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (block : DirectBlock Arch OldId) :
    (block.mapId map).entry = mapEntryId map block.entry := rfl

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Erase frontend-only references into the existing typed core block. -/
def toBasicBlock {Arch BlockId : Type} [TargetArch Arch]
    (block : DirectBlock Arch BlockId) : BasicBlock Arch BlockId where
  entry := block.entry
  body := fun state accepted =>
    let result := block.body state accepted
    ⟨result.1, result.2.1, result.2.2.toCpu⟩

@[simp] theorem toBasicBlock_entry {Arch BlockId : Type} [TargetArch Arch]
    (block : DirectBlock Arch BlockId) : block.toBasicBlock.entry = block.entry := rfl

theorem map_toBasicBlock_entry_ids {Arch BlockId : Type} [TargetArch Arch]
    (blocks : List (DirectBlock Arch BlockId)) :
    (blocks.map DirectBlock.toBasicBlock).map (·.entry.id) = blocks.map (·.entry.id) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [List.map_cons, toBasicBlock_entry, ih]

theorem mapId_entry_ids {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (blocks : List (DirectBlock Arch OldId)) :
    (blocks.map (DirectBlock.mapId map)).map (·.entry.id) =
      (blocks.map (·.entry.id)).map map := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [List.map_cons, mapId_entry, mapEntryId_id, ih]

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Erasure commutes with nominal-ID remapping, including the exact body definition retained by a
    `BlockRef`. -/
theorem map_toBasicBlock {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) (block : DirectBlock Arch OldId) :
    mapBasicBlockId map block.toBasicBlock = (block.mapId map).toBasicBlock := by
  cases block with
  | mk entry body =>
      simp only [toBasicBlock, mapBasicBlockId, mapId]
      congr
      funext state accepted
      rcases result : body state accepted with ⟨ExitState, exit, terminator⟩
      cases terminator <;> rfl

end DirectBlock

namespace BlockRef.Interned

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
theorem mapId {Arch OldId NewId : Type} [TargetArch Arch]
    (map : OldId → NewId) {ref : BlockRef Arch OldId}
    {blocks : List (DirectBlock Arch OldId)}
    (interned : ref.Interned (blocks.map DirectBlock.toBasicBlock)) :
    (ref.mapId map).Interned
      ((blocks.map (DirectBlock.mapId map)).map DirectBlock.toBasicBlock) := by
  rcases List.mem_map.mp interned with ⟨source, sourceMember, sameDefinition⟩
  apply List.mem_map.mpr
  refine ⟨source.mapId map, List.mem_map.mpr ⟨source, sourceMember, rfl⟩, ?_⟩
  change (source.mapId map).toBasicBlock = mapBasicBlockId map ref.definition
  exact (DirectBlock.map_toBasicBlock map source).symm.trans
    (congrArg (mapBasicBlockId map) sameDefinition)

end BlockRef.Interned

namespace DirectTerminator.TargetsInterned

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
theorem mapId {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {exit : ComposedState Arch S}
    {terminator : DirectTerminator (BlockId := OldId) exit}
    {blocks : List (DirectBlock Arch OldId)}
    (closed : terminator.TargetsInterned (blocks.map DirectBlock.toBasicBlock)) :
    (terminator.mapId map).TargetsInterned
      ((blocks.map (DirectBlock.mapId map)).map DirectBlock.toBasicBlock) := by
  cases terminator with
  | jmp => exact BlockRef.Interned.mapId map closed
  | ret | sysExit | halt => trivial

end DirectTerminator.TargetsInterned

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- A construction-order witness for a finite builder table. The only way to add one block requires
    every selected direct target to occur in the previous table. Independent histories may be
    appended only when their nominal ID sets are disjoint. Consequently a self- or mutual cycle has
    no constructor in this first acyclic slice. -/
inductive BuildHistory {Arch BlockId : Type} [TargetArch Arch] :
    List (DirectBlock Arch BlockId) → Prop where
  | empty : BuildHistory []
  | intern {blocks : List (DirectBlock Arch BlockId)}
      (history : BuildHistory blocks) (block : DirectBlock Arch BlockId)
      (fresh : block.entry.id ∉ blocks.map (·.entry.id))
      (closed : ∀ (state : ComposedState Arch block.entry.State)
        (accepted : block.entry.accepts state),
        let result := block.body state accepted
        result.2.2.TargetsInterned (blocks.map DirectBlock.toBasicBlock)) :
      BuildHistory (blocks ++ [block])
  | append {left right : List (DirectBlock Arch BlockId)}
      (leftHistory : BuildHistory left) (rightHistory : BuildHistory right)
      (disjoint : ∀ leftId ∈ left.map (·.entry.id),
        ∀ rightId ∈ right.map (·.entry.id), leftId ≠ rightId) :
      BuildHistory (left ++ right)

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- The finite acyclic builder invariant. A newly interned block may jump only to blocks already in
    the table; every nominal ID has one definition. -/
structure Builder (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  blocks : List (DirectBlock Arch BlockId)
  history : BuildHistory blocks
  uniqueIds : (blocks.map (·.entry.id)).Nodup
  targetsInterned : ∀ block ∈ blocks,
    ∀ (state : ComposedState Arch block.entry.State) (accepted : block.entry.accepts state),
      let result := block.body state accepted
      result.2.2.TargetsInterned (blocks.map DirectBlock.toBasicBlock)

namespace Builder

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
def empty (Arch : Type) [TargetArch Arch] (BlockId : Type) : Builder Arch BlockId where
  blocks := []
  history := .empty
  uniqueIds := by simp
  targetsInterned := by simp

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- An injective nominal remapping. This is the reusable collision-freedom premise for generated
    scopes; it carries no layout or byte claim. -/
structure IdEmbedding (OldId NewId : Type) where
  toFun : OldId → NewId
  injective : Function.Injective toFun

namespace IdEmbedding

theorem map_nodup {OldId NewId : Type} (embedding : IdEmbedding OldId NewId)
    {values : List OldId} (unique : values.Nodup) :
    (values.map embedding.toFun).Nodup := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique ⊢
      exact ⟨by
        intro member
        rcases List.mem_map.mp member with ⟨other, otherMember, same⟩
        have equal : other = value := embedding.injective same
        subst other
        exact unique.1 otherMember,
        ih unique.2⟩

def sumLeft (LeftId RightId : Type) : IdEmbedding LeftId (Sum LeftId RightId) where
  toFun := Sum.inl
  injective := by intro left right same; cases same; rfl

def sumRight (LeftId RightId : Type) : IdEmbedding RightId (Sum LeftId RightId) where
  toFun := Sum.inr
  injective := by intro left right same; cases same; rfl

theorem sum_disjoint {LeftId RightId : Type} (left : LeftId) (right : RightId) :
    (sumLeft LeftId RightId).toFun left ≠ (sumRight LeftId RightId).toFun right := by
  simp [sumLeft, sumRight]

def finLeft (leftSize rightSize : Nat) :
    IdEmbedding (Fin leftSize) (Fin (leftSize + rightSize)) where
  toFun := Fin.castAdd rightSize
  injective := by
    intro left right same
    apply Fin.ext
    have values := congrArg (fun value : Fin (leftSize + rightSize) => value.val) same
    exact values

def finRight (leftSize rightSize : Nat) :
    IdEmbedding (Fin rightSize) (Fin (leftSize + rightSize)) where
  toFun := Fin.natAdd leftSize
  injective := by
    intro left right same
    apply Fin.ext
    have values := congrArg Fin.val same
    exact Nat.add_left_cancel values

theorem fin_disjoint {leftSize rightSize : Nat}
    (left : Fin leftSize) (right : Fin rightSize) :
    (finLeft leftSize rightSize).toFun left ≠
      (finRight leftSize rightSize).toFun right := by
  intro same
  have values := congrArg Fin.val same
  simp [finLeft, finRight] at values
  omega

end IdEmbedding

namespace BuildHistory

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Injective remapping preserves the construction order as well as final target closure. -/
theorem mapId {Arch OldId NewId : Type} [TargetArch Arch]
    (embedding : IdEmbedding OldId NewId) {blocks : List (DirectBlock Arch OldId)}
    (history : BuildHistory blocks) :
    BuildHistory (blocks.map (DirectBlock.mapId embedding.toFun)) := by
  induction history with
  | empty => exact .empty
  | @intern blocks history block fresh closed ih =>
      rw [List.map_append]
      simp only [List.map_singleton]
      apply BuildHistory.intern ih (block.mapId embedding.toFun)
      · intro member
        rw [DirectBlock.mapId_entry_ids] at member
        rcases List.mem_map.mp member with ⟨oldId, oldMember, same⟩
        have same' : embedding.toFun oldId = embedding.toFun block.entry.id := by
          simpa only [DirectBlock.mapId_entry, mapEntryId_id] using same
        have equal : block.entry.id = oldId := (embedding.injective same').symm
        subst oldId
        exact fresh oldMember
      · intro state accepted
        have oldClosed := closed state accepted
        exact DirectTerminator.TargetsInterned.mapId embedding.toFun oldClosed
  | @append left right leftHistory rightHistory disjoint leftIH rightIH =>
      rw [List.map_append]
      apply BuildHistory.append leftIH rightIH
      intro leftMapped leftMember rightMapped rightMember
      rw [DirectBlock.mapId_entry_ids] at leftMember rightMember
      rcases List.mem_map.mp leftMember with ⟨leftId, leftIdMember, leftEqual⟩
      rcases List.mem_map.mp rightMember with ⟨rightId, rightIdMember, rightEqual⟩
      intro mappedEqual
      apply disjoint leftId leftIdMember rightId rightIdMember
      apply embedding.injective
      exact leftEqual.trans (mappedEqual.trans rightEqual.symm)

end BuildHistory

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Remap a complete builder through an injective identity embedding. Local block and edge proofs
    are reused; no symbolic CFG proof is regenerated. -/
def mapId {Arch OldId NewId : Type} [TargetArch Arch]
    (builder : Builder Arch OldId) (embedding : IdEmbedding OldId NewId) :
    Builder Arch NewId where
  blocks := builder.blocks.map (DirectBlock.mapId embedding.toFun)
  history := BuildHistory.mapId embedding builder.history
  uniqueIds := by
    rw [DirectBlock.mapId_entry_ids]
    exact embedding.map_nodup builder.uniqueIds
  targetsInterned := by
    intro mapped mappedMember state accepted
    rcases List.mem_map.mp mappedMember with ⟨source, sourceMember, rfl⟩
    have closed := builder.targetsInterned source sourceMember state accepted
    rcases bodyResult : source.body state accepted with ⟨ExitState, exit, terminator⟩
    rw [bodyResult] at closed
    simp only at closed
    simp only [DirectBlock.mapId]
    rw [bodyResult]
    simp only
    exact DirectTerminator.TargetsInterned.mapId embedding.toFun closed

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Compose two closed builders after their ID sets have been proved disjoint. Each side's target
    closure is weakened into the combined finite table. -/
def append {Arch BlockId : Type} [TargetArch Arch]
    (left right : Builder Arch BlockId)
    (disjoint : ∀ leftId ∈ left.blocks.map (·.entry.id),
      ∀ rightId ∈ right.blocks.map (·.entry.id), leftId ≠ rightId) :
    Builder Arch BlockId where
  blocks := left.blocks ++ right.blocks
  history := .append left.history right.history disjoint
  uniqueIds := by
    rw [List.map_append, List.nodup_append]
    exact ⟨left.uniqueIds, right.uniqueIds, disjoint⟩
  targetsInterned := by
    intro source sourceMember state accepted
    rw [List.map_append]
    rcases List.mem_append.mp sourceMember with inLeft | inRight
    · exact (left.targetsInterned source inLeft state accepted).weakenRight
    · exact (right.targetsInterned source inRight state accepted).weakenLeft

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Collision-free composition for independently scoped components. `Sum.inl` and `Sum.inr`
    preserve each nominal identity and make cross-component collisions impossible. -/
def sum {Arch LeftId RightId : Type} [TargetArch Arch]
    (left : Builder Arch LeftId) (right : Builder Arch RightId) :
    Builder Arch (Sum LeftId RightId) :=
  append (left.mapId (IdEmbedding.sumLeft LeftId RightId))
    (right.mapId (IdEmbedding.sumRight LeftId RightId)) (by
      intro leftMapped inLeft rightMapped inRight
      simp only [mapId] at inLeft inRight
      rw [DirectBlock.mapId_entry_ids] at inLeft inRight
      rcases List.mem_map.mp inLeft with ⟨leftId, _, leftEqual⟩
      rcases List.mem_map.mp inRight with ⟨rightId, _, rightEqual⟩
      subst leftMapped
      subst rightMapped
      exact IdEmbedding.sum_disjoint leftId rightId)

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Collision-free composition for generated finite scopes. Left IDs occupy `[0, leftSize)` and
    right IDs occupy `[leftSize, leftSize + rightSize)`. -/
def finAppend {Arch : Type} [TargetArch Arch] {leftSize rightSize : Nat}
    (left : Builder Arch (Fin leftSize)) (right : Builder Arch (Fin rightSize)) :
    Builder Arch (Fin (leftSize + rightSize)) :=
  append (left.mapId (IdEmbedding.finLeft leftSize rightSize))
    (right.mapId (IdEmbedding.finRight leftSize rightSize)) (by
      intro leftMapped inLeft rightMapped inRight
      simp only [mapId] at inLeft inRight
      rw [DirectBlock.mapId_entry_ids] at inLeft inRight
      rcases List.mem_map.mp inLeft with ⟨leftId, _, leftEqual⟩
      rcases List.mem_map.mp inRight with ⟨rightId, _, rightEqual⟩
      subst leftMapped
      subst rightMapped
      exact IdEmbedding.fin_disjoint leftId rightId)

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Extend the table with one fresh definition. Its direct targets must already be interned, making
    this first builder deliberately acyclic. `intern` packages the resulting reference. -/
private def extend {Arch BlockId : Type} [TargetArch Arch]
    (builder : Builder Arch BlockId) (block : DirectBlock Arch BlockId)
    (fresh : block.entry.id ∉ builder.blocks.map (·.entry.id))
    (closed : ∀ (state : ComposedState Arch block.entry.State)
      (accepted : block.entry.accepts state),
      let result := block.body state accepted
      result.2.2.TargetsInterned (builder.blocks.map DirectBlock.toBasicBlock)) :
    Builder Arch BlockId where
  blocks := builder.blocks ++ [block]
  history := .intern builder.history block fresh closed
  uniqueIds := by
    rw [List.map_append]
    simp only [List.map_singleton]
    rw [List.nodup_append]
    exact ⟨builder.uniqueIds, by simp, by simpa using fresh⟩
  targetsInterned := by
    intro source member state accepted
    rw [List.map_append]
    rcases List.mem_append.mp member with old | new
    · exact (builder.targetsInterned source old state accepted).weakenRight
    · simp only [List.mem_singleton] at new
      subst source
      exact (closed state accepted).weakenRight

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Result of interning one definition. The returned reference is already proved to resolve in the
    extended table, so it can be used as a later jump target or as the finalized graph entry. -/
structure InternResult (Arch : Type) [TargetArch Arch] (BlockId : Type)
    (block : DirectBlock Arch BlockId) where
  builder : Builder Arch BlockId
  ref : BlockRef Arch BlockId
  definition : ref.definition = block.toBasicBlock
  interned : ref.Interned (builder.blocks.map DirectBlock.toBasicBlock)

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Intern one block and return its typed reference. -/
def intern {Arch BlockId : Type} [TargetArch Arch]
    (builder : Builder Arch BlockId) (block : DirectBlock Arch BlockId)
    (fresh : block.entry.id ∉ builder.blocks.map (·.entry.id))
    (closed : ∀ (state : ComposedState Arch block.entry.State)
      (accepted : block.entry.accepts state),
      let result := block.body state accepted
      result.2.2.TargetsInterned (builder.blocks.map DirectBlock.toBasicBlock)) :
    InternResult Arch BlockId block := by
  let extended := builder.extend block fresh closed
  refine {
    builder := extended
    ref := BlockRef.ofBlock block.toBasicBlock
    definition := ?_
    interned := ?_
  }
  · rfl
  · apply List.mem_map.mpr
    refine ⟨block, ?_, rfl⟩
    simp [extended, extend]

/- REF: docs/MACRO_ASSEMBLER.md#next-control-flow-slice -/
/-- Finalize into the existing closed typed CFG. This is frontend proof production, not a competing
    execution or emission authority. -/
def finalize {Arch BlockId : Type} [TargetArch Arch]
    (builder : Builder Arch BlockId) (entry : BlockRef Arch BlockId)
    (entryInterned : entry.Interned (builder.blocks.map DirectBlock.toBasicBlock)) :
    TypedControlFlowGraph Arch BlockId where
  blocks := builder.blocks.map DirectBlock.toBasicBlock
  entry := entry.entry
  entryInGraph := ⟨entry.definition, entryInterned, rfl⟩
  uniqueIds := by
    rw [DirectBlock.map_toBasicBlock_entry_ids]
    exact builder.uniqueIds
  targetsInGraph := by
    intro compiled compiledMember state accepted
    rcases List.mem_map.mp compiledMember with ⟨source, sourceMember, rfl⟩
    have closed := builder.targetsInterned source sourceMember state accepted
    rcases bodyResult : source.body state accepted with ⟨ExitState, exit, terminator⟩
    rw [bodyResult] at closed
    simp only at closed
    simp only [DirectBlock.toBasicBlock]
    rw [bodyResult]
    simp only
    cases terminator with
    | jmp target edge targetExact =>
        exact ⟨target.definition, closed, targetExact.symm⟩
    | ret | sysExit | halt => trivial

end Builder

end Gasm.Core.CFGBuilder

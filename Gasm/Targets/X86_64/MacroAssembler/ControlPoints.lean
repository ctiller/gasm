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
import Gasm.Targets.X86_64.MacroAssembler

namespace Gasm.Targets.X86_64.MacroAssembler.ControlPoints

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Targets.X86_64

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Nominal identity for one marked instruction boundary. The reference retains the exact already
    interned block definition; the point ID is proof identity and never a rendered text label. -/
structure ControlPointRef (BlockId PointId : Type) where
  id : PointId
  target : BlockRef X86_64 BlockId

namespace ControlPointRef

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Remap block and point identities without changing the referenced definition's contract. -/
def mapIds {OldBlockId NewBlockId OldPointId NewPointId : Type}
    (blockMap : OldBlockId → NewBlockId) (pointMap : OldPointId → NewPointId)
    (ref : ControlPointRef OldBlockId OldPointId) :
    ControlPointRef NewBlockId NewPointId where
  id := pointMap ref.id
  target := ref.target.mapId blockMap

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem mapIds_id {OldBlockId NewBlockId OldPointId NewPointId : Type}
    (blockMap : OldBlockId → NewBlockId) (pointMap : OldPointId → NewPointId)
    (ref : ControlPointRef OldBlockId OldPointId) :
    (ref.mapIds blockMap pointMap).id = pointMap ref.id := rfl

end ControlPointRef

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- A marked point is an actual split of the immutable ordered instruction scope. A nonempty suffix
    makes it strictly earlier than the current end. Its target is an exact definition already
    interned by the acyclic CFG builder. -/
structure PointAt {BlockId PointId : Type} (builder : Builder X86_64 BlockId)
    (code : List X86_64Instr) where
  ref : ControlPointRef BlockId PointId
  before : List X86_64Instr
  after : List X86_64Instr
  decomposition : code = before ++ after
  strictlyEarlier : after ≠ []
  targetInterned : ref.target.Interned
    (builder.blocks.map DirectBlock.toBasicBlock)

namespace PointAt

/-- Number of instructions from this marked boundary to the current end of the scope. -/
/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def distance {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    {code : List X86_64Instr} (point : PointAt builder code (PointId := PointId)) : Nat :=
  point.after.length

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
theorem distance_pos {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    {code : List X86_64Instr} (point : PointAt builder code (PointId := PointId)) :
    0 < point.distance := by
  simp only [distance]
  have nonzero : point.after.length ≠ 0 := by
    simpa using point.strictlyEarlier
  omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
theorem distance_le_code_length {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    {code : List X86_64Instr} (point : PointAt builder code (PointId := PointId)) :
    point.distance ≤ code.length := by
  have lengths := congrArg List.length point.decomposition
  simp only [List.length_append] at lengths
  simp only [distance]
  omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Extend the current instruction stream. The point's nominal target is unchanged; its numeric
    authoring distance changes, which is why clients retain the resolved reference, not the Nat. -/
def appendCode {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    {code : List X86_64Instr} (point : PointAt builder code (PointId := PointId))
    (tail : List X86_64Instr) : PointAt builder (code ++ tail) (PointId := PointId) where
  ref := point.ref
  before := point.before
  after := point.after ++ tail
  decomposition := by simp [point.decomposition, List.append_assoc]
  strictlyEarlier := by
    intro empty
    have : point.after = [] := by
      simpa using congrArg (List.take point.after.length) empty
    exact point.strictlyEarlier this
  targetInterned := point.targetInterned

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem appendCode_distance {BlockId PointId : Type}
    {builder : Builder X86_64 BlockId} {code : List X86_64Instr}
    (point : PointAt builder code (PointId := PointId)) (tail : List X86_64Instr) :
    (point.appendCode tail).distance = point.distance + tail.length := by
  simp [appendCode, distance]

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem appendCode_ref_id {BlockId PointId : Type}
    {builder : Builder X86_64 BlockId} {code : List X86_64Instr}
    (point : PointAt builder code (PointId := PointId)) (tail : List X86_64Instr) :
    (point.appendCode tail).ref.id = point.ref.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Remap both nominal namespaces through injective embeddings. -/
def mapIds {OldBlockId NewBlockId OldPointId NewPointId : Type}
    {builder : Builder X86_64 OldBlockId} {code : List X86_64Instr}
    (blockMap : Builder.IdEmbedding OldBlockId NewBlockId)
    (pointMap : Builder.IdEmbedding OldPointId NewPointId)
    (point : PointAt builder code (PointId := OldPointId)) :
    PointAt (builder.mapId blockMap) code (PointId := NewPointId) where
  ref := point.ref.mapIds blockMap.toFun pointMap.toFun
  before := point.before
  after := point.after
  decomposition := point.decomposition
  strictlyEarlier := point.strictlyEarlier
  targetInterned := BlockRef.Interned.mapId blockMap.toFun point.targetInterned

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem mapIds_ref_id {OldBlockId NewBlockId OldPointId NewPointId : Type}
    {builder : Builder X86_64 OldBlockId} {code : List X86_64Instr}
    (blockMap : Builder.IdEmbedding OldBlockId NewBlockId)
    (pointMap : Builder.IdEmbedding OldPointId NewPointId)
    (point : PointAt builder code (PointId := OldPointId)) :
    (point.mapIds blockMap pointMap).ref.id = pointMap.toFun point.ref.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem mapIds_distance {OldBlockId NewBlockId OldPointId NewPointId : Type}
    {builder : Builder X86_64 OldBlockId} {code : List X86_64Instr}
    (blockMap : Builder.IdEmbedding OldBlockId NewBlockId)
    (pointMap : Builder.IdEmbedding OldPointId NewPointId)
    (point : PointAt builder code (PointId := OldPointId)) :
    (point.mapIds blockMap pointMap).distance = point.distance := rfl

end PointAt

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Immutable local authoring scope. Point identities and instruction distances are unique, so a
    successful numeric lookup selects one nominal exact-definition reference. -/
structure Scope (BlockId PointId : Type) (builder : Builder X86_64 BlockId) where
  code : List X86_64Instr
  points : List (PointAt builder code (PointId := PointId))
  uniquePointIds : (points.map (·.ref.id)).Nodup
  uniqueDistances : (points.map PointAt.distance).Nodup

namespace Scope

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def addEmbedding (amount : Nat) : Builder.IdEmbedding Nat Nat where
  toFun := fun value => value + amount
  injective := by intro left right same; exact Nat.add_right_cancel same

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def empty (BlockId PointId : Type) (builder : Builder X86_64 BlockId) :
    Scope BlockId PointId builder where
  code := []
  points := []
  uniquePointIds := by simp
  uniqueDistances := by simp

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Collision-free nominal remapping preserves the instruction stream and every structural point
    split. No numeric authoring query is rerun. -/
def mapIds {OldBlockId NewBlockId OldPointId NewPointId : Type}
    {builder : Builder X86_64 OldBlockId}
    (scope : Scope OldBlockId OldPointId builder)
    (blockMap : Builder.IdEmbedding OldBlockId NewBlockId)
    (pointMap : Builder.IdEmbedding OldPointId NewPointId) :
    Scope NewBlockId NewPointId (builder.mapId blockMap) where
  code := scope.code
  points := scope.points.map (·.mapIds blockMap pointMap)
  uniquePointIds := by
    have same :
        (scope.points.map (·.mapIds blockMap pointMap)).map (·.ref.id) =
          (scope.points.map (·.ref.id)).map pointMap.toFun := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact pointMap.map_nodup scope.uniquePointIds
  uniqueDistances := by
    have same :
        (scope.points.map (·.mapIds blockMap pointMap)).map PointAt.distance =
          scope.points.map PointAt.distance := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact scope.uniqueDistances

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Append instructions without introducing a new destination. Existing nominal references remain
    fixed while their disposable authoring distances shift by the appended instruction count. -/
def appendCode {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    (scope : Scope BlockId PointId builder) (tail : List X86_64Instr) :
    Scope BlockId PointId builder where
  code := scope.code ++ tail
  points := scope.points.map (·.appendCode tail)
  uniquePointIds := by
    have same :
        (scope.points.map (·.appendCode tail)).map (·.ref.id) =
          scope.points.map (·.ref.id) := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact scope.uniquePointIds
  uniqueDistances := by
    have same :
        (scope.points.map (·.appendCode tail)).map PointAt.distance =
          (scope.points.map PointAt.distance).map (fun value => value + tail.length) := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact (addEmbedding tail.length).map_nodup scope.uniqueDistances

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Mark the current instruction boundary with an exact already-interned block reference, then append
    a nonempty instruction suffix. This is the smart constructor that makes the new point genuinely
    earlier than the resulting current boundary. -/
def markThenAppend {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    (scope : Scope BlockId PointId builder) (ref : ControlPointRef BlockId PointId)
    (tail : List X86_64Instr) (tailNonempty : tail ≠ [])
    (freshPoint : ref.id ∉ scope.points.map (·.ref.id))
    (interned : ref.target.Interned (builder.blocks.map DirectBlock.toBasicBlock)) :
    Scope BlockId PointId builder := by
  let grown := scope.appendCode tail
  let marked : PointAt builder grown.code (PointId := PointId) := {
    ref := ref
    before := scope.code
    after := tail
    decomposition := rfl
    strictlyEarlier := tailNonempty
    targetInterned := interned
  }
  refine {
    code := grown.code
    points := grown.points ++ [marked]
    uniquePointIds := ?_
    uniqueDistances := ?_
  }
  · rw [List.map_append, List.nodup_append]
    refine ⟨grown.uniquePointIds, by simp, ?_⟩
    intro oldId oldMember newId newMember
    simp only [List.map_singleton, List.mem_singleton] at newMember
    subst newId
    have oldMember' : oldId ∈ scope.points.map (·.ref.id) := by
      simpa [grown, Scope.appendCode] using oldMember
    intro same
    subst oldId
    exact freshPoint oldMember'
  · rw [List.map_append, List.nodup_append]
    refine ⟨grown.uniqueDistances, by simp, ?_⟩
    intro oldDistance oldMember newDistance newMember
    simp only [List.map_singleton, List.mem_singleton] at newMember
    subst newDistance
    have expanded : oldDistance ∈
        (scope.points.map (·.appendCode tail)).map PointAt.distance := by
      simpa [grown, Scope.appendCode] using oldMember
    rw [List.map_map] at expanded
    rcases List.mem_map.mp expanded with ⟨oldPoint, _, same⟩
    simp only [Function.comp_apply, PointAt.appendCode_distance] at same
    have positive := oldPoint.distance_pos
    simp only [marked, PointAt.distance]
    omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def sumLeftPoint {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {left : Builder X86_64 LeftBlockId} {right : Builder X86_64 RightBlockId}
    {leftCode rightCode : List X86_64Instr}
    (point : PointAt left leftCode (PointId := LeftPointId)) :
    PointAt (Builder.sum left right) (leftCode ++ rightCode)
      (PointId := Sum LeftPointId RightPointId) where
  ref := point.ref.mapIds Sum.inl Sum.inl
  before := point.before
  after := point.after ++ rightCode
  decomposition := by simp [point.decomposition, List.append_assoc]
  strictlyEarlier := by
    intro empty
    have : point.after = [] := by
      simpa using congrArg (List.take point.after.length) empty
    exact point.strictlyEarlier this
  targetInterned := by
    have mapped :
        (point.ref.target.mapId (Sum.inl : LeftBlockId → Sum LeftBlockId RightBlockId)).Interned
          (((left.mapId (Builder.IdEmbedding.sumLeft LeftBlockId RightBlockId)).blocks).map
            DirectBlock.toBasicBlock) :=
      BlockRef.Interned.mapId (Sum.inl : LeftBlockId → Sum LeftBlockId RightBlockId)
        point.targetInterned
    change (point.ref.target.mapId (Sum.inl : LeftBlockId → Sum LeftBlockId RightBlockId)).Interned _
    simpa only [Builder.sum, Builder.append, List.map_append] using mapped.weakenRight

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def sumRightPoint {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {left : Builder X86_64 LeftBlockId} {right : Builder X86_64 RightBlockId}
    {leftCode rightCode : List X86_64Instr}
    (point : PointAt right rightCode (PointId := RightPointId)) :
    PointAt (Builder.sum left right) (leftCode ++ rightCode)
      (PointId := Sum LeftPointId RightPointId) where
  ref := point.ref.mapIds Sum.inr Sum.inr
  before := leftCode ++ point.before
  after := point.after
  decomposition := by simp [point.decomposition, List.append_assoc]
  strictlyEarlier := point.strictlyEarlier
  targetInterned := by
    have mapped :
        (point.ref.target.mapId (Sum.inr : RightBlockId → Sum LeftBlockId RightBlockId)).Interned
          (((right.mapId (Builder.IdEmbedding.sumRight LeftBlockId RightBlockId)).blocks).map
            DirectBlock.toBasicBlock) :=
      BlockRef.Interned.mapId (Sum.inr : RightBlockId → Sum LeftBlockId RightBlockId)
        point.targetInterned
    change (point.ref.target.mapId (Sum.inr : RightBlockId → Sum LeftBlockId RightBlockId)).Interned _
    simpa only [Builder.sum, Builder.append, List.map_append] using mapped.weakenLeft

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumLeftPoint_id
    {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {left : Builder X86_64 LeftBlockId} {right : Builder X86_64 RightBlockId}
    {leftCode rightCode : List X86_64Instr}
    (point : PointAt left leftCode (PointId := LeftPointId)) :
    (sumLeftPoint (right := right) (rightCode := rightCode)
      (RightPointId := RightPointId) point).ref.id = Sum.inl point.ref.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumRightPoint_id
    {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {left : Builder X86_64 LeftBlockId} {right : Builder X86_64 RightBlockId}
    {leftCode rightCode : List X86_64Instr}
    (point : PointAt right rightCode (PointId := RightPointId)) :
    (sumRightPoint (left := left) (leftCode := leftCode)
      (LeftPointId := LeftPointId) point).ref.id = Sum.inr point.ref.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumLeftPoint_distance
    {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {left : Builder X86_64 LeftBlockId} {right : Builder X86_64 RightBlockId}
    {leftCode rightCode : List X86_64Instr}
    (point : PointAt left leftCode (PointId := LeftPointId)) :
    (sumLeftPoint (right := right) (rightCode := rightCode)
      (RightPointId := RightPointId) point).distance =
      point.distance + rightCode.length := by
  simp [sumLeftPoint, PointAt.distance]

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumRightPoint_distance
    {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {left : Builder X86_64 LeftBlockId} {right : Builder X86_64 RightBlockId}
    {leftCode rightCode : List X86_64Instr}
    (point : PointAt right rightCode (PointId := RightPointId)) :
    (sumRightPoint (left := left) (leftCode := leftCode)
      (LeftPointId := LeftPointId) point).distance = point.distance := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Compose independent instruction/control-point scopes. `Sum` remaps both nominal namespaces
    without collision. Point splits are transported structurally into the concatenated instruction
    stream; previously resolved references need no numeric re-resolution. -/
def sum {LeftBlockId RightBlockId LeftPointId RightPointId : Type}
    {leftBuilder : Builder X86_64 LeftBlockId}
    {rightBuilder : Builder X86_64 RightBlockId}
    (left : Scope LeftBlockId LeftPointId leftBuilder)
    (right : Scope RightBlockId RightPointId rightBuilder) :
    Scope (Sum LeftBlockId RightBlockId) (Sum LeftPointId RightPointId)
      (Builder.sum leftBuilder rightBuilder) := by
  let leftPoints := left.points.map (sumLeftPoint (right := rightBuilder)
    (rightCode := right.code) (RightPointId := RightPointId))
  let rightPoints := right.points.map (sumRightPoint (left := leftBuilder)
    (leftCode := left.code) (LeftPointId := LeftPointId))
  refine {
    code := left.code ++ right.code
    points := leftPoints ++ rightPoints
    uniquePointIds := ?_
    uniqueDistances := ?_
  }
  · rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have mapped := (Builder.IdEmbedding.sumLeft LeftPointId RightPointId).map_nodup
          left.uniquePointIds
      rw [List.map_map] at mapped
      dsimp [leftPoints]
      rw [List.map_map]
      have functions :
          ((fun point => point.ref.id) ∘
            (sumLeftPoint (right := rightBuilder) (rightCode := right.code)
              (RightPointId := RightPointId))) =
          (Sum.inl ∘ fun point : PointAt leftBuilder left.code (PointId := LeftPointId) =>
            point.ref.id) := by
        funext point
        rfl
      rw [functions]
      exact mapped
    · have mapped := (Builder.IdEmbedding.sumRight LeftPointId RightPointId).map_nodup
          right.uniquePointIds
      rw [List.map_map] at mapped
      dsimp [rightPoints]
      rw [List.map_map]
      have functions :
          ((fun point => point.ref.id) ∘
            (sumRightPoint (left := leftBuilder) (leftCode := left.code)
              (LeftPointId := LeftPointId))) =
          (Sum.inr ∘ fun point : PointAt rightBuilder right.code (PointId := RightPointId) =>
            point.ref.id) := by
        funext point
        rfl
      rw [functions]
      exact mapped
    · intro leftId leftMember rightId rightMember
      simp only [leftPoints, rightPoints, List.map_map] at leftMember rightMember
      rcases List.mem_map.mp leftMember with ⟨leftPoint, _, rfl⟩
      rcases List.mem_map.mp rightMember with ⟨rightPoint, _, rfl⟩
      exact Builder.IdEmbedding.sum_disjoint leftPoint.ref.id rightPoint.ref.id
  · rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have shifted := (addEmbedding right.code.length).map_nodup left.uniqueDistances
      rw [List.map_map] at shifted
      dsimp [leftPoints]
      rw [List.map_map]
      have functions :
          (PointAt.distance ∘
            (sumLeftPoint (right := rightBuilder) (rightCode := right.code)
              (RightPointId := RightPointId))) =
          ((fun value => value + right.code.length) ∘
            (PointAt.distance : PointAt leftBuilder left.code (PointId := LeftPointId) → Nat)) := by
        funext point
        exact sumLeftPoint_distance point
      rw [functions]
      exact shifted
    · dsimp [rightPoints]
      rw [List.map_map]
      have functions :
          (PointAt.distance ∘
            (sumRightPoint (left := leftBuilder) (leftCode := left.code)
              (LeftPointId := LeftPointId))) =
          (PointAt.distance : PointAt rightBuilder right.code (PointId := RightPointId) → Nat) := by
        funext point
        exact sumRightPoint_distance point
      rw [functions]
      exact right.uniqueDistances
    · intro leftDistance leftMember rightDistance rightMember
      simp only [leftPoints, rightPoints, List.map_map] at leftMember rightMember
      rcases List.mem_map.mp leftMember with ⟨leftPoint, _, leftSame⟩
      rcases List.mem_map.mp rightMember with ⟨rightPoint, _, rightSame⟩
      simp only [Function.comp_apply, sumLeftPoint_distance] at leftSame
      simp only [Function.comp_apply, sumRightPoint_distance] at rightSame
      have leftPositive := leftPoint.distance_pos
      have rightBound := rightPoint.distance_le_code_length
      omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def findDistance {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    {code : List X86_64Instr} (distance : Nat) :
    List (PointAt builder code (PointId := PointId)) →
      Option (PointAt builder code (PointId := PointId))
  | [] => none
  | point :: rest =>
      if point.distance = distance then some point else findDistance distance rest

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private theorem findDistance_sound {BlockId PointId : Type}
    {builder : Builder X86_64 BlockId} {code : List X86_64Instr} {distance : Nat}
    {points : List (PointAt builder code (PointId := PointId))} {point}
    (found : findDistance distance points = some point) :
    point ∈ points ∧ point.distance = distance := by
  induction points with
  | nil => simp [findDistance] at found
  | cons head rest ih =>
      simp only [findDistance] at found
      split at found
      · rename_i same
        cases found
        exact ⟨by simp, same⟩
      · exact ⟨by simp [ih found |>.1], ih found |>.2⟩

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Proof-producing result of a numeric authoring lookup. The distance is only the query: all later
    authority comes from the returned nominal point, structural split, and exact interned target. -/
structure ResolvedBack {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    (scope : Scope BlockId PointId builder) (distance : Nat) where
  point : PointAt builder scope.code (PointId := PointId)
  pointInScope : point ∈ scope.points
  exactDistance : point.distance = distance

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
inductive ResolveError where
  | zeroDistance
  | unmarkedBoundary
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Resolve “back K instructions” once. Zero cannot denote the current boundary, and an unmarked
    instruction boundary cannot be promoted into a CFG destination. -/
def resolveBack {BlockId PointId : Type} {builder : Builder X86_64 BlockId}
    (scope : Scope BlockId PointId builder) (distance : Nat) :
    Except ResolveError (ResolvedBack scope distance) :=
  if distance = 0 then .error .zeroDistance
  else
    match found : findDistance distance scope.points with
    | none => .error .unmarkedBoundary
    | some point => .ok {
        point := point
        pointInScope := (findDistance_sound found).1
        exactDistance := (findDistance_sound found).2
      }

namespace ResolvedBack

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- An unresolved/current block ID that is fresh for the acyclic builder cannot be the selected
    target. This explicitly rules out using relative syntax to enter the current block or create a
    self loop in this slice. -/
theorem target_ne_fresh_current {BlockId PointId : Type}
    {builder : Builder X86_64 BlockId} {scope : Scope BlockId PointId builder}
    {distance : Nat} (resolved : ResolvedBack scope distance) {currentId : BlockId}
    (fresh : currentId ∉ builder.blocks.map (·.entry.id)) :
    resolved.point.ref.target.entry.id ≠ currentId := by
  intro same
  rcases List.mem_map.mp resolved.point.targetInterned with
    ⟨targetBlock, targetMember, definition⟩
  apply fresh
  apply List.mem_map.mpr
  refine ⟨targetBlock, targetMember, ?_⟩
  exact (congrArg (fun block => block.entry.id) definition).trans same

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Desugar a resolved relative target to the existing typed direct-JMP terminator. -/
def jmp {BlockId PointId S : Type} {builder : Builder X86_64 BlockId}
    {scope : Scope BlockId PointId builder} {distance : Nat}
    (resolved : ResolvedBack scope distance) {exit : ComposedState X86_64 S}
    (edge : BlockEdge (BlockId := BlockId) exit)
    (targetExact : edge.target = resolved.point.ref.target.entry) :
    DirectTerminator (BlockId := BlockId) exit :=
  .jmp resolved.point.ref.target edge targetExact

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Desugar a pair of resolved relative targets to the existing typed JCC terminator. No new edge
    or condition semantics are introduced. -/
def jcc {BlockId PointId S : Type} {builder : Builder X86_64 BlockId}
    {scope : Scope BlockId PointId builder} {trueDistance falseDistance : Nat}
    (condition : ConditionCode X86_64)
    (targetTrue : ResolvedBack scope trueDistance)
    (targetFalse : ResolvedBack scope falseDistance)
    {exit : ComposedState X86_64 S}
    (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine))
    (trueExact : edgeTrue.target = targetTrue.point.ref.target.entry)
    (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine))
    (falseExact : edgeFalse.target = targetFalse.point.ref.target.entry) :
    DirectTerminator (BlockId := BlockId) exit :=
  .jcc condition targetTrue.point.ref.target edgeTrue trueExact
    targetFalse.point.ref.target edgeFalse falseExact

end ResolvedBack

end Scope

end Gasm.Targets.X86_64.MacroAssembler.ControlPoints

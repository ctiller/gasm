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

import Gasm.Core.RecursiveCFGBuilder
import Gasm.Targets.X86_64.MacroAssembler

namespace Gasm.Targets.X86_64.MacroAssembler.ControlPoints

universe uItem uPoint vPoint uTarget vTarget wTarget

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Core.RecursiveCFGBuilder
open Gasm.Targets.X86_64

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- One nominal point in an immutable ordered item stream. The target is a concrete payload, never
    a forgeable relation. The split itself proves that the point is an item boundary. -/
structure OrderedPoint (Item : Type uItem) (PointId : Type uPoint) (Target : Type uTarget)
    (code : List Item) where
  id : PointId
  target : Target
  before : List Item
  after : List Item
  decomposition : code = before ++ after
  strictlyEarlier : after ≠ []

namespace OrderedPoint

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def distance {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget} {code : List Item}
    (point : OrderedPoint Item PointId Target code) : Nat :=
  point.after.length

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
theorem distance_pos {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    {code : List Item}
    (point : OrderedPoint Item PointId Target code) : 0 < point.distance := by
  simp only [distance]
  have nonzero : point.after.length ≠ 0 := by simpa using point.strictlyEarlier
  omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
theorem distance_le_code_length {Item : Type uItem} {PointId : Type uPoint}
    {Target : Type uTarget} {code : List Item}
    (point : OrderedPoint Item PointId Target code) : point.distance ≤ code.length := by
  have lengths := congrArg List.length point.decomposition
  simp only [List.length_append] at lengths
  simp only [distance]
  omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Map nominal point identity and its concrete target payload without changing its boundary. -/
def map {Item : Type uItem} {OldPointId : Type uPoint} {NewPointId : Type vPoint}
    {OldTarget : Type uTarget} {NewTarget : Type vTarget} {code : List Item}
    (pointMap : OldPointId → NewPointId) (targetMap : OldTarget → NewTarget)
    (point : OrderedPoint Item OldPointId OldTarget code) :
    OrderedPoint Item NewPointId NewTarget code where
  id := pointMap point.id
  target := targetMap point.target
  before := point.before
  after := point.after
  decomposition := point.decomposition
  strictlyEarlier := point.strictlyEarlier

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def appendItems {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    {code : List Item}
    (point : OrderedPoint Item PointId Target code) (tail : List Item) :
    OrderedPoint Item PointId Target (code ++ tail) where
  id := point.id
  target := point.target
  before := point.before
  after := point.after ++ tail
  decomposition := by simp [point.decomposition, List.append_assoc]
  strictlyEarlier := by
    intro empty
    have : point.after = [] := by
      simpa using congrArg (List.take point.after.length) empty
    exact point.strictlyEarlier this

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem map_id {Item : Type uItem} {OldPointId : Type uPoint}
    {NewPointId : Type vPoint} {OldTarget : Type uTarget} {NewTarget : Type vTarget}
    {code : List Item} (pointMap : OldPointId → NewPointId)
    (targetMap : OldTarget → NewTarget) (point : OrderedPoint Item OldPointId OldTarget code) :
    (point.map pointMap targetMap).id = pointMap point.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem map_distance {Item : Type uItem} {OldPointId : Type uPoint}
    {NewPointId : Type vPoint} {OldTarget : Type uTarget} {NewTarget : Type vTarget}
    {code : List Item} (pointMap : OldPointId → NewPointId)
    (targetMap : OldTarget → NewTarget) (point : OrderedPoint Item OldPointId OldTarget code) :
    (point.map pointMap targetMap).distance = point.distance := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem appendItems_id {Item : Type uItem} {PointId : Type uPoint}
    {Target : Type uTarget} {code : List Item}
    (point : OrderedPoint Item PointId Target code) (tail : List Item) :
    (point.appendItems tail).id = point.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] theorem appendItems_distance {Item : Type uItem} {PointId : Type uPoint}
    {Target : Type uTarget} {code : List Item}
    (point : OrderedPoint Item PointId Target code) (tail : List Item) :
    (point.appendItems tail).distance = point.distance + tail.length := by
  simp [appendItems, distance]

end OrderedPoint

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- A universe-polymorphic injective remapping for generic point identities. Block-identity
    remapping continues to use the core builder's nominal embedding. -/
structure PointIdEmbedding (OldId : Type uPoint) (NewId : Type vPoint) where
  toFun : OldId → NewId
  injective : Function.Injective toFun

namespace PointIdEmbedding

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def refl (Id : Type uPoint) : PointIdEmbedding Id Id where
  toFun := id
  injective := Function.injective_id

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
theorem map_nodup {OldId : Type uPoint} {NewId : Type vPoint}
    (embedding : PointIdEmbedding OldId NewId) {values : List OldId}
    (unique : values.Nodup) : (values.map embedding.toFun).Nodup := by
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

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def sumLeft (LeftId : Type uPoint) (RightId : Type vPoint) :
    PointIdEmbedding LeftId (Sum LeftId RightId) where
  toFun := Sum.inl
  injective := by intro left right same; cases same; rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def sumRight (LeftId : Type uPoint) (RightId : Type vPoint) :
    PointIdEmbedding RightId (Sum LeftId RightId) where
  toFun := Sum.inr
  injective := by intro left right same; cases same; rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
theorem sum_disjoint {LeftId : Type uPoint} {RightId : Type vPoint}
    (left : LeftId) (right : RightId) :
    (sumLeft LeftId RightId).toFun left ≠ (sumRight LeftId RightId).toFun right := by
  simp [sumLeft, sumRight]

end PointIdEmbedding

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Generic ordered-point kernel shared by acyclic exact-block and recursive declaration payloads. -/
structure Scope (Item : Type uItem) (PointId : Type uPoint) (Target : Type uTarget) where
  code : List Item
  points : List (OrderedPoint Item PointId Target code)
  uniquePointIds : (points.map (·.id)).Nodup
  uniqueDistances : (points.map OrderedPoint.distance).Nodup

namespace Scope

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def addEmbedding (amount : Nat) : PointIdEmbedding Nat Nat where
  toFun := fun value => value + amount
  injective := by intro left right same; exact Nat.add_right_cancel same

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def empty (Item : Type uItem) (PointId : Type uPoint) (Target : Type uTarget) :
    Scope Item PointId Target where
  code := []
  points := []
  uniquePointIds := by simp
  uniqueDistances := by simp

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Remap IDs injectively and map the concrete payload once. -/
def map {Item : Type uItem} {OldPointId : Type uPoint} {NewPointId : Type vPoint}
    {OldTarget : Type uTarget} {NewTarget : Type vTarget}
    (scope : Scope Item OldPointId OldTarget)
    (pointMap : PointIdEmbedding OldPointId NewPointId)
    (targetMap : OldTarget → NewTarget) : Scope Item NewPointId NewTarget where
  code := scope.code
  points := scope.points.map (·.map pointMap.toFun targetMap)
  uniquePointIds := by
    have same : (scope.points.map (·.map pointMap.toFun targetMap)).map (·.id) =
        (scope.points.map (·.id)).map pointMap.toFun := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact pointMap.map_nodup scope.uniquePointIds
  uniqueDistances := by
    have same : (scope.points.map (·.map pointMap.toFun targetMap)).map
        OrderedPoint.distance = scope.points.map OrderedPoint.distance := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact scope.uniqueDistances

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Remap only nominal point identity, retaining every concrete target payload. -/
def mapPointId {Item : Type uItem} {OldPointId : Type uPoint} {NewPointId : Type vPoint}
    {Target : Type uTarget} (scope : Scope Item OldPointId Target)
    (pointMap : PointIdEmbedding OldPointId NewPointId) : Scope Item NewPointId Target :=
  scope.map pointMap id

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Remap only concrete targets, retaining the nominal point namespace. -/
def mapTarget {Item : Type uItem} {PointId : Type uPoint}
    {OldTarget : Type uTarget} {NewTarget : Type vTarget}
    (scope : Scope Item PointId OldTarget) (targetMap : OldTarget → NewTarget) :
    Scope Item PointId NewTarget :=
  scope.map (PointIdEmbedding.refl PointId) targetMap

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def appendItems {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    (scope : Scope Item PointId Target)
    (tail : List Item) : Scope Item PointId Target where
  code := scope.code ++ tail
  points := scope.points.map (·.appendItems tail)
  uniquePointIds := by
    have same : (scope.points.map (·.appendItems tail)).map (·.id) =
        scope.points.map (·.id) := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact scope.uniquePointIds
  uniqueDistances := by
    have same : (scope.points.map (·.appendItems tail)).map OrderedPoint.distance =
        (scope.points.map OrderedPoint.distance).map (fun value => value + tail.length) := by
      induction scope.points with
      | nil => rfl
      | cons point rest ih => simp [ih]
    rw [same]
    exact (addEmbedding tail.length).map_nodup scope.uniqueDistances

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Mark the current boundary with a concrete target, then append a nonempty suffix. -/
def markThenAppend {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    (scope : Scope Item PointId Target)
    (pointId : PointId) (target : Target) (tail : List Item) (tailNonempty : tail ≠ [])
    (freshPoint : pointId ∉ scope.points.map (·.id)) : Scope Item PointId Target := by
  let grown := scope.appendItems tail
  let marked : OrderedPoint Item PointId Target grown.code := {
    id := pointId
    target := target
    before := scope.code
    after := tail
    decomposition := rfl
    strictlyEarlier := tailNonempty
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
    have oldMember' : oldId ∈ scope.points.map (·.id) := by
      simpa [grown, Scope.appendItems] using oldMember
    intro same
    subst oldId
    exact freshPoint oldMember'
  · rw [List.map_append, List.nodup_append]
    refine ⟨grown.uniqueDistances, by simp, ?_⟩
    intro oldDistance oldMember newDistance newMember
    simp only [List.map_singleton, List.mem_singleton] at newMember
    subst newDistance
    have expanded : oldDistance ∈
        (scope.points.map (·.appendItems tail)).map OrderedPoint.distance := by
      simpa [grown, Scope.appendItems] using oldMember
    rw [List.map_map] at expanded
    rcases List.mem_map.mp expanded with ⟨oldPoint, _, same⟩
    simp only [Function.comp_apply, OrderedPoint.appendItems_distance] at same
    have positive := oldPoint.distance_pos
    simp only [marked, OrderedPoint.distance]
    omega

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def sumLeftPoint {Item : Type uItem} {LeftPointId : Type uPoint}
    {RightPointId : Type vPoint} {LeftTarget : Type uTarget} {Target : Type wTarget}
    {leftCode rightCode : List Item} (leftTarget : LeftTarget → Target)
    (point : OrderedPoint Item LeftPointId LeftTarget leftCode) :
    OrderedPoint Item (Sum LeftPointId RightPointId) Target (leftCode ++ rightCode) where
  id := .inl point.id
  target := leftTarget point.target
  before := point.before
  after := point.after ++ rightCode
  decomposition := by simp [point.decomposition, List.append_assoc]
  strictlyEarlier := by
    intro empty
    have : point.after = [] := by
      simpa using congrArg (List.take point.after.length) empty
    exact point.strictlyEarlier this

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private def sumRightPoint {Item : Type uItem} {LeftPointId : Type uPoint}
    {RightPointId : Type vPoint} {RightTarget : Type vTarget} {Target : Type wTarget}
    {leftCode rightCode : List Item} (rightTarget : RightTarget → Target)
    (point : OrderedPoint Item RightPointId RightTarget rightCode) :
    OrderedPoint Item (Sum LeftPointId RightPointId) Target (leftCode ++ rightCode) where
  id := .inr point.id
  target := rightTarget point.target
  before := leftCode ++ point.before
  after := point.after
  decomposition := by simp [point.decomposition, List.append_assoc]
  strictlyEarlier := point.strictlyEarlier

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumLeftPoint_id {Item : Type uItem} {LeftPointId : Type uPoint}
    {RightPointId : Type vPoint} {LeftTarget : Type uTarget} {Target : Type wTarget}
    {leftCode rightCode : List Item} (leftTarget : LeftTarget → Target)
    (point : OrderedPoint Item LeftPointId LeftTarget leftCode) :
    (sumLeftPoint (rightCode := rightCode) (RightPointId := RightPointId)
      leftTarget point).id = Sum.inl point.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumRightPoint_id {Item : Type uItem} {LeftPointId : Type uPoint}
    {RightPointId : Type vPoint} {RightTarget : Type vTarget} {Target : Type wTarget}
    {leftCode rightCode : List Item} (rightTarget : RightTarget → Target)
    (point : OrderedPoint Item RightPointId RightTarget rightCode) :
    (sumRightPoint (leftCode := leftCode) (LeftPointId := LeftPointId)
      rightTarget point).id = Sum.inr point.id := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumLeftPoint_distance {Item : Type uItem}
    {LeftPointId : Type uPoint} {RightPointId : Type vPoint}
    {LeftTarget : Type uTarget} {Target : Type wTarget} {leftCode rightCode : List Item}
    (leftTarget : LeftTarget → Target)
    (point : OrderedPoint Item LeftPointId LeftTarget leftCode) :
    (sumLeftPoint (rightCode := rightCode) (RightPointId := RightPointId)
      leftTarget point).distance = point.distance + rightCode.length := by
  simp [sumLeftPoint, OrderedPoint.distance]

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
@[simp] private theorem sumRightPoint_distance {Item : Type uItem}
    {LeftPointId : Type uPoint} {RightPointId : Type vPoint}
    {RightTarget : Type vTarget} {Target : Type wTarget} {leftCode rightCode : List Item}
    (rightTarget : RightTarget → Target)
    (point : OrderedPoint Item RightPointId RightTarget rightCode) :
    (sumRightPoint (leftCode := leftCode) (LeftPointId := LeftPointId)
      rightTarget point).distance = point.distance := rfl

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Collision-free component composition. Payload mappings are explicit functions; no relation is
    introduced as proof authority. -/
def sum {Item : Type uItem} {LeftPointId : Type uPoint} {RightPointId : Type vPoint}
    {LeftTarget : Type uTarget} {RightTarget : Type vTarget} {Target : Type wTarget}
    (left : Scope Item LeftPointId LeftTarget) (right : Scope Item RightPointId RightTarget)
    (leftTarget : LeftTarget → Target) (rightTarget : RightTarget → Target) :
    Scope Item (Sum LeftPointId RightPointId) Target := by
  let leftPoints := left.points.map (sumLeftPoint (rightCode := right.code)
    (RightPointId := RightPointId) leftTarget)
  let rightPoints := right.points.map (sumRightPoint (leftCode := left.code)
    (LeftPointId := LeftPointId) rightTarget)
  refine {
    code := left.code ++ right.code
    points := leftPoints ++ rightPoints
    uniquePointIds := ?_
    uniqueDistances := ?_
  }
  · rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have mapped := (PointIdEmbedding.sumLeft LeftPointId RightPointId).map_nodup
          left.uniquePointIds
      rw [List.map_map] at mapped
      dsimp [leftPoints]
      rw [List.map_map]
      have functions :
          ((fun point => point.id) ∘
            (sumLeftPoint (rightCode := right.code) (RightPointId := RightPointId)
              leftTarget)) =
          (Sum.inl ∘ fun point : OrderedPoint Item LeftPointId LeftTarget left.code =>
            point.id) := by
        funext point
        rfl
      rw [functions]
      exact mapped
    · have mapped := (PointIdEmbedding.sumRight LeftPointId RightPointId).map_nodup
          right.uniquePointIds
      rw [List.map_map] at mapped
      dsimp [rightPoints]
      rw [List.map_map]
      have functions :
          ((fun point => point.id) ∘
            (sumRightPoint (leftCode := left.code) (LeftPointId := LeftPointId)
              rightTarget)) =
          (Sum.inr ∘ fun point : OrderedPoint Item RightPointId RightTarget right.code =>
            point.id) := by
        funext point
        rfl
      rw [functions]
      exact mapped
    · intro leftId leftMember rightId rightMember
      simp only [leftPoints, rightPoints, List.map_map] at leftMember rightMember
      rcases List.mem_map.mp leftMember with ⟨leftPoint, _, rfl⟩
      rcases List.mem_map.mp rightMember with ⟨rightPoint, _, rfl⟩
      exact PointIdEmbedding.sum_disjoint leftPoint.id rightPoint.id
  · rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · have shifted := (addEmbedding right.code.length).map_nodup left.uniqueDistances
      rw [List.map_map] at shifted
      dsimp [leftPoints]
      rw [List.map_map]
      have functions :
          (OrderedPoint.distance ∘
            (sumLeftPoint (rightCode := right.code) (RightPointId := RightPointId)
              leftTarget)) =
          ((fun value => value + right.code.length) ∘
            (OrderedPoint.distance :
              OrderedPoint Item LeftPointId LeftTarget left.code → Nat)) := by
        funext point
        exact sumLeftPoint_distance leftTarget point
      rw [functions]
      exact shifted
    · dsimp [rightPoints]
      rw [List.map_map]
      have functions :
          (OrderedPoint.distance ∘
            (sumRightPoint (leftCode := left.code) (LeftPointId := LeftPointId)
              rightTarget)) =
          (OrderedPoint.distance :
            OrderedPoint Item RightPointId RightTarget right.code → Nat) := by
        funext point
        exact sumRightPoint_distance rightTarget point
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
private def findDistance {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    {code : List Item} (distance : Nat) :
    List (OrderedPoint Item PointId Target code) → Option (OrderedPoint Item PointId Target code)
  | [] => none
  | point :: rest =>
      if point.distance = distance then some point else findDistance distance rest

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
private theorem findDistance_sound {Item : Type uItem} {PointId : Type uPoint}
    {Target : Type uTarget} {code : List Item}
    {distance : Nat} {points : List (OrderedPoint Item PointId Target code)} {point}
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
/-- Dependent lookup result: later consumers use this stored point and target, not the query Nat. -/
structure ResolvedBack {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    (scope : Scope Item PointId Target)
    (distance : Nat) where
  point : OrderedPoint Item PointId Target scope.code
  pointInScope : point ∈ scope.points
  exactDistance : point.distance = distance

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
inductive ResolveError where
  | zeroDistance
  | unmarkedBoundary
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def resolveBack {Item : Type uItem} {PointId : Type uPoint} {Target : Type uTarget}
    (scope : Scope Item PointId Target)
    (distance : Nat) : Except ResolveError (ResolvedBack scope distance) :=
  if distance = 0 then .error .zeroDistance
  else
    match found : findDistance distance scope.points with
    | none => .error .unmarkedBoundary
    | some point => .ok {
        point := point
        pointInScope := (findDistance_sound found).1
        exactDistance := (findDistance_sound found).2
      }

end Scope

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- Acyclic payload makes exact definition membership intrinsic. -/
structure InternedBlockTarget (BlockId : Type) (builder : Builder X86_64 BlockId) where
  ref : BlockRef X86_64 BlockId
  interned : ref.Interned (builder.blocks.map DirectBlock.toBasicBlock)

namespace Acyclic

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def mapTarget {OldId NewId : Type} {builder : Builder X86_64 OldId}
    (embedding : Builder.IdEmbedding OldId NewId) (target : InternedBlockTarget OldId builder) :
    InternedBlockTarget NewId (builder.mapId embedding) where
  ref := target.ref.mapId embedding.toFun
  interned := BlockRef.Interned.mapId embedding.toFun target.interned

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def sumLeftTarget {LeftId RightId : Type} {left : Builder X86_64 LeftId}
    {right : Builder X86_64 RightId} (target : InternedBlockTarget LeftId left) :
    InternedBlockTarget (Sum LeftId RightId) (Builder.sum left right) where
  ref := target.ref.mapId (Builder.IdEmbedding.sumLeft LeftId RightId).toFun
  interned := by
    have mapped := BlockRef.Interned.mapId
      (Builder.IdEmbedding.sumLeft LeftId RightId).toFun target.interned
    simpa only [Builder.sum, Builder.append, Builder.mapId, List.map_append] using
      mapped.weakenRight

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def sumRightTarget {LeftId RightId : Type} {left : Builder X86_64 LeftId}
    {right : Builder X86_64 RightId} (target : InternedBlockTarget RightId right) :
    InternedBlockTarget (Sum LeftId RightId) (Builder.sum left right) where
  ref := target.ref.mapId (Builder.IdEmbedding.sumRight LeftId RightId).toFun
  interned := by
    have mapped := BlockRef.Interned.mapId
      (Builder.IdEmbedding.sumRight LeftId RightId).toFun target.interned
    simpa only [Builder.sum, Builder.append, Builder.mapId, List.map_append] using
      mapped.weakenLeft

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
/-- A block ID fresh for the acyclic builder cannot be selected by a resolved point. Thus this
    binding cannot use relative syntax to create a self edge into the block currently being added. -/
theorem target_ne_fresh_current {BlockId PointId : Type}
    {builder : Builder X86_64 BlockId}
    {scope : Scope X86_64Instr PointId (InternedBlockTarget BlockId builder)} {distance : Nat}
    (resolved : Scope.ResolvedBack scope distance) {currentId : BlockId}
    (fresh : currentId ∉ builder.blocks.map (·.entry.id)) :
    resolved.point.target.ref.entry.id ≠ currentId := by
  intro same
  rcases List.mem_map.mp resolved.point.target.interned with
    ⟨targetBlock, targetMember, definition⟩
  apply fresh
  apply List.mem_map.mpr
  refine ⟨targetBlock, targetMember, ?_⟩
  exact (congrArg (fun block => block.entry.id) definition).trans same

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def jmp {BlockId PointId S : Type} {builder : Builder X86_64 BlockId}
    {scope : Scope X86_64Instr PointId (InternedBlockTarget BlockId builder)} {distance : Nat}
    (resolved : Scope.ResolvedBack scope distance) {exit : ComposedState X86_64 S}
    (edge : BlockEdge (BlockId := BlockId) exit)
    (targetExact : edge.target = resolved.point.target.ref.entry) :
    DirectTerminator (BlockId := BlockId) exit :=
  .jmp resolved.point.target.ref edge targetExact

/- REF: docs/MACRO_ASSEMBLER.md#instruction-relative-authoring -/
def jcc {BlockId PointId S : Type} {builder : Builder X86_64 BlockId}
    {scope : Scope X86_64Instr PointId (InternedBlockTarget BlockId builder)}
    {trueDistance falseDistance : Nat} (condition : ConditionCode X86_64)
    (targetTrue : Scope.ResolvedBack scope trueDistance)
    (targetFalse : Scope.ResolvedBack scope falseDistance)
    {exit : ComposedState X86_64 S}
    (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine))
    (trueExact : edgeTrue.target = targetTrue.point.target.ref.entry)
    (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine))
    (falseExact : edgeFalse.target = targetFalse.point.target.ref.entry) :
    DirectTerminator (BlockId := BlockId) exit :=
  .jcc condition targetTrue.point.target.ref edgeTrue trueExact
    targetFalse.point.target.ref edgeFalse falseExact

end Acyclic

namespace Recursive

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def mapTarget {BlockId NewId Index : Type} {declarations :
    RecursiveCFGBuilder.Scope X86_64 BlockId Index}
    (embedding : Builder.IdEmbedding BlockId NewId) (target : DeclRef declarations) :
    DeclRef (declarations.mapBlockId embedding) :=
  target.mapBlockId embedding

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def jmp {BlockId Index PointId S : Type}
    {declarations : RecursiveCFGBuilder.Scope X86_64 BlockId Index}
    {scope : Scope X86_64Instr PointId (DeclRef declarations)} {distance : Nat}
    (resolved : Scope.ResolvedBack scope distance) {exit : ComposedState X86_64 S}
    (edge : BlockEdge (BlockId := BlockId) exit)
    (targetExact : edge.target = resolved.point.target.entry) :
    RecursiveTerminator declarations exit :=
  .jmp resolved.point.target edge targetExact

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
def jcc {BlockId Index PointId S : Type}
    {declarations : RecursiveCFGBuilder.Scope X86_64 BlockId Index}
    {scope : Scope X86_64Instr PointId (DeclRef declarations)}
    {trueDistance falseDistance : Nat} (condition : ConditionCode X86_64)
    (targetTrue : Scope.ResolvedBack scope trueDistance)
    (targetFalse : Scope.ResolvedBack scope falseDistance)
    {exit : ComposedState X86_64 S}
    (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine))
    (trueExact : edgeTrue.target = targetTrue.point.target.entry)
    (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine))
    (falseExact : edgeFalse.target = targetFalse.point.target.entry) :
    RecursiveTerminator declarations exit :=
  .jcc condition targetTrue.point.target edgeTrue trueExact
    targetFalse.point.target edgeFalse falseExact

/- REF: docs/MACRO_ASSEMBLER.md#finite-recursive-cfg-authoring -/
/-- Compose recursive authoring scopes by remapping PointId, BlockId, and declaration Index through
    `Sum`. Cross-scope references remain unconstructible. -/
def sumScopes {LeftId RightId LeftIndex RightIndex LeftPointId RightPointId : Type}
    {leftDeclarations : RecursiveCFGBuilder.Scope X86_64 LeftId LeftIndex}
    {rightDeclarations : RecursiveCFGBuilder.Scope X86_64 RightId RightIndex}
    (left : Scope X86_64Instr LeftPointId (DeclRef leftDeclarations))
    (right : Scope X86_64Instr RightPointId (DeclRef rightDeclarations)) :
    Scope X86_64Instr (Sum LeftPointId RightPointId)
      (DeclRef (leftDeclarations.sum rightDeclarations)) :=
  left.sum right DeclRef.sumLeft DeclRef.sumRight

end Recursive

end Gasm.Targets.X86_64.MacroAssembler.ControlPoints

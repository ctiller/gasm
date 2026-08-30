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

namespace Gasm.Compiler.TypedCFG

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Core.RecursiveCFGBuilder

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Finite compiler source scope. Contracts are declared before bodies, and nominal block identity
    is injective over the source indices. -/
structure SourceScope (Arch BlockId : Type) [TargetArch Arch] (size : Nat) where
  entry : Fin size → BlockEntry Arch BlockId
  idInjective : Function.Injective (fun index => (entry index).id)

namespace SourceScope

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- The exact recursive declaration table generated from a compiler source scope. -/
def declarations {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch BlockId size) :
    RecursiveCFGBuilder.Scope Arch BlockId (Fin size) :=
  RecursiveCFGBuilder.Scope.fin size scope.entry scope.idInjective

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Injectively rename nominal block identities without changing indices or entry contracts. -/
def mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch OldId size) (embedding : Builder.IdEmbedding OldId NewId) :
    SourceScope Arch NewId size where
  entry := fun index => mapEntryId embedding.toFun (scope.entry index)
  idInjective := by
    intro left right same
    apply scope.idInjective
    apply embedding.injective
    exact same

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
@[simp] theorem declarations_entry {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch BlockId size) (index : Fin size) :
    scope.declarations.entry index = scope.entry index := rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
theorem declarations_mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch OldId size) (embedding : Builder.IdEmbedding OldId NewId) :
    (scope.mapBlockId embedding).declarations = scope.declarations.mapBlockId embedding := by
  rfl

end SourceScope

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- A typed source reference is a finite source index whose entry is fixed by one exact scope. -/
structure SourceRef {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch BlockId size) where
  index : Fin size

namespace SourceRef

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def entry {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (ref : SourceRef scope) :
    BlockEntry Arch BlockId :=
  scope.entry ref.index

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Lower a source ref to the same-index declaration ref; no textual or numeric target is resolved. -/
def toDeclRef {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (ref : SourceRef scope) :
    DeclRef scope.declarations :=
  ⟨ref.index⟩

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
@[simp] theorem toDeclRef_index {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (ref : SourceRef scope) :
    ref.toDeclRef.index = ref.index := rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
@[simp] theorem toDeclRef_entry {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (ref : SourceRef scope) :
    ref.toDeclRef.entry = ref.entry := rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch OldId size} (embedding : Builder.IdEmbedding OldId NewId)
    (ref : SourceRef scope) : SourceRef (scope.mapBlockId embedding) :=
  ⟨ref.index⟩

end SourceRef

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Source terminators retain the existing typed edge contracts. Only the target representation is
    compiler-facing; lowering selects the corresponding recursive constructor structurally. -/
inductive SourceTerminator {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch BlockId size) {S : Type} (exit : ComposedState Arch S) where
  | jmp (target : SourceRef scope) (edge : BlockEdge (BlockId := BlockId) exit)
      (targetExact : edge.target = target.entry) : SourceTerminator scope exit
  | jcc (condition : ConditionCode Arch)
      (targetTrue : SourceRef scope)
      (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
        (condition.holds exit.machine))
      (trueExact : edgeTrue.target = targetTrue.entry)
      (targetFalse : SourceRef scope)
      (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
        (¬ condition.holds exit.machine))
      (falseExact : edgeFalse.target = targetFalse.entry) : SourceTerminator scope exit
  | ret (exportedObligations : List ObligationToken) (bytesToPop : UInt16 := 0)
      (stackClean : exit.stackDepth = 0)
      (obligationsMatch : exit.obligations = exportedObligations)
      (callee : CalleeDiscipline Arch exit) : SourceTerminator scope exit
  | sysExit (exitCode : UInt8)
      (droppable : ∀ obligation ∈ exit.obligations, obligation.isDroppableOnExit) :
      SourceTerminator scope exit
  | halt (droppable : ∀ obligation ∈ exit.obligations, obligation.isDroppableOnExit) :
      SourceTerminator scope exit

namespace SourceTerminator

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Proof-facing constructor summary. JCC stores true then false source indices explicitly. -/
inductive Shape (Index : Type) where
  | jmp (target : Index)
  | jcc (targetTrue targetFalse : Index)
  | ret
  | sysExit
  | halt
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def shape {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} {S : Type} {exit : ComposedState Arch S} :
    SourceTerminator scope exit → Shape (Fin size)
  | .jmp target _ _ => .jmp target.index
  | .jcc _ targetTrue _ _ targetFalse _ _ => .jcc targetTrue.index targetFalse.index
  | .ret .. => .ret
  | .sysExit .. => .sysExit
  | .halt .. => .halt

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def recursiveShape {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} {S : Type} {exit : ComposedState Arch S} :
    RecursiveTerminator scope.declarations exit → Shape (Fin size)
  | .jmp target _ _ => .jmp target.index
  | .jcc _ targetTrue _ _ targetFalse _ _ => .jcc targetTrue.index targetFalse.index
  | .ret .. => .ret
  | .sysExit .. => .sysExit
  | .halt .. => .halt

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Structural lowering to the existing recursive terminator family. -/
def lower {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} {S : Type} {exit : ComposedState Arch S} :
    SourceTerminator scope exit → RecursiveTerminator scope.declarations exit
  | .jmp target edge targetExact => .jmp target.toDeclRef edge targetExact
  | .jcc condition targetTrue edgeTrue trueExact targetFalse edgeFalse falseExact =>
      .jcc condition targetTrue.toDeclRef edgeTrue trueExact
        targetFalse.toDeclRef edgeFalse falseExact
  | .ret obligations bytesToPop stackClean obligationsMatch callee =>
      .ret obligations bytesToPop stackClean obligationsMatch callee
  | .sysExit exitCode droppable => .sysExit exitCode droppable
  | .halt droppable => .halt droppable

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Constructor choice and every target index are unchanged by lowering; in particular the first
    JCC index remains true and the second remains false. -/
@[simp] theorem recursiveShape_lower {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} {S : Type} {exit : ComposedState Arch S}
    (terminator : SourceTerminator scope exit) :
    recursiveShape terminator.lower = terminator.shape := by
  cases terminator <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
private def mapEdge {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {exit : ComposedState Arch S}
    (edge : BlockEdge (BlockId := OldId) exit) : BlockEdge (BlockId := NewId) exit where
  target := mapEntryId map edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
private def mapConditionalEdge {Arch OldId NewId : Type} [TargetArch Arch] {S : Type}
    (map : OldId → NewId) {exit : ComposedState Arch S} {enabled : Prop}
    (edge : ConditionalBlockEdge (BlockId := OldId) exit enabled) :
    ConditionalBlockEdge (BlockId := NewId) exit enabled where
  target := mapEntryId map edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch OldId size} (embedding : Builder.IdEmbedding OldId NewId)
    {S : Type} {exit : ComposedState Arch S} :
    SourceTerminator scope exit → SourceTerminator (scope.mapBlockId embedding) exit
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

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Lowering preserves constructor selection, target indices, and JCC true/false orientation. -/
theorem lower_mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch OldId size} (embedding : Builder.IdEmbedding OldId NewId)
    {S : Type} {exit : ComposedState Arch S} (terminator : SourceTerminator scope exit) :
    (terminator.mapBlockId embedding).lower = terminator.lower.mapBlockId embedding := by
  cases terminator <;> rfl

end SourceTerminator

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- One already-lowered logical body plan. It carries typed state transition and terminator data,
    but makes no instruction, execution, byte, or artifact claim. -/
structure BlockPlan {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch BlockId size) (index : Fin size) where
  body : (state : ComposedState Arch (scope.entry index).State) →
    (scope.entry index).accepts state →
    Σ (ExitState : Type), Σ (exit : ComposedState Arch ExitState), SourceTerminator scope exit

namespace BlockPlan

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch OldId size} {index : Fin size}
    (plan : BlockPlan scope index) (embedding : Builder.IdEmbedding OldId NewId) :
    BlockPlan (scope.mapBlockId embedding) index where
  body := fun state accepted =>
    let result := plan.body state accepted
    ⟨result.1, result.2.1, result.2.2.mapBlockId embedding⟩

end BlockPlan

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Total finite source block table. Totality gives exactly one body plan for every declaration. -/
structure ProgramPlan {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    (scope : SourceScope Arch BlockId size) where
  block : (index : Fin size) → BlockPlan scope index

namespace ProgramPlan

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
def mapBlockId {Arch OldId NewId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch OldId size} (plan : ProgramPlan scope)
    (embedding : Builder.IdEmbedding OldId NewId) :
    ProgramPlan (scope.mapBlockId embedding) where
  block := fun index => (plan.block index).mapBlockId embedding

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Total structural lowering into the sole recursive CFG definition table. -/
def lowerDefinitions {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope) :
    Definitions scope.declarations where
  body := fun index state accepted =>
    let result := (plan.block index).body state accepted
    ⟨result.1, result.2.1, result.2.2.lower⟩

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Each source declaration maps to its same-index generated recursive definition. -/
theorem lowerDefinitions_body {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope) (index : Fin size)
    (state : ComposedState Arch (scope.entry index).State)
    (accepted : (scope.entry index).accepts state) :
    (plan.lowerDefinitions.body index state accepted) =
      let result := (plan.block index).body state accepted
      ⟨result.1, result.2.1, result.2.2.lower⟩ := rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- The generated block is exactly the source block plan with only its terminator structurally
    lowered. This is the per-block differential-proof handoff. -/
def loweredBlock {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope) (index : Fin size) :
    BasicBlock Arch BlockId where
  entry := scope.entry index
  body := fun state accepted =>
    let result := (plan.block index).body state accepted
    ⟨result.1, result.2.1, result.2.2.lower.toCpu⟩

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
@[simp] theorem loweredBlock_entry {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope) (index : Fin size) :
    (plan.loweredBlock index).entry = scope.entry index := rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
theorem lowerDefinitions_block {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope) (index : Fin size) :
    plan.lowerDefinitions.block index = plan.loweredBlock index := by
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Seal through the existing recursive builder; no alternate graph representation is produced. -/
def lower {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope)
    (entry : SourceRef scope) : Definitions.Sealed plan.lowerDefinitions :=
  Definitions.sealDefinitions plan.lowerDefinitions entry.toDeclRef

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Every sealed exact-definition reference points to the same-index lowered source block. -/
theorem lower_ref_exact {Arch BlockId : Type} [TargetArch Arch] {size : Nat}
    {scope : SourceScope Arch BlockId size} (plan : ProgramPlan scope)
    (entry : SourceRef scope) (index : Fin size) :
    ((plan.lower entry).ref index).definition = plan.loweredBlock index := by
  exact (plan.lower entry).refExact index |>.trans (plan.lowerDefinitions_block index)

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- The complete recursive definition table is unchanged whether nominal IDs are remapped before or
    after structural lowering. -/
theorem lowerDefinitions_mapBlockId {Arch OldId NewId : Type} [TargetArch Arch]
    {size : Nat} {scope : SourceScope Arch OldId size} (plan : ProgramPlan scope)
    (embedding : Builder.IdEmbedding OldId NewId) :
    plan.lowerDefinitions.mapBlockId embedding =
      (plan.mapBlockId embedding).lowerDefinitions := by
  cases plan with
  | mk block =>
      change Definitions.mk _ = Definitions.mk _
      congr 1
      funext index state accepted
      simp only [lowerDefinitions, ProgramPlan.mapBlockId, BlockPlan.mapBlockId]
      rcases result : (block index).body state accepted with
        ⟨ExitState, exit, terminator⟩
      rw [terminator.lower_mapBlockId embedding]
      rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-control-flow-compiler-frontend -/
/-- Lowering commutes with injective nominal BlockId remapping at every generated block. -/
theorem lowerDefinitions_mapBlockId_block {Arch OldId NewId : Type} [TargetArch Arch]
    {size : Nat} {scope : SourceScope Arch OldId size} (plan : ProgramPlan scope)
    (embedding : Builder.IdEmbedding OldId NewId) (index : Fin size) :
    mapBasicBlockId embedding.toFun (plan.lowerDefinitions.block index) =
      ((plan.mapBlockId embedding).lowerDefinitions.block index) := by
  simp only [Definitions.block, lowerDefinitions, ProgramPlan.mapBlockId, BlockPlan.mapBlockId,
    mapBasicBlockId]
  congr
  funext state accepted
  rcases result : (plan.block index).body state accepted with
    ⟨ExitState, exit, terminator⟩
  cases terminator <;> rfl

end ProgramPlan

end Gasm.Compiler.TypedCFG

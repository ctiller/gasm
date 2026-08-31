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

import Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry
import Gasm.Compiler.Word.StructuredCFG

namespace Gasm.Compiler.Word.StructuredConditionMicrosoftX64CFG

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Compiler.Word
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG
open Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry
open Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-branch-blocks -/
/-- Lift the exact local comparison result into the same API typestate and ghost world. Only the
    physical x86 state changes; all authority, obligations, clocks, history and stack depth are
    preserved definitionally. -/
def afterCondition (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) : ComposedState X86_64 State :=
  { state with machine := runLocalSteps lowered.instructions state.machine }

@[simp] theorem afterCondition_machine (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).machine = runLocalSteps lowered.instructions state.machine := rfl

@[simp] theorem afterCondition_stackDepth (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).stackDepth = state.stackDepth := rfl

@[simp] theorem afterCondition_api (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).api = state.api := rfl

@[simp] theorem afterCondition_perms (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).perms = state.perms := rfl

@[simp] theorem afterCondition_obligations (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).obligations = state.obligations := rfl

@[simp] theorem afterCondition_causalClock (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).causalClock = state.causalClock := rfl

@[simp] theorem afterCondition_eventHistory (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    (afterCondition lowered state).eventHistory = state.eventHistory := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-branch-blocks -/
theorem afterCondition_ghostFrame (lowered : LoweredCondition source)
    (state : ComposedState X86_64 State) :
    ConservativeGhostFrame state (afterCondition lowered state) where
  sameState := rfl
  stackDepth := rfl
  api := rfl
  permissions := rfl
  obligations := rfl
  causalClock := rfl
  eventHistory := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-branch-blocks -/
/-- The target/world premises for one exact branch block. Both static successors are supplied, but
    each destination entry contract is demanded only under its own selected predicate. The
    compiler does not synthesize these edges from portable syntax. -/
structure Successors {BlockId : Type} {source : Structured.Expr InputContext .bool}
    (lowered : LoweredCondition source) (entry : BlockEntry X86_64 BlockId)
    (targetTrue targetFalse : DirectBlock X86_64 BlockId) where
  trueEdge : ∀ (state : ComposedState X86_64 entry.State) (_accepted : entry.accepts state),
    ConditionalBlockEdge (BlockId := BlockId) (afterCondition lowered state)
      ((Condition.conditionCode lowered.kind).holds (afterCondition lowered state).machine)
  trueExact : ∀ state accepted,
    (trueEdge state accepted).target = targetTrue.entry
  falseEdge : ∀ (state : ComposedState X86_64 entry.State) (_accepted : entry.accepts state),
    ConditionalBlockEdge (BlockId := BlockId) (afterCondition lowered state)
      (¬(Condition.conditionCode lowered.kind).holds (afterCondition lowered state).machine)
  falseExact : ∀ state accepted,
    (falseEdge state accepted).target = targetFalse.entry

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-branch-blocks -/
/-- Exact logical block generated from one lowered comparison and caller-owned typed successors.
    Its instruction body is retained separately by `lowered`; native JCC encoding and layout remain
    target-linker obligations. -/
def block {BlockId : Type} {source : Structured.Expr InputContext .bool}
    (lowered : LoweredCondition source) (entry : BlockEntry X86_64 BlockId)
    (targetTrue targetFalse : DirectBlock X86_64 BlockId)
    (successors : Successors lowered entry targetTrue targetFalse) :
    DirectBlock X86_64 BlockId where
  entry := entry
  body := fun state accepted =>
    ⟨entry.State, afterCondition lowered state,
      .jccToBlocks (Condition.conditionCode lowered.kind)
        targetTrue.toBasicBlock (successors.trueEdge state accepted)
        (successors.trueExact state accepted)
        targetFalse.toBasicBlock (successors.falseEdge state accepted)
        (successors.falseExact state accepted)⟩

@[simp] theorem block_entry {BlockId : Type} {source : Structured.Expr InputContext .bool}
    (lowered : LoweredCondition source) (entry : BlockEntry X86_64 BlockId)
    (targetTrue targetFalse : DirectBlock X86_64 BlockId)
    (successors : Successors lowered entry targetTrue targetFalse) :
    (block lowered entry targetTrue targetFalse successors).entry = entry := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-branch-blocks -/
/-- The generated block retains both exact definitions and agrees with the portable condition for
    every entry whose four input registers denote the supplied source arguments. -/
def realizes {BlockId : Type} {source : Structured.Expr InputContext .bool}
    (lowered : LoweredCondition source) (entry : BlockEntry X86_64 BlockId)
    (targetTrue targetFalse : DirectBlock X86_64 BlockId)
    (successors : Successors lowered entry targetTrue targetFalse) :
    RealizesCondition
      (Evidence := PUnit)
      (block lowered entry targetTrue targetFalse successors)
      source targetTrue targetFalse where
  evidence := PUnit.unit
  entryRelation := fun args state => argsOfState state.machine = args
  targetsExact := by
    intro state accepted
    exact ⟨rfl, rfl⟩
  conditionAgrees := by
    intro args state accepted argsExact
    change
      (Condition.conditionCode lowered.kind).holds (afterCondition lowered state).machine ↔
        source.eval (InputContext.env args) = true
    rw [Condition.conditionCode_holds]
    change
      lowered.kind.holds (runLocalSteps lowered.instructions state.machine) ↔
        source.eval (InputContext.env args) = true
    rw [lowered.semanticAgreement state.machine]
    rw [argsExact]

end Gasm.Compiler.Word.StructuredConditionMicrosoftX64CFG

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

import Lean
import Gasm.Core.Arch
import Gasm.Core.State
import Gasm.Core.BlockM

namespace Gasm.Core

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Target register model parameterized by architecture and bit width. -/
structure Register (Arch : Type) (width : Nat) where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- A target-owned branch condition together with its meaning on machine state.
    Naming a condition without this predicate is insufficient for typed edges. -/
structure ConditionCode (Arch : Type) [TargetArch Arch] where
  name : String
  holds : TargetArch.MachineState Arch → Prop

/- REF: docs/STACK_DISCIPLINE.md#2-multi-abi-calling-conventions-stack-restoration-laws -/
/-- Current minimal callee stack-clean predicate.
It contains no register-preservation or external-boundary/link certificate by itself. -/
structure CalleeDiscipline (Arch : Type) [TargetArch Arch] {S : Type} (s : ComposedState Arch S) : Prop where
  stack_clean : s.stackDepth = 0

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- The contract owned by a basic-block entry. `id` is nominal proof identity, independent of any
    human-readable linker/debug name. `State` is erased typestate; `accepts` is the complete entry
    property demanded from every predecessor. -/
structure BlockEntry (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  State : Type
  id : BlockId
  expectedDepth : Nat
  accepts : ComposedState Arch State → Prop

namespace BlockEntry

/-- Transport a target state across equality of complete dependent entry
    contracts. -/
def transportState {Arch BlockId : Type} [TargetArch Arch]
    {left right : BlockEntry Arch BlockId}
    (same : left = right) (state : ComposedState Arch right.State) :
    ComposedState Arch left.State := by
  cases same
  exact state

theorem transport_accepts {Arch BlockId : Type} [TargetArch Arch]
    {left right : BlockEntry Arch BlockId} (same : left = right)
    {state : ComposedState Arch right.State} (accepted : right.accepts state) :
    left.accepts (transportState same state) := by
  cases same
  exact accepted

end BlockEntry

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- A jump changes control location but cannot manufacture authority.  The
    target may refine the erased API typestate, while the concrete state and
    framed ghost resources are preserved exactly across the edge. -/
structure JumpFramePreserved {Arch : Type} [TargetArch Arch]
    {Source Target : Type}
    (source : ComposedState Arch Source) (target : ComposedState Arch Target) : Prop where
  machine : target.machine = source.machine
  stackDepth : target.stackDepth = source.stackDepth
  permissions : target.perms = source.perms
  obligations : target.obligations = source.obligations
  causalClock : target.causalClock = source.causalClock
  eventHistory : target.eventHistory = source.eventHistory

namespace JumpFramePreserved

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- Frame preservation is reflexive, so a block may refine only its entry
    predicate without paying for an artificial state rewrite. -/
theorem refl {Arch : Type} [TargetArch Arch] {State : Type}
    (state : ComposedState Arch State) : JumpFramePreserved state state where
  machine := rfl
  stackDepth := rfl
  permissions := rfl
  obligations := rfl
  causalClock := rfl
  eventHistory := rfl

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- The frame law used by CFG composition: adjacent ghost-world transfers
    compose without reopening either block's local proof. -/
theorem trans {Arch : Type} [TargetArch Arch] {A B C : Type}
    {a : ComposedState Arch A} {b : ComposedState Arch B} {c : ComposedState Arch C}
    (ab : JumpFramePreserved a b) (bc : JumpFramePreserved b c) :
    JumpFramePreserved a c where
  machine := bc.machine.trans ab.machine
  stackDepth := bc.stackDepth.trans ab.stackDepth
  permissions := bc.permissions.trans ab.permissions
  obligations := bc.obligations.trans ab.obligations
  causalClock := bc.causalClock.trans ab.causalClock
  eventHistory := bc.eventHistory.trans ab.eventHistory

end JumpFramePreserved

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- Evidence for one direct control-flow edge. -/
structure BlockEdge {Arch BlockId : Type} [TargetArch Arch] {Source : Type}
    (source : ComposedState Arch Source) where
  target : BlockEntry Arch BlockId
  targetState : ComposedState Arch target.State
  framePreserved : JumpFramePreserved source targetState
  depthEstablished : target.expectedDepth = targetState.stackDepth
  entryEstablished : target.accepts targetState

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- Evidence for a conditional successor.  Only the selected edge must establish
    its target, avoiding an artificial obligation to prove mutually exclusive
    path refinements simultaneously. -/
structure ConditionalBlockEdge {Arch BlockId : Type} [TargetArch Arch] {Source : Type}
    (source : ComposedState Arch Source) (enabled : Prop) where
  target : BlockEntry Arch BlockId
  targetState : ComposedState Arch target.State
  framePreserved : JumpFramePreserved source targetState
  depthEstablished : target.expectedDepth = targetState.stackDepth
  entryEstablished : enabled → target.accepts targetState

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- An indirect jump is an ordinary typed edge plus target-owned resolution
    into a finite, duplicate-free candidate set.  The final artifact connection
    must prove that `decodeTarget` is the semantics of the emitted indirect
    branch operand; this record proves the local closed-world dispatch fact. -/
structure IndirectBlockEdge {Arch BlockId : Type} [TargetArch Arch] {Source TargetId : Type}
    (source : ComposedState Arch Source) where
  decodeTarget : TargetArch.MachineState Arch → TargetId
  candidates : List (TargetId × BlockEntry Arch BlockId)
  uniqueTargetIds : (candidates.map Prod.fst).Nodup
  edge : BlockEdge (BlockId := BlockId) source
  resolved : ∃ candidate ∈ candidates,
    candidate.1 = decodeTarget source.machine ∧ candidate.2 = edge.target

namespace BlockEdge

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- General edge-composition law. Constructing the second edge already demands
    the first target's entry contract, while the result exposes only the final
    target and the transitively preserved frame. -/
def trans {Arch BlockId : Type} [TargetArch Arch] {Source : Type}
    {source : ComposedState Arch Source}
    (first : BlockEdge (BlockId := BlockId) source)
    (second : BlockEdge (BlockId := BlockId) first.targetState) :
    BlockEdge (BlockId := BlockId) source where
  target := second.target
  targetState := second.targetState
  framePreserved := first.framePreserved.trans second.framePreserved
  depthEstablished := second.depthEstablished
  entryEstablished := second.entryEstablished

end BlockEdge

namespace ConditionalBlockEdge

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- Once target-owned condition semantics selects an edge, it becomes an
    ordinary typed edge and participates in the same composition theorem. -/
def activate {Arch BlockId : Type} [TargetArch Arch] {Source : Type}
    {source : ComposedState Arch Source} {enabled : Prop}
    (edge : ConditionalBlockEdge (BlockId := BlockId) source enabled) (selected : enabled) :
    BlockEdge (BlockId := BlockId) source where
  target := edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished selected

end ConditionalBlockEdge

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Architecture-defined control-flow terminator family indexed over the terminal state. -/
inductive CpuTerminator (Arch : Type) [TargetArch Arch] (BlockId : Type)
    {S : Type} (s_exit : ComposedState Arch S) where
  | jmp   (edge : BlockEdge (BlockId := BlockId) s_exit) : CpuTerminator Arch BlockId s_exit
  | jmpIndirect {TargetId : Type}
      (edge : IndirectBlockEdge (BlockId := BlockId) (TargetId := TargetId) s_exit) :
      CpuTerminator Arch BlockId s_exit
  | jcc   (cond : ConditionCode Arch)
          (targetTrue : ConditionalBlockEdge (BlockId := BlockId) s_exit (cond.holds s_exit.machine))
          (targetFalse : ConditionalBlockEdge (BlockId := BlockId) s_exit (¬ cond.holds s_exit.machine)) :
          CpuTerminator Arch BlockId s_exit
  | ret   (exportedObligations : List ObligationToken) (bytesToPop : UInt16 := 0)
          (h_zero      : s_exit.stackDepth = 0)
          (h_match     : s_exit.obligations = exportedObligations)
          (h_callee    : CalleeDiscipline Arch s_exit) : CpuTerminator Arch BlockId s_exit
  | sysExit (exitCode  : UInt8)
            (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) :
            CpuTerminator Arch BlockId s_exit
  | halt    (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) :
      CpuTerminator Arch BlockId s_exit

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Single-entry basic block whose body is callable only with its typed entry
    contract established. -/
structure BasicBlock (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  entry : BlockEntry Arch BlockId
  body : (state : ComposedState Arch entry.State) → entry.accepts state →
    Σ (ExitState : Type), Σ (exit : ComposedState Arch ExitState),
      CpuTerminator Arch BlockId exit

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- A finite typed CFG. Nominal IDs have unique definitions, and closure is proved against the
    actual terminator returned by every block body, so a control-flow edge cannot name an entry
    contract that the graph did not publish. -/
structure TypedControlFlowGraph (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  blocks : List (BasicBlock Arch BlockId)
  entry : BlockEntry Arch BlockId
  entryInGraph : ∃ block ∈ blocks, block.entry = entry
  uniqueIds : (blocks.map (·.entry.id)).Nodup
  targetsInGraph : ∀ block ∈ blocks,
    ∀ (state : ComposedState Arch block.entry.State) (accepted : block.entry.accepts state),
      let result := block.body state accepted
      match result.2.2 with
      | .jmp edge => ∃ target ∈ blocks, target.entry = edge.target
      | .jmpIndirect edge =>
          (∃ target ∈ blocks, target.entry = edge.edge.target) ∧
          ∀ candidate ∈ edge.candidates,
            ∃ target ∈ blocks, target.entry = candidate.2
      | .jcc _ targetTrue targetFalse =>
          (∃ target ∈ blocks, target.entry = targetTrue.target) ∧
          ∃ target ∈ blocks, target.entry = targetFalse.target
      | .ret .. | .sysExit .. | .halt .. => True

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- A control point packages exactly the evidence a block call consumes.  It is
    the common assume/guarantee boundary for function entries and jump targets. -/
structure BlockControlPoint (Arch : Type) [TargetArch Arch] (BlockId : Type) where
  block : BasicBlock Arch BlockId
  state : ComposedState Arch block.entry.State
  accepted : block.entry.accepts state

namespace TypedControlFlowGraph

/-- Membership of a typed control point in a graph is membership of its complete entry contract,
    not equality of a rendered linker/debug name. -/
def Contains {Arch BlockId : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch BlockId)
    (point : BlockControlPoint Arch BlockId) : Prop :=
  point.block ∈ graph.blocks

/-- Selection of exactly one successor from a terminator.  Conditional proof
    burden follows the branch that is actually enabled; the unselected target
    contributes no path-local obligation. -/
inductive SelectedEdge {Arch BlockId : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} :
    CpuTerminator Arch BlockId exit → BlockEdge (BlockId := BlockId) exit → Prop where
  | direct (edge : BlockEdge (BlockId := BlockId) exit) : SelectedEdge (.jmp edge) edge
  | indirect {TargetId : Type}
      (edge : IndirectBlockEdge (BlockId := BlockId) (TargetId := TargetId) exit) :
      SelectedEdge (.jmpIndirect edge) edge.edge
  | branchTrue (cond : ConditionCode Arch)
      (targetTrue : ConditionalBlockEdge (BlockId := BlockId) exit (cond.holds exit.machine))
      (targetFalse : ConditionalBlockEdge (BlockId := BlockId) exit (¬ cond.holds exit.machine))
      (selected : cond.holds exit.machine) :
      SelectedEdge (.jcc cond targetTrue targetFalse) (targetTrue.activate selected)
  | branchFalse (cond : ConditionCode Arch)
      (targetTrue : ConditionalBlockEdge (BlockId := BlockId) exit (cond.holds exit.machine))
      (targetFalse : ConditionalBlockEdge (BlockId := BlockId) exit (¬ cond.holds exit.machine))
      (selected : ¬ cond.holds exit.machine) :
      SelectedEdge (.jcc cond targetTrue targetFalse) (targetFalse.activate selected)

/-- Reindex a proved edge target by the exact block entry published in the graph. Equality is over
    the complete dependent contract, including its nominal ID. -/
def targetPoint {Arch BlockId : Type} [TargetArch Arch] {Source : Type}
    {source : ComposedState Arch Source} (edge : BlockEdge (BlockId := BlockId) source)
    (targetBlock : BasicBlock Arch BlockId) (sameEntry : targetBlock.entry = edge.target) :
    BlockControlPoint Arch BlockId :=
  ⟨targetBlock,
    BlockEntry.transportState sameEntry edge.targetState,
    BlockEntry.transport_accepts sameEntry edge.entryEstablished⟩

/-- One selected jump.  The successor already carries the destination's entry
    proof; the relation cannot represent an unchecked transfer. -/
inductive Step {Arch BlockId : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch BlockId) :
    BlockControlPoint Arch BlockId → BlockControlPoint Arch BlockId → Prop where
  | jump {source : BlockControlPoint Arch BlockId} {ExitState : Type}
      {exit : ComposedState Arch ExitState} {terminator : CpuTerminator Arch BlockId exit}
      (sourceInGraph : graph.Contains source)
      (bodyResult : source.block.body source.state source.accepted =
        ⟨ExitState, exit, terminator⟩)
      (edge : BlockEdge (BlockId := BlockId) exit) (selected : SelectedEdge terminator edge)
      (targetBlock : BasicBlock Arch BlockId) (targetInGraph : targetBlock ∈ graph.blocks)
      (sameEntry : targetBlock.entry = edge.target) :
      Step graph source (targetPoint edge targetBlock sameEntry)

/-- Graph closure discharges successor lookup once for all clients.  A caller
    selecting a branch supplies only the body equation and branch fact; it does
    not re-prove membership of that target at every use site. -/
theorem selected_target_in_graph {Arch BlockId : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch BlockId} {source : BlockControlPoint Arch BlockId}
    {ExitState : Type} {exit : ComposedState Arch ExitState}
    {terminator : CpuTerminator Arch BlockId exit}
    {edge : BlockEdge (BlockId := BlockId) exit}
    (sourceInGraph : graph.Contains source)
    (bodyResult : source.block.body source.state source.accepted =
      ⟨ExitState, exit, terminator⟩)
    (selected : SelectedEdge terminator edge) :
    ∃ target ∈ graph.blocks, target.entry = edge.target := by
  have closed := graph.targetsInGraph source.block sourceInGraph source.state source.accepted
  rw [bodyResult] at closed
  cases selected with
  | direct => exact closed
  | indirect => exact closed.1
  | branchTrue => exact closed.1
  | branchFalse => exact closed.2

/-- Proof-economical step constructor: target lookup is derived from the one
    graph-closure proof and the selected terminator edge. -/
theorem Step.fromBody {Arch BlockId : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch BlockId} {source : BlockControlPoint Arch BlockId}
    {ExitState : Type} {exit : ComposedState Arch ExitState}
    {terminator : CpuTerminator Arch BlockId exit}
    {edge : BlockEdge (BlockId := BlockId) exit}
    (sourceInGraph : graph.Contains source)
    (bodyResult : source.block.body source.state source.accepted =
      ⟨ExitState, exit, terminator⟩)
    (selected : SelectedEdge terminator edge) :
    ∃ target, Step graph source target := by
  rcases selected_target_in_graph sourceInGraph bodyResult selected with
    ⟨targetBlock, targetInGraph, sameEntry⟩
  exact ⟨targetPoint edge targetBlock sameEntry,
    .jump sourceInGraph bodyResult edge selected targetBlock targetInGraph sameEntry⟩

/-- Reflexive-transitive typed reachability.  Induction over this relation is
    the reusable whole-CFG proof rule: each block proves its contract once and
    each predecessor pays only for the selected target's precondition. -/
inductive Reachable {Arch BlockId : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch BlockId) :
    BlockControlPoint Arch BlockId → BlockControlPoint Arch BlockId → Prop where
  | refl (point) : Reachable graph point point
  | tail {start middle finish}
      (path : Reachable graph start middle) (step : Step graph middle finish) :
      Reachable graph start finish

theorem step_preserves_membership {Arch BlockId : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch BlockId}
    {source target : BlockControlPoint Arch BlockId}
    (step : Step graph source target) : graph.Contains target := by
  cases step with
  | jump _ _ _ _ _ targetInGraph _ => exact targetInGraph

theorem reachable_preserves_membership {Arch BlockId : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch BlockId}
    {start finish : BlockControlPoint Arch BlockId}
    (startInGraph : graph.Contains start) (path : Reachable graph start finish) :
    graph.Contains finish := by
  induction path with
  | refl => exact startInGraph
  | tail _ step _ => exact step_preserves_membership step

/-- A property factored at typed control-flow boundaries.  The preservation
    proof is demanded once per selected edge shape, never once per complete
    path through the routine. -/
structure Invariant {Arch BlockId : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch BlockId) where
  holds : BlockControlPoint Arch BlockId → Prop
  preserved : ∀ {source target}, Step graph source target →
    holds source → holds target

theorem Invariant.alongReachable {Arch BlockId : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch BlockId} (invariant : Invariant graph)
    {start finish : BlockControlPoint Arch BlockId}
    (initial : invariant.holds start) (path : Reachable graph start finish) :
    invariant.holds finish := by
  induction path with
  | refl => exact initial
  | tail _ step ih => exact invariant.preserved step ih

theorem reachable_trans {Arch BlockId : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch BlockId}
    {a b c : BlockControlPoint Arch BlockId}
    (ab : Reachable graph a b) (bc : Reachable graph b c) : Reachable graph a c := by
  induction bc with
  | refl => exact ab
  | tail _ step ih => exact .tail ih step

end TypedControlFlowGraph

end Gasm.Core

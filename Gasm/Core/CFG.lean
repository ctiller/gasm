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
/-- The contract owned by a basic-block entry.  `State` is erased typestate;
    `accepts` is the complete entry property demanded from every predecessor. -/
structure BlockEntry (Arch : Type) [TargetArch Arch] where
  State : Type
  label : String
  expectedDepth : Nat
  accepts : ComposedState Arch State → Prop

namespace BlockEntry

/-- Transport a target state across equality of complete dependent entry
    contracts. -/
def transportState {Arch : Type} [TargetArch Arch] {left right : BlockEntry Arch}
    (same : left = right) (state : ComposedState Arch right.State) :
    ComposedState Arch left.State := by
  cases same
  exact state

theorem transport_accepts {Arch : Type} [TargetArch Arch]
    {left right : BlockEntry Arch} (same : left = right)
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
structure BlockEdge {Arch : Type} [TargetArch Arch] {Source : Type}
    (source : ComposedState Arch Source) where
  target : BlockEntry Arch
  targetState : ComposedState Arch target.State
  framePreserved : JumpFramePreserved source targetState
  depthEstablished : target.expectedDepth = targetState.stackDepth
  entryEstablished : target.accepts targetState

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- Evidence for a conditional successor.  Only the selected edge must establish
    its target, avoiding an artificial obligation to prove mutually exclusive
    path refinements simultaneously. -/
structure ConditionalBlockEdge {Arch : Type} [TargetArch Arch] {Source : Type}
    (source : ComposedState Arch Source) (enabled : Prop) where
  target : BlockEntry Arch
  targetState : ComposedState Arch target.State
  framePreserved : JumpFramePreserved source targetState
  depthEstablished : target.expectedDepth = targetState.stackDepth
  entryEstablished : enabled → target.accepts targetState

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- An indirect jump is an ordinary typed edge plus target-owned resolution
    into a finite, duplicate-free candidate set.  The final artifact connection
    must prove that `decodeTarget` is the semantics of the emitted indirect
    branch operand; this record proves the local closed-world dispatch fact. -/
structure IndirectBlockEdge {Arch : Type} [TargetArch Arch] {Source TargetId : Type}
    (source : ComposedState Arch Source) where
  decodeTarget : TargetArch.MachineState Arch → TargetId
  candidates : List (TargetId × BlockEntry Arch)
  uniqueTargetIds : (candidates.map Prod.fst).Nodup
  edge : BlockEdge source
  resolved : ∃ candidate ∈ candidates,
    candidate.1 = decodeTarget source.machine ∧ candidate.2 = edge.target

namespace BlockEdge

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- General edge-composition law. Constructing the second edge already demands
    the first target's entry contract, while the result exposes only the final
    target and the transitively preserved frame. -/
def trans {Arch : Type} [TargetArch Arch] {Source : Type}
    {source : ComposedState Arch Source}
    (first : BlockEdge source) (second : BlockEdge first.targetState) :
    BlockEdge source where
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
def activate {Arch : Type} [TargetArch Arch] {Source : Type}
    {source : ComposedState Arch Source} {enabled : Prop}
    (edge : ConditionalBlockEdge source enabled) (selected : enabled) :
    BlockEdge source where
  target := edge.target
  targetState := edge.targetState
  framePreserved := edge.framePreserved
  depthEstablished := edge.depthEstablished
  entryEstablished := edge.entryEstablished selected

end ConditionalBlockEdge

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Architecture-defined control-flow terminator family indexed over the terminal state. -/
inductive CpuTerminator (Arch : Type) [TargetArch Arch] {S : Type} (s_exit : ComposedState Arch S) where
  | jmp   (edge : BlockEdge s_exit) : CpuTerminator Arch s_exit
  | jmpIndirect {TargetId : Type} (edge : IndirectBlockEdge (TargetId := TargetId) s_exit) :
      CpuTerminator Arch s_exit
  | jcc   (cond : ConditionCode Arch)
          (targetTrue : ConditionalBlockEdge s_exit (cond.holds s_exit.machine))
          (targetFalse : ConditionalBlockEdge s_exit (¬ cond.holds s_exit.machine)) :
          CpuTerminator Arch s_exit
  | ret   (exportedObligations : List ObligationToken) (bytesToPop : UInt16 := 0)
          (h_zero      : s_exit.stackDepth = 0)
          (h_match     : s_exit.obligations = exportedObligations)
          (h_callee    : CalleeDiscipline Arch s_exit) : CpuTerminator Arch s_exit
  | sysExit (exitCode  : UInt8)
            (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) : CpuTerminator Arch s_exit
  | halt    (h_droppable : ∀ o ∈ s_exit.obligations, o.isDroppableOnExit) : CpuTerminator Arch s_exit

/- REF: docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators -/
/-- Single-entry basic block whose body is callable only with its typed entry
    contract established. -/
structure BasicBlock (Arch : Type) [TargetArch Arch] where
  entry : BlockEntry Arch
  body : (state : ComposedState Arch entry.State) → entry.accepts state →
    Σ (ExitState : Type), Σ (exit : ComposedState Arch ExitState), CpuTerminator Arch exit

/- REF: docs/STACK_DISCIPLINE.md#3-basicblock-structure-typed-terminators -/
/-- A finite typed CFG.  Closure is proved against the actual terminator returned
    by every block body, so a control-flow edge cannot name an entry contract
    that the graph did not publish. -/
structure TypedControlFlowGraph (Arch : Type) [TargetArch Arch] where
  blocks : List (BasicBlock Arch)
  entry : BlockEntry Arch
  entryInGraph : ∃ block ∈ blocks, block.entry = entry
  uniqueLabels : (blocks.map (·.entry.label)).Nodup
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
structure BlockControlPoint (Arch : Type) [TargetArch Arch] where
  block : BasicBlock Arch
  state : ComposedState Arch block.entry.State
  accepted : block.entry.accepts state

namespace TypedControlFlowGraph

/-- Membership of a typed control point in a graph is membership of its complete
    entry contract, not merely equality of a textual label. -/
def Contains {Arch : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch) (point : BlockControlPoint Arch) : Prop :=
  point.block ∈ graph.blocks

/-- Selection of exactly one successor from a terminator.  Conditional proof
    burden follows the branch that is actually enabled; the unselected target
    contributes no path-local obligation. -/
inductive SelectedEdge {Arch : Type} [TargetArch Arch] {S : Type}
    {exit : ComposedState Arch S} : CpuTerminator Arch exit → BlockEdge exit → Prop where
  | direct (edge : BlockEdge exit) : SelectedEdge (.jmp edge) edge
  | indirect {TargetId : Type} (edge : IndirectBlockEdge (TargetId := TargetId) exit) :
      SelectedEdge (.jmpIndirect edge) edge.edge
  | branchTrue (cond : ConditionCode Arch)
      (targetTrue : ConditionalBlockEdge exit (cond.holds exit.machine))
      (targetFalse : ConditionalBlockEdge exit (¬ cond.holds exit.machine))
      (selected : cond.holds exit.machine) :
      SelectedEdge (.jcc cond targetTrue targetFalse) (targetTrue.activate selected)
  | branchFalse (cond : ConditionCode Arch)
      (targetTrue : ConditionalBlockEdge exit (cond.holds exit.machine))
      (targetFalse : ConditionalBlockEdge exit (¬ cond.holds exit.machine))
      (selected : ¬ cond.holds exit.machine) :
      SelectedEdge (.jcc cond targetTrue targetFalse) (targetFalse.activate selected)

/-- Reindex a proved edge target by the exact block entry published in the
    graph.  Equality is over the complete dependent contract, never its label. -/
def targetPoint {Arch : Type} [TargetArch Arch] {Source : Type}
    {source : ComposedState Arch Source} (edge : BlockEdge source)
    (targetBlock : BasicBlock Arch) (sameEntry : targetBlock.entry = edge.target) :
    BlockControlPoint Arch :=
  ⟨targetBlock,
    BlockEntry.transportState sameEntry edge.targetState,
    BlockEntry.transport_accepts sameEntry edge.entryEstablished⟩

/-- One selected jump.  The successor already carries the destination's entry
    proof; the relation cannot represent an unchecked transfer. -/
inductive Step {Arch : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch) :
    BlockControlPoint Arch → BlockControlPoint Arch → Prop where
  | jump {source : BlockControlPoint Arch} {ExitState : Type}
      {exit : ComposedState Arch ExitState} {terminator : CpuTerminator Arch exit}
      (sourceInGraph : graph.Contains source)
      (bodyResult : source.block.body source.state source.accepted =
        ⟨ExitState, exit, terminator⟩)
      (edge : BlockEdge exit) (selected : SelectedEdge terminator edge)
      (targetBlock : BasicBlock Arch) (targetInGraph : targetBlock ∈ graph.blocks)
      (sameEntry : targetBlock.entry = edge.target) :
      Step graph source (targetPoint edge targetBlock sameEntry)

/-- Reflexive-transitive typed reachability.  Induction over this relation is
    the reusable whole-CFG proof rule: each block proves its contract once and
    each predecessor pays only for the selected target's precondition. -/
inductive Reachable {Arch : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch) :
    BlockControlPoint Arch → BlockControlPoint Arch → Prop where
  | refl (point) : Reachable graph point point
  | tail {start middle finish}
      (path : Reachable graph start middle) (step : Step graph middle finish) :
      Reachable graph start finish

theorem step_preserves_membership {Arch : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch} {source target : BlockControlPoint Arch}
    (step : Step graph source target) : graph.Contains target := by
  cases step with
  | jump _ _ _ _ _ targetInGraph _ => exact targetInGraph

theorem reachable_preserves_membership {Arch : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch} {start finish : BlockControlPoint Arch}
    (startInGraph : graph.Contains start) (path : Reachable graph start finish) :
    graph.Contains finish := by
  induction path with
  | refl => exact startInGraph
  | tail _ step _ => exact step_preserves_membership step

/-- A property factored at typed control-flow boundaries.  The preservation
    proof is demanded once per selected edge shape, never once per complete
    path through the routine. -/
structure Invariant {Arch : Type} [TargetArch Arch]
    (graph : TypedControlFlowGraph Arch) where
  holds : BlockControlPoint Arch → Prop
  preserved : ∀ {source target}, Step graph source target →
    holds source → holds target

theorem Invariant.alongReachable {Arch : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch} (invariant : Invariant graph)
    {start finish : BlockControlPoint Arch}
    (initial : invariant.holds start) (path : Reachable graph start finish) :
    invariant.holds finish := by
  induction path with
  | refl => exact initial
  | tail _ step ih => exact invariant.preserved step ih

theorem reachable_trans {Arch : Type} [TargetArch Arch]
    {graph : TypedControlFlowGraph Arch} {a b c : BlockControlPoint Arch}
    (ab : Reachable graph a b) (bc : Reachable graph b c) : Reachable graph a c := by
  induction bc with
  | refl => exact ab
  | tail _ step ih => exact .tail ih step

end TypedControlFlowGraph

end Gasm.Core

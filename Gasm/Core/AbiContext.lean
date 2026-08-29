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

namespace Gasm.Core

/-!
This module contains staging vocabulary for composable boundary contexts. It deliberately does not
define a link gate or a whole-program callability theorem. Constructing one of these descriptive
values is not authority to emit a `VerifiedProgram`; the required connection theorem is tracked in
`docs/ABI_CONTEXT.md`.

The logical vocabulary is a projection of the common authority/obligation world specified by
`docs/MEMORY_MODEL.md`. It is not a second ownership or cleanup system.
-/

/- REF: docs/ABI_CONTEXT.md#3-nominal-placement-free-contracts -/
/-- Whether a logical context is erased or requires a runtime realization. -/
inductive ContextMateriality where
  | erasedGhost
  | runtime
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-nominal-placement-free-contracts -/
/-- Logical lifetime is independent of the storage selected by a target realization. -/
inductive ContextExtent where
  | call
  | lexical
  | request
  | task
  | thread
  | process
  | object
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-nominal-placement-free-contracts -/
/-- How authority may cross a child or nested execution boundary. -/
inductive ContextPropagation where
  | borrow
  | copy
  | move
  | inherit
  | doNotPropagate
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-nominal-placement-free-contracts -/
/-- Whether a binding may follow work between execution agents. -/
inductive ContextScheduling where
  | pinned
  | migratable
  deriving Repr, DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#3-nominal-placement-free-contracts -/
/--
A nominal context key selects one canonical contract, including its common logical world and its
argument-, result-, and outcome-dependent obligation flow. `requiredObligations` and
`emittedObligations` are caller-facing projections; `transitions` remains the authoritative account
of preservation, transfer, discharge, creation, poisoning, and framing.

Rows will contain keys, not freely constructed records containing predicates. The eventual row
implementation must enforce coherent instances for every admitted key.
-/
class BoundaryContextSpec (World Key : Type) where
  Args : Type
  Binding : Type
  Result : Type
  Outcome : Type
  ObligationFragment : Type
  materiality : ContextMateriality
  extent : ContextExtent
  propagation : ContextPropagation
  scheduling : ContextScheduling
  carries : World → ObligationFragment → Prop
  requiredObligations : Args → Binding → ObligationFragment
  emittedObligations : Args → Binding → Result → Outcome → ObligationFragment
  requires : Args → Binding → World → Prop
  transitions : Args → Binding → Result → Outcome → World → World → Prop
  requires_carries : ∀ {args binding world},
    requires args binding world → carries world (requiredObligations args binding)
  transition_carries : ∀ {args binding result outcome before after},
    transitions args binding result outcome before after →
      carries after (emittedObligations args binding result outcome)

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- Proof that one call followed its nominal, value-dependent world transition. -/
structure ContextBoundaryTransition (World Key : Type) [spec : BoundaryContextSpec World Key]
    (args : spec.Args) (binding : spec.Binding) (result : spec.Result) (outcome : spec.Outcome)
    (before after : World) : Prop where
  requirementsHeld : spec.requires args binding before
  transitioned : spec.transitions args binding result outcome before after

/- REF: docs/ABI_CONTEXT.md#9-protocol-evolution-and-linking -/
/--
An explicit stateful refinement between two nominal context contracts. Worlds and obligation
fragments are related rather than assumed equal. A refinement must preserve both preconditions and
every result-indexed transition; equality of diagnostic names is irrelevant.
-/
structure ContextContractRefinement
    (OldWorld OldKey NewWorld NewKey : Type)
    [oldSpec : BoundaryContextSpec OldWorld OldKey]
    [newSpec : BoundaryContextSpec NewWorld NewKey] where
  relateWorld : OldWorld → NewWorld → Prop
  adaptArgs : oldSpec.Args → newSpec.Args
  adaptBinding : oldSpec.Binding → newSpec.Binding
  adaptResult : oldSpec.Result → newSpec.Result
  adaptOutcome : oldSpec.Outcome → newSpec.Outcome
  adaptObligations : oldSpec.ObligationFragment → newSpec.ObligationFragment
  preservesRequiredObligations : ∀ args binding,
    adaptObligations (oldSpec.requiredObligations args binding) =
      newSpec.requiredObligations (adaptArgs args) (adaptBinding binding)
  preservesEmittedObligations : ∀ args binding result outcome,
    adaptObligations (oldSpec.emittedObligations args binding result outcome) =
      newSpec.emittedObligations (adaptArgs args) (adaptBinding binding)
        (adaptResult result) (adaptOutcome outcome)
  preservesRequirements : ∀ {args binding oldWorld newWorld},
    relateWorld oldWorld newWorld → oldSpec.requires args binding oldWorld →
      newSpec.requires (adaptArgs args) (adaptBinding binding) newWorld
  preservesTransitions : ∀ {args binding result outcome oldBefore oldAfter newBefore},
    relateWorld oldBefore newBefore →
    oldSpec.transitions args binding result outcome oldBefore oldAfter →
      ∃ newAfter,
        relateWorld oldAfter newAfter ∧
        newSpec.transitions (adaptArgs args) (adaptBinding binding) (adaptResult result)
          (adaptOutcome outcome) newBefore newAfter

/- REF: docs/ABI_CONTEXT.md#5-target-realization-interface -/
/--
A target/environment profile owns its entry and exit classes, classified signatures, physical
states, executions, and complete admissibility predicate. `admissible` is where that profile states
phase/path-sensitive access, byte-range aliasing, intended handoffs, value agreement, helper-call
clobbers, unwind behavior, and preservation. No universal pairwise access matrix can replace it.
-/
class TargetBoundarySemantics (Target : Type) where
  Signature : Type
  EntryKind : Type
  ExitKind : Type
  PhysicalState : Type
  Execution : Type
  runs : Signature → EntryKind → PhysicalState → Execution → ExitKind → PhysicalState → Prop
  admissible : Signature → EntryKind → PhysicalState → Execution → ExitKind → PhysicalState → Prop

/- REF: docs/ABI_CONTEXT.md#5-target-realization-interface -/
/--
A staged realization connects every physical execution of one boundary to the exact nominal logical
transition. Physical admissibility is mandatory, not an optional footprint supplied by the
realization. This remains disconnected from `VerifiedProgram` until the whole-program theorem and
closed target profiles exist.
-/
structure ContextBoundaryRealization
    (World Key Target : Type)
    [spec : BoundaryContextSpec World Key]
    [target : TargetBoundarySemantics Target] where
  signature : target.Signature
  entryKind : target.EntryKind
  logicalArgs : target.PhysicalState → target.Execution → spec.Args
  logicalBinding : target.PhysicalState → target.Execution → spec.Binding
  logicalResult : target.Execution → target.PhysicalState → spec.Result
  logicalOutcome : target.ExitKind → target.Execution → target.PhysicalState → spec.Outcome
  logicalWorld : target.PhysicalState → World
  physicalAdmissibility : ∀ {before execution exitKind after},
    target.runs signature entryKind before execution exitKind after →
      target.admissible signature entryKind before execution exitKind after
  refinesContract : ∀ {before execution exitKind after},
    target.runs signature entryKind before execution exitKind after →
      ContextBoundaryTransition World Key
        (logicalArgs before execution)
        (logicalBinding before execution)
        (logicalResult execution after)
        (logicalOutcome exitKind execution after)
        (logicalWorld before)
        (logicalWorld after)

end Gasm.Core

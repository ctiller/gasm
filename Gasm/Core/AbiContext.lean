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
  requiredObligations : Args → Binding → ObligationFragment
  emittedObligations : Args → Binding → Result → Outcome → ObligationFragment
  requires : Args → Binding → World → Prop
  transitions : Args → Binding → Result → Outcome → World → World → Prop

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- Proof that one call followed its nominal, value-dependent world transition. -/
structure ContextBoundaryTransition (World Key : Type) [spec : BoundaryContextSpec World Key]
    (args : spec.Args) (binding : spec.Binding) (result : spec.Result) (outcome : spec.Outcome)
    (before after : World) : Prop where
  requirementsHeld : spec.requires args binding before
  transitioned : spec.transitions args binding result outcome before after

/- REF: docs/ABI_CONTEXT.md#5-target-realization-interface -/
/--
A target/environment profile owns implementation and artifact identities, entry and exit classes,
classified signatures, physical states, executions, and its complete admissibility predicate.
`admissible` is where that profile states phase/path-sensitive access, byte-range aliasing, intended
handoffs, value agreement, helper-call clobbers, unwind behavior, and preservation. No universal
pairwise access matrix can replace it.
-/
class TargetBoundarySemantics (Target : Type) where
  Implementation : Type
  Artifact : Type
  Signature : Type
  EntryKind : Type
  ExitKind : Type
  PhysicalState : Type
  Execution : Type
  artifactImplements : Artifact → Implementation → Prop
  runs : Implementation → Signature → EntryKind →
    PhysicalState → Execution → ExitKind → PhysicalState → Prop
  admissible : Implementation → Signature → EntryKind →
    PhysicalState → Execution → ExitKind → PhysicalState → Prop

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
  implementation : target.Implementation
  artifact : target.Artifact
  artifactConnection : target.artifactImplements artifact implementation
  logicalArgs : target.PhysicalState → spec.Args
  logicalBinding : target.PhysicalState → spec.Binding
  logicalResult : target.PhysicalState → target.Execution → target.PhysicalState → spec.Result
  logicalOutcome : target.PhysicalState → target.Execution →
    target.ExitKind → target.PhysicalState → spec.Outcome
  relatesWorld : target.PhysicalState → World → Prop
  physicalAdmissibility : ∀ {before execution exitKind after},
    target.runs implementation signature entryKind before execution exitKind after →
      target.admissible implementation signature entryKind before execution exitKind after
  refinesContract : ∀ {physicalBefore logicalBefore execution exitKind physicalAfter},
    relatesWorld physicalBefore logicalBefore →
    spec.requires (logicalArgs physicalBefore) (logicalBinding physicalBefore) logicalBefore →
    target.runs implementation signature entryKind
      physicalBefore execution exitKind physicalAfter →
      ∃ logicalAfter,
        relatesWorld physicalAfter logicalAfter ∧
        spec.transitions
          (logicalArgs physicalBefore)
          (logicalBinding physicalBefore)
          (logicalResult physicalBefore execution physicalAfter)
          (logicalOutcome physicalBefore execution exitKind physicalAfter)
          logicalBefore logicalAfter

end Gasm.Core

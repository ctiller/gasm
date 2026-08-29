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
  PublicEntry : Type
  LookupKey : Type
  artifactImplements : Artifact → Implementation → Prop
  publicEntries : Artifact → List PublicEntry
  callableEntries : Artifact → List PublicEntry
  lookupKey : PublicEntry → LookupKey
  resolvesEntry : Artifact → PublicEntry → Implementation → Signature → EntryKind → Prop
  jointlyAdmissible : Artifact → List (PublicEntry × Implementation × Signature × EntryKind) → Prop
  runs : Artifact → Implementation → Signature → EntryKind →
    PhysicalState → Execution → ExitKind → PhysicalState → Prop
  admissible : Artifact → Implementation → Signature → EntryKind →
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
  relatesEntry : target.PhysicalState → spec.Args → spec.Binding → World → Prop
  logicalResult : target.PhysicalState → target.Execution → target.PhysicalState → spec.Result
  logicalOutcome : target.PhysicalState → target.Execution →
    target.ExitKind → target.PhysicalState → spec.Outcome
  relatesWorld : target.PhysicalState → World → Prop
  entryRelatesWorld : ∀ {physicalState args binding world},
    relatesEntry physicalState args binding world → relatesWorld physicalState world
  physicalAdmissibility : ∀ {before execution exitKind after},
    target.runs artifact implementation signature entryKind before execution exitKind after →
      target.admissible artifact implementation signature entryKind before execution exitKind after
  refinesContract : ∀ {physicalBefore args binding logicalBefore execution exitKind physicalAfter},
    relatesEntry physicalBefore args binding logicalBefore →
    spec.requires args binding logicalBefore →
    target.runs artifact implementation signature entryKind
      physicalBefore execution exitKind physicalAfter →
      ∃ logicalAfter,
        relatesWorld physicalAfter logicalAfter ∧
        spec.transitions
          args
          binding
          (logicalResult physicalBefore execution physicalAfter)
          (logicalOutcome physicalBefore execution exitKind physicalAfter)
          logicalBefore logicalAfter

/- REF: docs/ABI_CONTEXT.md#10-whole-program-connection-obligations -/
/--
Caller-side evidence that a concrete entry state supplies the exact arguments, binding, world, and
precondition consumed by a boundary realization. Requiring this certificate at the emission gate
prevents an empty `relatesEntry` relation from authorizing a program vacuously.
-/
structure EstablishedBoundaryEntry
    (World Key Target Environment : Type)
    [spec : BoundaryContextSpec World Key]
    [target : TargetBoundarySemantics Target]
    (realization : ContextBoundaryRealization World Key Target)
    (load : target.Artifact → Environment → target.PhysicalState) where
  args : Environment → spec.Args
  binding : Environment → spec.Binding
  world : Environment → World
  related : ∀ environment,
    realization.relatesEntry
      (load realization.artifact environment)
      (args environment)
      (binding environment)
      (world environment)
  requirementsHeld : ∀ environment,
    spec.requires (args environment) (binding environment) (world environment)

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/--
A non-total artifact intended to be loaded or linked as a library.  It makes no
whole-process root claim: each published export instead carries an
assume/guarantee boundary realization, and every realization is tied to the one
artifact selected for component emission.  Callers must separately establish
`relatesEntry` and `requires` at each invocation.
-/
structure PublishedBoundary
    (World Key Target : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target) where
  physicalEntry : target.PublicEntry
  realization : @ContextBoundaryRealization World Key Target spec target
  resolves : target.resolvesEntry realization.artifact physicalEntry
    realization.implementation realization.signature realization.entryKind

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- Joint certificate for the complete public surface of one final artifact.
    Individual boundary proofs do not compose unconditionally: target-owned
    joint admissibility is mandatory after final layout and relocation. -/
structure VerifiedExportSet
    (World Key Target : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target) where
  artifact : target.Artifact
  publicManifest : List target.PublicEntry
  entries : List (PublishedBoundary World Key Target spec target)
  uniqueLookup : (publicManifest.map target.lookupKey).Nodup
  exactPublicTable : publicManifest = target.publicEntries artifact
  exactCallableTable : entries.map (·.physicalEntry) = target.callableEntries artifact
  sameArtifact : ∀ entry, entry ∈ entries → entry.realization.artifact = artifact
  jointlyAdmissible : target.jointlyAdmissible artifact
    (entries.map fun entry =>
      (entry.physicalEntry, entry.realization.implementation,
        entry.realization.signature, entry.realization.entryKind))

namespace VerifiedExportSet

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- Canonical certificate for a target artifact with no public surface.  The
    caller proves the three target-owned facts once; no per-export evidence is
    manufactured or demanded. -/
def empty
    (World Key Target : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target)
    (artifact : target.Artifact)
    (publicEmpty : target.publicEntries artifact = [])
    (callableEmpty : target.callableEntries artifact = [])
    (joint : target.jointlyAdmissible artifact []) :
    VerifiedExportSet World Key Target spec target where
  artifact := artifact
  publicManifest := []
  entries := []
  uniqueLookup := by simp
  exactPublicTable := publicEmpty.symm
  exactCallableTable := callableEmpty.symm
  sameArtifact := by simp
  jointlyAdmissible := joint

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- Canonical certificate when an executable has a physical public manifest
    (for example `_start` and a Wasm memory) but no auxiliary callable library
    boundary.  Only lookup uniqueness and the target's two global facts remain
    to prove. -/
def withoutCallableEntries
    (World Key Target : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target)
    (artifact : target.Artifact)
    (unique : ((target.publicEntries artifact).map target.lookupKey).Nodup)
    (callableEmpty : target.callableEntries artifact = [])
    (joint : target.jointlyAdmissible artifact []) :
    VerifiedExportSet World Key Target spec target where
  artifact := artifact
  publicManifest := target.publicEntries artifact
  entries := []
  uniqueLookup := unique
  exactPublicTable := rfl
  exactCallableTable := callableEmpty.symm
  sameArtifact := by simp
  jointlyAdmissible := joint

end VerifiedExportSet

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- A non-total library/component is exactly a nonempty jointly verified
    callable export set, with no fabricated whole-process root theorem. -/
structure VerifiedComponent
    (World Key Target : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target) where
  exportSet : VerifiedExportSet World Key Target spec target
  callableNonempty : exportSet.entries ≠ []

end Gasm.Core

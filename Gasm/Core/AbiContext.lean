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
This module contains staging vocabulary and reusable export/link certificates for composable
boundary contexts. `Gasm.Core.Platform` carries exact export-set evidence into `VerifiedProgram`,
but this module deliberately does not define the closed per-call gate or a substantive target
callability theorem. Constructing one realization is therefore not execution or emission authority;
the remaining connection obligations are tracked in `docs/ABI_CONTEXT.md`.

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
  Args : Key → Type
  Binding : Key → Type
  Result : Key → Type
  Outcome : Key → Type
  ObligationFragment : Key → Type
  requiredObligations : (key : Key) → Args key → Binding key → ObligationFragment key
  emittedObligations : (key : Key) →
    Args key → Binding key → Result key → Outcome key → ObligationFragment key
  requires : (key : Key) → Args key → Binding key → World → Prop
  transitions : (key : Key) →
    Args key → Binding key → Result key → Outcome key → World → World → Prop

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- Proof that one call followed its nominal, value-dependent world transition. -/
structure ContextBoundaryTransition (World Key : Type) [spec : BoundaryContextSpec World Key]
    (key : Key) (args : spec.Args key) (binding : spec.Binding key)
    (result : spec.Result key) (outcome : spec.Outcome key)
    (before after : World) : Prop where
  requirementsHeld : spec.requires key args binding before
  transitioned : spec.transitions key args binding result outcome before after

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
realization. A realization may be published only through exact export/artifact certificates, and a
reachable call still needs caller establishment plus a closed substantive target profile.
-/
structure ContextBoundaryRealization
    (World Key Target : Type)
    [spec : BoundaryContextSpec World Key]
    [target : TargetBoundarySemantics Target]
    (key : Key) where
  signature : target.Signature
  entryKind : target.EntryKind
  implementation : target.Implementation
  artifact : target.Artifact
  artifactConnection : target.artifactImplements artifact implementation
  relatesEntry : target.PhysicalState → spec.Args key → spec.Binding key → World → Prop
  relatesWorld : target.PhysicalState → World → Prop
  relatesExit : target.PhysicalState → target.Execution → target.ExitKind →
    target.PhysicalState → spec.Result key → spec.Outcome key → World → Prop
  entryRelatesWorld : ∀ {physicalState args binding world},
    relatesEntry physicalState args binding world → relatesWorld physicalState world
  exitRelatesWorld : ∀ {physicalBefore execution exitKind physicalAfter result outcome world},
    relatesExit physicalBefore execution exitKind physicalAfter result outcome world →
      relatesWorld physicalAfter world
  physicalAdmissibility : ∀ {before execution exitKind after},
    target.runs artifact implementation signature entryKind before execution exitKind after →
      target.admissible artifact implementation signature entryKind before execution exitKind after
  refinesContract : ∀ {physicalBefore args binding logicalBefore execution exitKind physicalAfter},
    relatesEntry physicalBefore args binding logicalBefore →
    spec.requires key args binding logicalBefore →
    target.runs artifact implementation signature entryKind
      physicalBefore execution exitKind physicalAfter →
      ∃ result outcome logicalAfter,
        relatesExit physicalBefore execution exitKind physicalAfter result outcome logicalAfter ∧
        spec.transitions key
          args
          binding
          result
          outcome
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
    (key : Key)
    (realization : ContextBoundaryRealization World Key Target key)
    (load : target.Artifact → Environment → target.PhysicalState) where
  args : Environment → spec.Args key
  binding : Environment → spec.Binding key
  world : Environment → World
  related : ∀ environment,
    realization.relatesEntry
      (load realization.artifact environment)
      (args environment)
      (binding environment)
      (world environment)
  requirementsHeld : ∀ environment,
    spec.requires key (args environment) (binding environment) (world environment)

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
  key : Key
  physicalEntry : target.PublicEntry
  realization : @ContextBoundaryRealization World Key Target spec target key
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

/- REF: docs/ABI_CONTEXT.md#10-whole-program-connection-obligations -/
/--
The closed logical gate for one selected call to one published boundary.  The
boundary must be an exact member of the final artifact's callable export set,
and the caller must establish the realization's complete dependent entry
tuple.  Code which contains no such call constructs no certificate and pays
no context proof burden.

This certificate does not identify a machine call instruction by itself.  A
target CFG/artifact bridge must connect the selected call edge to
`boundary.physicalEntry`; after that connection, `refines` below supplies the
logical transition without reopening export-layout or ABI-realization proofs.
-/
structure VerifiedBoundaryCall
    (World Key Target Call : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target)
    (exports : VerifiedExportSet World Key Target spec target)
    (loadCallState : target.Artifact → Call → target.PhysicalState) where
  boundary : PublishedBoundary World Key Target spec target
  member : boundary ∈ exports.entries
  established : @EstablishedBoundaryEntry
    World Key Target Call spec target boundary.key boundary.realization loadCallState

namespace VerifiedBoundaryCall

/- REF: docs/ABI_CONTEXT.md#10-whole-program-connection-obligations -/
/-- Membership in the final export set fixes the realization to the exact
    final boundary artifact. -/
theorem realization_artifact_eq
    {World Key Target Call : Type}
    {spec : BoundaryContextSpec World Key}
    {target : TargetBoundarySemantics Target}
    {exports : VerifiedExportSet World Key Target spec target}
    {loadCallState : target.Artifact → Call → target.PhysicalState}
    (call : VerifiedBoundaryCall World Key Target Call spec target exports loadCallState) :
    call.boundary.realization.artifact = exports.artifact :=
  exports.sameArtifact call.boundary call.member

/- REF: docs/ABI_CONTEXT.md#10-whole-program-connection-obligations -/
/-- Every physical execution reached through an established selected call has
    the boundary's exact result/outcome-indexed logical transition. -/
theorem refines
    {World Key Target Call : Type}
    {spec : BoundaryContextSpec World Key}
    {target : TargetBoundarySemantics Target}
    {exports : VerifiedExportSet World Key Target spec target}
    {loadCallState : target.Artifact → Call → target.PhysicalState}
    (call : VerifiedBoundaryCall World Key Target Call spec target exports loadCallState)
    (site : Call)
    {execution : target.Execution}
    {exitKind : target.ExitKind}
    {physicalAfter : target.PhysicalState}
    (runs : target.runs
      exports.artifact
      call.boundary.realization.implementation
      call.boundary.realization.signature
      call.boundary.realization.entryKind
      (loadCallState exports.artifact site)
      execution exitKind physicalAfter) :
    ∃ result outcome logicalAfter,
      call.boundary.realization.relatesExit
        (loadCallState exports.artifact site)
        execution exitKind physicalAfter result outcome logicalAfter ∧
      spec.transitions call.boundary.key
        (call.established.args site)
        (call.established.binding site)
        result outcome
        (call.established.world site) logicalAfter := by
  have artifactEq := realization_artifact_eq call
  have related := call.established.related site
  have refined := call.boundary.realization.refinesContract
    related (call.established.requirementsHeld site)
    (by simpa [artifactEq] using runs)
  simpa [artifactEq] using refined

end VerifiedBoundaryCall

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- Target-owned final-link semantics are separate from boundary semantics so
    targets which never link components incur no proof burden.  A plan denotes
    the actual layout/relocation/import-resolution operation; `safe` must cover
    its whole final artifact, including recursive call components and shared
    runtime state. -/
class TargetLinkSemantics
    (Target : Type)
    (target : TargetBoundarySemantics Target) where
  Plan : Type
  sourceArtifacts : Plan → List target.Artifact
  finalArtifact : Plan → target.Artifact
  safe : Plan → Prop

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- Evidence that particular verified source surfaces were safely moved into
    one particular final artifact.  The final export set is proved directly
    against that artifact; source certificates cannot be combined by names or
    pairwise ABI agreement alone. -/
structure JointLinkCertificate
    (World Key Target : Type)
    (spec : BoundaryContextSpec World Key)
    (target : TargetBoundarySemantics Target)
    (linker : TargetLinkSemantics Target target)
    (sources : List (VerifiedExportSet World Key Target spec target))
    (final : VerifiedExportSet World Key Target spec target) where
  plan : linker.Plan
  exactSources : linker.sourceArtifacts plan = sources.map (·.artifact)
  exactFinal : linker.finalArtifact plan = final.artifact
  safe : linker.safe plan

/- REF: docs/ABI_CONTEXT.md#11-non-total-components-and-exported-boundaries -/
/-- The composition law exposes only the export set proved for the final
    artifact.  Its small conclusion is intentional: all difficult linking
    evidence is paid once by `JointLinkCertificate`, never by downstream
    callers of an already-linked component. -/
def JointLinkCertificate.composedExportSet
    {World Key Target : Type}
    {spec : BoundaryContextSpec World Key}
    {target : TargetBoundarySemantics Target}
    {linker : TargetLinkSemantics Target target}
    {sources : List (VerifiedExportSet World Key Target spec target)}
    {final : VerifiedExportSet World Key Target spec target}
    (_certificate : JointLinkCertificate World Key Target spec target linker sources final) :
    VerifiedExportSet World Key Target spec target :=
  final

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

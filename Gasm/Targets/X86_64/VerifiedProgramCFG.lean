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

import Gasm.Core.Verification
import Gasm.Targets.X86_64.CFGLinker

/-!
Verified-program-owned CFG/artifact certificates for native x86-64 targets.

The certificate below deliberately starts with a `VerifiedProgram`, rather
than with a caller-selected artifact or a post-hoc equality.  A native target
profile is responsible for extracting the instruction index from that exact
artifact and for identifying the runtime which consumes it.
Consequently an operational CFG proof cannot combine the graph from one
program with the artifact, providers, runtime, or environment of another.
-/

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Targets.X86_64.MacroAssembler

universe u

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Target-owned native x86-64 profile laws.  The profile has no independently
    supplied runtime adapter: `runtimeOf` is derived from the platform's
    runtime-context identity below.  The execution law is guarded by the
    platform's own `artifactConnected` predicate, so a caller cannot attach a
    CFG to an unrelated text image. -/
class NativeX86_64Profile (P : Type) (Event : Type) [Platform P] where
  linkedText : Platform.Artifact (P := P) → CFGLinker.LinkedText
  machineState : Platform.State (P := P) = X86_64MachineState
  runtimeContext : Platform.RuntimeContext (P := P) = ExternalCallInterceptor X86_64 Event
  observation : Platform.Observation (P := P) = List Event
  runFromConnected : ∀ (runtime : Platform.RuntimeContext (P := P))
      (artifact : Platform.Artifact (P := P)) (_connected : Platform.artifactConnected artifact)
      (state : X86_64MachineState),
    Platform.run runtime artifact (cast machineState.symm state) =
      cast observation.symm
        (letI : ExternalCallInterceptor X86_64 Event :=
            cast runtimeContext runtime
         (runProgramOutcomeWithLoops (Event := Event) state.rip
           (linkedText artifact).instructions 50000 state).events)

/-- The runtime interceptor is determined by the target's runtime-context
    identity; it is not a second certificate field that a client may replace. -/
@[instance_reducible] def NativeX86_64Profile.runtimeOf {P Event : Type} [Platform P]
    [profile : NativeX86_64Profile P Event]
    (runtime : Platform.RuntimeContext (P := P)) : ExternalCallInterceptor X86_64 Event :=
  cast profile.runtimeContext runtime

/-- The production instruction index of the target-owned linked text.  The
    index is a projection of the artifact, not an argument accepted from a CFG
    client. -/
def NativeX86_64Profile.instructionIndex {P Event : Type} [Platform P]
    [NativeX86_64Profile P Event] (artifact : Platform.Artifact (P := P)) :
    List (UInt64 × X86_64Instr) :=
  (NativeX86_64Profile.linkedText (P := P) (Event := Event) artifact).indexed

/-- The derived interceptor transports provider support back to the platform's
    exact runtime context. -/
theorem NativeX86_64Profile.runtimeOf_supports {P Event : Type} [Platform P]
    [profile : NativeX86_64Profile P Event]
    (runtime : Platform.RuntimeContext (P := P))
    (artifact : Platform.Artifact (P := P)) (provider : Platform.Provider (P := P))
    (supported : Platform.runtimeSupports runtime artifact provider) :
    Platform.runtimeSupports
      (cast profile.runtimeContext.symm (profile.runtimeOf runtime)) artifact provider := by
  simpa [NativeX86_64Profile.runtimeOf] using supported

/-- Realizing a capability row and then deriving the native interceptor cannot
    select a different platform runtime context. -/
theorem NativeX86_64Profile.runtimeOf_realize {P Event : Type} [Platform P]
    [profile : NativeX86_64Profile P Event] (capabilities : CapabilityComposition P)
    (artifact : Platform.Artifact (P := P)) (context : capabilities.root.Context) :
    cast profile.runtimeContext.symm
      (profile.runtimeOf (capabilities.realize artifact context)) =
      capabilities.realize artifact context := by
  simp [NativeX86_64Profile.runtimeOf]

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The Linux target's instruction index is extracted directly from the exact
    artifact published by its platform profile. -/
instance linuxNativeX86_64Profile {Event : Type} :
    NativeX86_64Profile (LinuxX86_64 Event) Event where
  linkedText := fun artifact =>
    { base := artifact.executable.load.rip, instructions := artifact.instructions }
  machineState := rfl
  runtimeContext := rfl
  observation := rfl
  runFromConnected := by
    intro runtime artifact _ state
    rfl

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The Windows target's instruction index is extracted directly from the exact
    PE artifact published by its platform profile. -/
instance windowsNativeX86_64Profile {Event : Type} :
    NativeX86_64Profile (WindowsX86_64 Event) Event where
  linkedText := fun artifact =>
    { base := artifact.executable.load.rip, instructions := artifact.instructions }
  machineState := rfl
  runtimeContext := rfl
  observation := rfl
  runFromConnected := by
    intro runtime artifact _ state
    rfl

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- A whole-CFG realization pinned to one `VerifiedProgram`, one environment,
    its exact final artifact, and the runtime context that the program itself
    establishes for that environment.  `layout`, `emitted`, and `realizes`
    are the existing target bridge obligations; all program/export/provider
    facts are projections of the sole whole-program authority rather than
    independently supplied claims. -/
structure VerifiedProgramCFGArtifactCertificate
    {P : Type} [Platform P] {Event : Type} [NativeX86_64Profile P Event]
    {capabilities : CapabilityComposition P}
    (program : VerifiedProgram P capabilities) (environment : Environment)
    (graph : TypedControlFlowGraph X86_64 BlockId) where
  layout : CFGLinker.ClosedCFGLayout graph
    (NativeX86_64Profile.linkedText (P := P) (Event := Event) program.artifact)
  realizes : ∀ (block : BasicBlock X86_64 BlockId) (member : block ∈ graph.blocks)
    (state : ComposedState X86_64 block.entry.State) (accepted : block.entry.accepts state),
    @EmittedBasicBlock.RealizesAt Event Unit BlockId
      (NativeX86_64Profile.runtimeOf (P := P) (Event := Event)
        (capabilities.realize program.artifact (program.entryContext environment)))
      (fun _ : Unit => NativeX86_64Profile.instructionIndex (P := P) (Event := Event)
        program.artifact) ()
      block (layout.emitted block member) state accepted
  /-- Exact, loaded control point for this graph.  Its machine state is the
      platform loader state for this program/environment; the remaining
      composed-state resources are fixed by the entry contract rather than
      invented by a path theorem. -/
  entryPoint : BlockControlPoint X86_64 BlockId
  entryInGraph : entryPoint.block ∈ graph.blocks
  entryExact : entryPoint.block.entry = graph.entry
  entryLoadedState :
    cast (NativeX86_64Profile.machineState (P := P) (Event := Event)).symm
      entryPoint.state.machine = Platform.load program.artifact environment

namespace VerifiedProgramCFGArtifactCertificate

variable {P : Type} [Platform P] {Event : Type} [NativeX86_64Profile P Event]
  {capabilities : CapabilityComposition P}
  {program : VerifiedProgram P capabilities} {environment : Environment}
  {graph : TypedControlFlowGraph X86_64 BlockId}

/-- The concrete runtime used by this CFG certificate is exactly the runtime
    realized from the program's own entry context for its fixed environment. -/
@[instance_reducible] def runtime (_certificate : VerifiedProgramCFGArtifactCertificate (Event := Event)
    program environment graph) :
    ExternalCallInterceptor X86_64 Event :=
  NativeX86_64Profile.runtimeOf (P := P) (Event := Event)
    (capabilities.realize program.artifact (program.entryContext environment))

/-- Reassemble the existing graph-wide operational bridge without introducing
    a second control-flow authority. -/
def operational (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event)
    program environment graph) :
    letI : ExternalCallInterceptor X86_64 Event := runtime certificate
    OperationalCFGRealization (Event := Event)
      (fun _ : Unit => NativeX86_64Profile.instructionIndex (P := P) (Event := Event)
        program.artifact) () graph := by
  letI : ExternalCallInterceptor X86_64 Event := runtime certificate
  exact {
    layout := certificate.layout.indexedLayout
    emitted := certificate.layout.emitted
    realizes := certificate.realizes }

/-- The final-artifact connection is the one stored in the sole
    `VerifiedProgram`; a CFG client cannot replace its artifact. -/
theorem artifactConnected
    (_certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    Platform.artifactConnected program.artifact :=
  program.artifactConnection

/-- Exact public export evidence for the same program artifact. -/
def artifactCertificate
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    ProgramArtifactCertificate P where
  artifact := program.artifact
  exports := program.exports
  exportsArtifact := program.exportsArtifact
  artifactConnection := certificate.artifactConnected

/-- Every selected provider is linked to the exact artifact that supplies the
    certificate's instruction index. -/
theorem providerLinked
    (_certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    (provider : Platform.Provider (P := P))
    (selected : provider ∈ capabilities.root.providers) :
    Platform.providerLinked program.artifact provider :=
  program.providersLinked provider selected

/-- The exact realized runtime supports every provider selected by the program
    on the same final artifact. -/
theorem runtimeSupportsProvider
    (_certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    (provider : Platform.Provider (P := P))
    (selected : provider ∈ capabilities.root.providers) :
    Platform.runtimeSupports
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact provider :=
  capabilities.realizeSupports (program.entryContext environment) program.artifact provider
    selected (program.providersLinked provider selected)

/-- Provider support survives transport to the exact interceptor consumed by
    the CFG bridge. -/
theorem operationalRuntimeSupportsProvider
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    (provider : Platform.Provider (P := P))
    (selected : provider ∈ capabilities.root.providers) :
    Platform.runtimeSupports
      (cast (NativeX86_64Profile.runtimeContext (P := P) (Event := Event)).symm
        (runtime certificate))
      program.artifact provider :=
  NativeX86_64Profile.runtimeOf_supports (P := P) (Event := Event)
    (capabilities.realize program.artifact (program.entryContext environment))
    program.artifact provider
    (capabilities.realizeSupports (program.entryContext environment) program.artifact provider
      selected (program.providersLinked provider selected))

/-- The runtime consumed by the bridge is the program's realized runtime,
    transported only across the target's fixed runtime-context identity. -/
theorem operationalRuntimeIsRealized
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    cast (NativeX86_64Profile.runtimeContext (P := P) (Event := Event)).symm
      (runtime certificate) =
      capabilities.realize program.artifact (program.entryContext environment) :=
  NativeX86_64Profile.runtimeOf_realize (P := P) (Event := Event) capabilities
    program.artifact (program.entryContext environment)

/-- The environment is fixed in the certificate, so the program's entry proof
    establishes precisely the runtime context used by `operational`. -/
theorem entryEstablished
    (_certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    capabilities.root.establishes program.artifact environment
      (Platform.load program.artifact environment) (program.entryContext environment) :=
  program.entryEstablished environment

/-- The platform safety predicate applies to the same artifact, environment,
    and realized runtime—not to an edge-local existential profile. -/
theorem platformAdmissible
    (_certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    Platform.admissible
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact (Platform.load program.artifact environment) :=
  program.platformAdmissible environment

/-- The certificate's entry control point is published by the graph and uses
    the exact graph entry contract. -/
theorem entryPublished
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    graph.Contains certificate.entryPoint :=
  certificate.entryInGraph

/-- The published control point is the graph's designated entry block. -/
theorem entryIsGraphEntry
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    certificate.entryPoint.block.entry = graph.entry :=
  certificate.entryExact

/-- The loaded entry state satisfies the exact entry predicate, not merely an
    existentially chosen block predicate. -/
theorem entryAccepted
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    certificate.entryPoint.block.entry.accepts certificate.entryPoint.state :=
  certificate.entryPoint.accepted

/-- Transporting the entry control point's machine component back through the
    fixed target identity yields the exact platform loader result. -/
theorem entryStateIsLoaded
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    cast (NativeX86_64Profile.machineState (P := P) (Event := Event)).symm
      certificate.entryPoint.state.machine = Platform.load program.artifact environment :=
  certificate.entryLoadedState

/-- Production execution of a connected artifact is fixed by the native
    profile's target-owned law.  It consumes the program's selected runtime,
    artifact connection, and loaded machine state together. -/
theorem runLoadedMachineExact
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph) :
    Platform.run
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact (Platform.load program.artifact environment) =
      cast (NativeX86_64Profile.observation (P := P) (Event := Event)).symm
        (letI : ExternalCallInterceptor X86_64 Event := runtime certificate
         (runProgramOutcomeWithLoops (Event := Event)
           certificate.entryPoint.state.machine.rip
           (NativeX86_64Profile.linkedText (P := P) (Event := Event)
             program.artifact).instructions 50000
           certificate.entryPoint.state.machine).events) := by
  rw [← certificate.entryLoadedState]
  exact NativeX86_64Profile.runFromConnected
    (P := P) (Event := Event)
    (capabilities.realize program.artifact (program.entryContext environment))
    program.artifact program.artifactConnection certificate.entryPoint.state.machine

/-- Any point reached from the exact loaded entry through the typed graph is a
    published block, so its *path-carried* control point is covered by the
    same artifact-bound realization.  No fresh target state is accepted here.
    This is terminator-agnostic: direct, indirect, conditional, and future
    effectful terminators remain within the one graph closure rather than
    carrying edge-local artifact/profile existentials. -/
theorem realizesReachable
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    {finish : BlockControlPoint X86_64 BlockId}
    (reachable : TypedControlFlowGraph.Reachable graph certificate.entryPoint finish) :
    @EmittedBasicBlock.RealizesAt Event Unit BlockId (runtime certificate)
      (fun _ : Unit => NativeX86_64Profile.instructionIndex (P := P) (Event := Event)
        program.artifact) ()
      finish.block
      (certificate.layout.emitted finish.block
        (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable))
      finish.state finish.accepted :=
  by
    letI := runtime certificate
    exact certificate.realizes finish.block
      (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable)
      finish.state finish.accepted

/-- Execute the exact loaded graph entry's emitted block. -/
theorem runEntryBlock
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    (fuel : Nat) (eventsRev : List Event) :
    letI := runtime certificate
    let result := certificate.entryPoint.block.body
      certificate.entryPoint.state certificate.entryPoint.accepted
    let next := nativeOutcomeTransition
      (certificate.layout.emitted certificate.entryPoint.block certificate.entryInGraph).terminatorInstruction
      (runLocalSteps
        (certificate.layout.emitted certificate.entryPoint.block certificate.entryInGraph).bodyCode
        certificate.entryPoint.state.machine) eventsRev
    runProgramOutcomeLoop
        (NativeX86_64Profile.instructionIndex (P := P) (Event := Event) program.artifact)
        ((certificate.layout.emitted certificate.entryPoint.block certificate.entryInGraph).bodyCode.length +
          (fuel + 1)) certificate.entryPoint.state.machine eventsRev =
      resumeAfterTerminator
        (NativeX86_64Profile.instructionIndex (P := P) (Event := Event) program.artifact)
        fuel result.2.1 next.2 result.2.2 := by
  letI := runtime certificate
  apply EmittedBasicBlock.runProgramOutcomeLoop_block
    (certificate.layout.emitted certificate.entryPoint.block certificate.entryInGraph)
    certificate.layout.indexedLayout certificate.entryPoint.state certificate.entryPoint.accepted
  exact certificate.realizes certificate.entryPoint.block certificate.entryInGraph
    certificate.entryPoint.state certificate.entryPoint.accepted

/-- Apply the bridge's production execution theorem to a block reached from
    that same loaded entry.  `finish.state` is the predecessor-produced typed
    control point in `reachable`; callers cannot substitute a fresh state. -/
theorem runReachableBlock
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    {finish : BlockControlPoint X86_64 BlockId}
    (reachable : TypedControlFlowGraph.Reachable graph certificate.entryPoint finish)
    (fuel : Nat) (eventsRev : List Event) :
    letI := runtime certificate
    let result := finish.block.body finish.state finish.accepted
    let next := nativeOutcomeTransition
      (certificate.layout.emitted finish.block
        (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable)).terminatorInstruction
      (runLocalSteps
        (certificate.layout.emitted finish.block
          (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable)).bodyCode
        finish.state.machine) eventsRev
    runProgramOutcomeLoop
        (NativeX86_64Profile.instructionIndex (P := P) (Event := Event) program.artifact)
        ((certificate.layout.emitted finish.block
          (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable)).bodyCode.length +
          (fuel + 1)) finish.state.machine eventsRev =
      resumeAfterTerminator
        (NativeX86_64Profile.instructionIndex (P := P) (Event := Event) program.artifact)
        fuel result.2.1 next.2 result.2.2 := by
  letI := runtime certificate
  apply EmittedBasicBlock.runProgramOutcomeLoop_block
    (certificate.layout.emitted finish.block
      (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable))
    certificate.layout.indexedLayout finish.state finish.accepted
  exact certificate.realizes finish.block
    (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable)
    finish.state finish.accepted

end VerifiedProgramCFGArtifactCertificate

end Gasm.Targets.X86_64

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
/-- The only x86-64 native targets admitted by this bridge.  This closed
    choice deliberately has no payload: clients can select Linux or Windows,
    but cannot attach a replacement text extractor, load address, or runtime
    equation to either target. -/
inductive NativeX86_64Target (Event : Type) where
  | linux : NativeX86_64Target Event
  | windows : NativeX86_64Target Event

namespace NativeX86_64Target

/-- The platform fixed by a closed native target choice. -/
def PlatformOf {Event : Type} : NativeX86_64Target Event → Type
  | .linux => LinuxX86_64 Event
  | .windows => WindowsX86_64 Event

@[instance_reducible] instance platformOf {Event : Type} (target : NativeX86_64Target Event) :
    Platform (PlatformOf target) :=
  match target with
  | .linux => inferInstanceAs (Platform (LinuxX86_64 Event))
  | .windows => inferInstanceAs (Platform (WindowsX86_64 Event))

/-- The closed targets share the concrete x86-64 machine-state representation. -/
theorem machineState {Event : Type} (target : NativeX86_64Target Event) :
    Platform.State (P := PlatformOf target) = X86_64MachineState := by
  cases target <;> rfl

/-- The closed targets use a native runtime containing both the x86-64 host-call interceptor and
    the caller-selected finite execution policy. -/
theorem runtimeContext {Event : Type} (target : NativeX86_64Target Event) :
    Platform.RuntimeContext (P := PlatformOf target) = NativeX86_64Runtime Event := by
  cases target <;> rfl

/-- The closed targets expose a classification-preserving native observation, including explicit
    fuel exhaustion and fault rather than an event-list projection. -/
theorem observation {Event : Type} (target : NativeX86_64Target Event) :
    Platform.Observation (P := PlatformOf target) = NativeObservable Event := by
  cases target <;> rfl

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Extract the only linked text accepted by a closed target.  Its base is the
    executable loader RIP and therefore cannot be shifted independently of
    `Platform.load`. -/
def linkedText {Event : Type} (target : NativeX86_64Target Event) :
    Platform.Artifact (P := PlatformOf target) → CFGLinker.LinkedText :=
  match target with
  | .linux => fun artifact =>
      { base := artifact.executable.load.rip, instructions := artifact.instructions }
  | .windows => fun artifact =>
      { base := artifact.executable.load.rip, instructions := artifact.instructions }

/-- The runtime interceptor consumed by native step semantics is extracted from the exact
    platform runtime context.  Its selected execution policy remains in the context and is used
    by the whole-program runner below. -/
@[instance_reducible] def runtimeOf {Event : Type} (target : NativeX86_64Target Event)
    (runtime : Platform.RuntimeContext (P := PlatformOf target)) :
    ExternalCallInterceptor X86_64 Event :=
  (cast (runtimeContext target) runtime).interceptor

/-- Extract the finite policy selected with the exact platform runtime context. -/
def proofBudgetOf {Event : Type} (target : NativeX86_64Target Event)
    (runtime : Platform.RuntimeContext (P := PlatformOf target)) : NativeProofBudget :=
  (cast (runtimeContext target) runtime).proofBudget

/-- The production instruction index is a projection of the exact artifact
    through the closed target extractor. -/
def instructionIndex {Event : Type} (target : NativeX86_64Target Event)
    (artifact : Platform.Artifact (P := PlatformOf target)) :
    List (UInt64 × X86_64Instr) :=
  (linkedText target artifact).indexed

/-- The target-owned production runner is fixed to the artifact's own
    instruction sequence.  The connectedness premise is retained at the
    boundary so execution cannot be claimed for an unconnected artifact. -/
theorem runFromConnected {Event : Type} (target : NativeX86_64Target Event)
    (runtime : Platform.RuntimeContext (P := PlatformOf target))
    (artifact : Platform.Artifact (P := PlatformOf target))
    (_connected : Platform.artifactConnected artifact)
    (state : X86_64MachineState) :
    Platform.run runtime artifact (cast (machineState target).symm state) =
      cast (observation target).symm
        (letI : ExternalCallInterceptor X86_64 Event := runtimeOf target runtime
         (runProgramOutcomeWithLoops (Event := Event) state.rip
           (linkedText target artifact).instructions
           (proofBudgetOf target runtime).evaluatorFuel state).observable) := by
  cases target <;> rfl

/-- Closed-target runtime derivation preserves the platform support predicate. -/
theorem runtimeOf_supports {Event : Type} (target : NativeX86_64Target Event)
    (runtime : Platform.RuntimeContext (P := PlatformOf target))
    (artifact : Platform.Artifact (P := PlatformOf target))
    (provider : Platform.Provider (P := PlatformOf target))
    (supported : Platform.runtimeSupports runtime artifact provider) :
    Platform.runtimeSupports runtime artifact provider := supported

/-- Capability realization remains the one runtime used by the closed target. -/
theorem runtimeOf_realize {Event : Type} (target : NativeX86_64Target Event)
    (capabilities : CapabilityComposition (PlatformOf target))
    (artifact : Platform.Artifact (P := PlatformOf target))
    (context : capabilities.root.Context) :
    runtimeOf target (capabilities.realize artifact context) =
      (cast (runtimeContext target) (capabilities.realize artifact context)).interceptor := by
  simp [runtimeOf]

end NativeX86_64Target

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- A whole-CFG realization pinned to one `VerifiedProgram`, one environment,
    its exact final artifact, and the runtime context that the program itself
    establishes for that environment.  `layout`, `emitted`, and `realizes`
    are the existing target bridge obligations; all program/export/provider
    facts are projections of the sole whole-program authority rather than
    independently supplied claims. -/
structure VerifiedProgramCFGArtifactCertificate
    {Event : Type} (target : NativeX86_64Target Event)
    {capabilities : CapabilityComposition (NativeX86_64Target.PlatformOf target)}
    (program : VerifiedProgram (NativeX86_64Target.PlatformOf target) capabilities)
    (environment : Environment)
    (graph : TypedControlFlowGraph X86_64 BlockId) where
  layout : CFGLinker.ClosedCFGLayout graph
    (NativeX86_64Target.linkedText target program.artifact)
  realizes : ∀ (block : BasicBlock X86_64 BlockId) (member : block ∈ graph.blocks)
    (state : ComposedState X86_64 block.entry.State) (accepted : block.entry.accepts state),
    @EmittedBasicBlock.RealizesAt Event Unit BlockId
      (NativeX86_64Target.runtimeOf target
        (capabilities.realize program.artifact (program.entryContext environment)))
      (fun _ : Unit => NativeX86_64Target.instructionIndex target program.artifact) ()
      block (layout.emitted block member) state accepted
  /-- Exact, loaded control point for this graph.  Its machine state is the
      platform loader state for this program/environment; the remaining
      composed-state resources are fixed by the entry contract rather than
      invented by a path theorem. -/
  entryPoint : BlockControlPoint X86_64 BlockId
  entryInGraph : entryPoint.block ∈ graph.blocks
  entryExact : entryPoint.block.entry = graph.entry
  entryLoadedState :
    cast (NativeX86_64Target.machineState target).symm entryPoint.state.machine =
      Platform.load program.artifact environment

namespace VerifiedProgramCFGArtifactCertificate

variable {Event : Type} {target : NativeX86_64Target Event}
  {capabilities : CapabilityComposition (NativeX86_64Target.PlatformOf target)}
  {program : VerifiedProgram (NativeX86_64Target.PlatformOf target) capabilities}
  {environment : Environment}
  {graph : TypedControlFlowGraph X86_64 BlockId}

/-- The concrete runtime used by this CFG certificate is exactly the runtime
    realized from the program's own entry context for its fixed environment. -/
@[instance_reducible] def runtime (_certificate :
    VerifiedProgramCFGArtifactCertificate target program environment graph) :
    ExternalCallInterceptor X86_64 Event :=
  NativeX86_64Target.runtimeOf target
    (capabilities.realize program.artifact (program.entryContext environment))

/-- Reassemble the existing graph-wide operational bridge without introducing
    a second control-flow authority. -/
def operational (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    letI : ExternalCallInterceptor X86_64 Event := runtime certificate
    OperationalCFGRealization (Event := Event)
      (fun _ : Unit => NativeX86_64Target.instructionIndex target program.artifact) () graph := by
  letI : ExternalCallInterceptor X86_64 Event := runtime certificate
  exact {
    layout := certificate.layout.indexedLayout
    emitted := certificate.layout.emitted
    realizes := certificate.realizes }

/-- The final-artifact connection is the one stored in the sole
    `VerifiedProgram`; a CFG client cannot replace its artifact. -/
theorem artifactConnected
    (_certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    Platform.artifactConnected program.artifact :=
  program.artifactConnection

/-- Exact public export evidence for the same program artifact. -/
def artifactCertificate
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    ProgramArtifactCertificate (NativeX86_64Target.PlatformOf target) where
  artifact := program.artifact
  exports := program.exports
  exportsArtifact := program.exportsArtifact
  artifactConnection := certificate.artifactConnected

/-- Every selected provider is linked to the exact artifact that supplies the
    certificate's instruction index. -/
theorem providerLinked
    (_certificate : VerifiedProgramCFGArtifactCertificate target program environment graph)
    (provider : Platform.Provider (P := NativeX86_64Target.PlatformOf target))
    (selected : provider ∈ capabilities.root.providers) :
    Platform.providerLinked program.artifact provider :=
  program.providersLinked provider selected

/-- The exact realized runtime supports every provider selected by the program
    on the same final artifact. -/
theorem runtimeSupportsProvider
    (_certificate : VerifiedProgramCFGArtifactCertificate target program environment graph)
    (provider : Platform.Provider (P := NativeX86_64Target.PlatformOf target))
    (selected : provider ∈ capabilities.root.providers) :
    Platform.runtimeSupports
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact provider :=
  capabilities.realizeSupports (program.entryContext environment) program.artifact provider
    selected (program.providersLinked provider selected)

/-- Provider support is retained for the exact realized native runtime.  The CFG bridge extracts
    only its interceptor for local steps; it does not manufacture a second runtime or policy. -/
theorem operationalRuntimeSupportsProvider
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph)
    (provider : Platform.Provider (P := NativeX86_64Target.PlatformOf target))
    (selected : provider ∈ capabilities.root.providers) :
    Platform.runtimeSupports
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact provider :=
  NativeX86_64Target.runtimeOf_supports target
    (capabilities.realize program.artifact (program.entryContext environment))
    program.artifact provider
    (capabilities.realizeSupports (program.entryContext environment) program.artifact provider
      selected (program.providersLinked provider selected))

/-- The interceptor consumed by the bridge is the interceptor selected by the program's exact
    realized native runtime. -/
theorem operationalRuntimeIsRealized
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    runtime certificate =
      (cast (NativeX86_64Target.runtimeContext target)
        (capabilities.realize program.artifact (program.entryContext environment))).interceptor :=
  NativeX86_64Target.runtimeOf_realize target capabilities
    program.artifact (program.entryContext environment)

/-- The environment is fixed in the certificate, so the program's entry proof
    establishes precisely the runtime context used by `operational`. -/
theorem entryEstablished
    (_certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    capabilities.root.establishes program.artifact environment
      (Platform.load program.artifact environment) (program.entryContext environment) :=
  program.entryEstablished environment

/-- The platform safety predicate applies to the same artifact, environment,
    and realized runtime—not to an edge-local existential profile. -/
theorem platformAdmissible
    (_certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    Platform.admissible
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact (Platform.load program.artifact environment) :=
  program.platformAdmissible environment

/-- The certificate's entry control point is published by the graph and uses
    the exact graph entry contract. -/
theorem entryPublished
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    graph.Contains certificate.entryPoint :=
  certificate.entryInGraph

/-- The published control point is the graph's designated entry block. -/
theorem entryIsGraphEntry
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    certificate.entryPoint.block.entry = graph.entry :=
  certificate.entryExact

/-- The loaded entry state satisfies the exact entry predicate, not merely an
    existentially chosen block predicate. -/
theorem entryAccepted
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    certificate.entryPoint.block.entry.accepts certificate.entryPoint.state :=
  certificate.entryPoint.accepted

/-- The entry control point's machine component is exactly the platform loader
    result for the fixed closed target. -/
theorem entryStateIsLoaded
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    cast (NativeX86_64Target.machineState target).symm certificate.entryPoint.state.machine =
      Platform.load program.artifact environment :=
  certificate.entryLoadedState

/-- Production execution of a connected artifact is fixed by the closed
    target's target-owned law.  It consumes the program's selected runtime,
    artifact connection, and loaded machine state together. -/
theorem runLoadedMachineExact
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph) :
    Platform.run
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact (Platform.load program.artifact environment) =
      cast (NativeX86_64Target.observation target).symm
        (letI : ExternalCallInterceptor X86_64 Event := runtime certificate
         (runProgramOutcomeWithLoops (Event := Event)
           certificate.entryPoint.state.machine.rip
           (NativeX86_64Target.linkedText target program.artifact).instructions
           (NativeX86_64Target.proofBudgetOf target
             (capabilities.realize program.artifact (program.entryContext environment))).evaluatorFuel
           certificate.entryPoint.state.machine).observable) := by
  rw [← certificate.entryLoadedState]
  exact NativeX86_64Target.runFromConnected target
    (capabilities.realize program.artifact (program.entryContext environment))
    program.artifact program.artifactConnection certificate.entryPoint.state.machine

/-- Any point reached from the exact loaded entry through the typed graph is a
    published block, so its *path-carried* control point is covered by the
    same artifact-bound realization.  No fresh target state is accepted here.
    This is terminator-agnostic: direct, indirect, conditional, and future
    effectful terminators remain within the one graph closure rather than
    carrying edge-local artifact/profile existentials. -/
theorem realizesReachable
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph)
    {finish : BlockControlPoint X86_64 BlockId}
    (reachable : TypedControlFlowGraph.Reachable graph certificate.entryPoint finish) :
    @EmittedBasicBlock.RealizesAt Event Unit BlockId (runtime certificate)
      (fun _ : Unit => NativeX86_64Target.instructionIndex target program.artifact) ()
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
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph)
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
        (NativeX86_64Target.instructionIndex target program.artifact)
        ((certificate.layout.emitted certificate.entryPoint.block certificate.entryInGraph).bodyCode.length +
          (fuel + 1)) certificate.entryPoint.state.machine eventsRev =
      resumeAfterTerminator
        (NativeX86_64Target.instructionIndex target program.artifact)
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
    (certificate : VerifiedProgramCFGArtifactCertificate target program environment graph)
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
        (NativeX86_64Target.instructionIndex target program.artifact)
        ((certificate.layout.emitted finish.block
          (TypedControlFlowGraph.reachable_preserves_membership certificate.entryInGraph reachable)).bodyCode.length +
          (fuel + 1)) finish.state.machine eventsRev =
      resumeAfterTerminator
        (NativeX86_64Target.instructionIndex target program.artifact)
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

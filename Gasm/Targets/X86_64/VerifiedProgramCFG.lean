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
/-- Target-owned extraction of the final linked text for a native x86-64
    platform profile.  This is not an artifact connection supplied by a CFG
    client: the platform fixes the exact artifact projection. -/
class NativeX86_64Profile (P : Type) (Event : Type) [Platform P] where
  linkedText : Platform.Artifact (P := P) → CFGLinker.LinkedText
  runtimeOf : Platform.RuntimeContext (P := P) → ExternalCallInterceptor X86_64 Event

/-- The production instruction index of the target-owned linked text.  The
    index is a projection of the artifact, not an argument accepted from a CFG
    client. -/
def NativeX86_64Profile.instructionIndex {P Event : Type} [Platform P]
    [NativeX86_64Profile P Event] (artifact : Platform.Artifact (P := P)) :
    List (UInt64 × X86_64Instr) :=
  (NativeX86_64Profile.linkedText (P := P) (Event := Event) artifact).indexed

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The Linux target's instruction index is extracted directly from the exact
    artifact published by its platform profile. -/
instance linuxNativeX86_64Profile {Event : Type} :
    NativeX86_64Profile (LinuxX86_64 Event) Event where
  linkedText := fun artifact =>
    { base := artifact.executable.load.rip, instructions := artifact.instructions }
  runtimeOf := id

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The Windows target's instruction index is extracted directly from the exact
    PE artifact published by its platform profile. -/
instance windowsNativeX86_64Profile {Event : Type} :
    NativeX86_64Profile (WindowsX86_64 Event) Event where
  linkedText := fun artifact =>
    { base := artifact.executable.load.rip, instructions := artifact.instructions }
  runtimeOf := id

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

/-- Linux production execution of the exact artifact selected by the
    certificate.  This is a target equation, not an equality accepted from a
    CFG client. -/
theorem linuxRunExact {Event : Type}
    {capabilities : CapabilityComposition (LinuxX86_64 Event)}
    {program : VerifiedProgram (LinuxX86_64 Event) capabilities}
    {environment : Environment} {graph : TypedControlFlowGraph X86_64 BlockId}
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event)
      program environment graph)
    (state : X86_64MachineState) :
    Platform.run
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact state =
      letI := runtime certificate
      (runProgramOutcomeWithLoops (Event := Event) state.rip
        program.artifact.instructions 50000 state).events := by
  rfl

/-- Windows production execution of the exact artifact selected by the
    certificate.  This is a target equation, not an equality accepted from a
    CFG client. -/
theorem windowsRunExact {Event : Type}
    {capabilities : CapabilityComposition (WindowsX86_64 Event)}
    {program : VerifiedProgram (WindowsX86_64 Event) capabilities}
    {environment : Environment} {graph : TypedControlFlowGraph X86_64 BlockId}
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event)
      program environment graph)
    (state : X86_64MachineState) :
    Platform.run
      (capabilities.realize program.artifact (program.entryContext environment))
      program.artifact state =
      letI := runtime certificate
      (runProgramOutcomeWithLoops (Event := Event) state.rip
        program.artifact.instructions 50000 state).events := by
  rfl

/-- Any point reached through the typed graph is a published block, so its
    body is covered by the same artifact-bound realization.  This is
    terminator-agnostic: direct, indirect, conditional, and future effectful
    terminators all remain within the one graph closure rather than carrying
    edge-local artifact/profile existentials. -/
theorem realizesReachable
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    {start finish : BlockControlPoint X86_64 BlockId}
    (startInGraph : graph.Contains start)
    (reachable : TypedControlFlowGraph.Reachable graph start finish)
    (state : ComposedState X86_64 finish.block.entry.State)
    (accepted : finish.block.entry.accepts state) :
    @EmittedBasicBlock.RealizesAt Event Unit BlockId (runtime certificate)
      (fun _ : Unit => NativeX86_64Profile.instructionIndex (P := P) (Event := Event)
        program.artifact) ()
      finish.block
      (certificate.layout.emitted finish.block
        (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable))
      state accepted :=
  by
    letI := runtime certificate
    exact certificate.realizes finish.block
      (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable) state accepted

/-- Apply the bridge's production execution theorem to any reachable block,
    retaining the exact program artifact/index/runtime selected above. -/
theorem runReachableBlock
    (certificate : VerifiedProgramCFGArtifactCertificate (Event := Event) program environment graph)
    {start finish : BlockControlPoint X86_64 BlockId}
    (startInGraph : graph.Contains start)
    (reachable : TypedControlFlowGraph.Reachable graph start finish)
    (state : ComposedState X86_64 finish.block.entry.State)
    (accepted : finish.block.entry.accepts state)
    (fuel : Nat) (eventsRev : List Event) :
    letI := runtime certificate
    let result := finish.block.body state accepted
    let next := nativeOutcomeTransition
      (certificate.layout.emitted finish.block
        (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable)).terminatorInstruction
      (runLocalSteps
        (certificate.layout.emitted finish.block
          (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable)).bodyCode
        state.machine) eventsRev
    runProgramOutcomeLoop
        (NativeX86_64Profile.instructionIndex (P := P) (Event := Event) program.artifact)
        ((certificate.layout.emitted finish.block
          (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable)).bodyCode.length +
          (fuel + 1)) state.machine eventsRev =
      resumeAfterTerminator
        (NativeX86_64Profile.instructionIndex (P := P) (Event := Event) program.artifact)
        fuel result.2.1 next.2 result.2.2 := by
  letI := runtime certificate
  apply EmittedBasicBlock.runProgramOutcomeLoop_block
    (certificate.layout.emitted finish.block
      (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable))
    certificate.layout.indexedLayout state accepted
  exact certificate.realizes finish.block
    (TypedControlFlowGraph.reachable_preserves_membership startInGraph reachable) state accepted

end VerifiedProgramCFGArtifactCertificate

end Gasm.Targets.X86_64

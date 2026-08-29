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
import Gasm.Core.Types
import Gasm.Core.Verification
import Gasm.Effects.Inject
import Gasm.Effects.Trace
import Gasm.Targets.AArch64.Instructions.Base
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.Linux.Linker
import Gasm.Targets.Dispatcher
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.AArch64Linux.Program

namespace Spikes.Spike1Hello.AArch64Linux

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Linux

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered static Linux ELF64 execution on AArch64. -/
theorem spike1_aarch64_linux_canonical_effect_trace_equivalence :
    (runAArch64Trace (Event := AnyEvent) spike1AArch64LinuxInstructions spike1AArch64LinuxExecutable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  set_option maxRecDepth 4000 in
  decide

theorem spike1_aarch64_linux_selected_termination :
    selectedExecutionTerminates (Event := AnyEvent) selectedNonInputAArch64LinuxCall
      (indexInstructions spike1AArch64LinuxExecutable.load.pc
        spike1AArch64LinuxInstructions) 50000
      spike1AArch64LinuxExecutable.load = true := by
  rfl

def spike1AArch64LinuxTerminationCertificate :
    SelectedTerminationCertificate (Event := AnyEvent) selectedNonInputAArch64LinuxCall
      spike1AArch64LinuxExecutable.load.pc spike1AArch64LinuxInstructions
      spike1AArch64LinuxExecutable.load where
  fuel := 50000
  verifies := spike1_aarch64_linux_selected_termination

theorem spike1_aarch64_linux_outcome_external_input_frame (environment : Environment) :
    runAArch64Outcome (Event := AnyEvent) spike1AArch64LinuxExecutable.load.pc
        spike1AArch64LinuxInstructions 50000
        (spike1AArch64LinuxExecutable.load.withExternalInputs environment.stdin
          environment.incomingRequests) =
      (runAArch64Outcome (Event := AnyEvent) spike1AArch64LinuxExecutable.load.pc
        spike1AArch64LinuxInstructions 50000 spike1AArch64LinuxExecutable.load).withExternalInputs
          environment.stdin environment.incomingRequests := by
  exact spike1AArch64LinuxTerminationCertificate.externalInputFrame
    aarch64LinuxCallInterceptor_preserves_selected_external_input_frame
    environment.stdin environment.incomingRequests

theorem spike1_aarch64_linux_trace_external_input_frame (environment : Environment) :
    runAArch64Trace (Event := AnyEvent) spike1AArch64LinuxInstructions
        (spike1AArch64LinuxExecutable.load.withExternalInputs environment.stdin
          environment.incomingRequests) =
      runAArch64Trace (Event := AnyEvent) spike1AArch64LinuxInstructions
        spike1AArch64LinuxExecutable.load := by
  have hout := congrArg AArch64RunOutcome.events
    (spike1_aarch64_linux_outcome_external_input_frame environment)
  simp only [AArch64RunOutcome.withExternalInputs_events] at hout
  simpa [runAArch64Trace, runAArch64Outcome_events] using hout

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Complete AArch64 Linux artifact whose emitted bytes and operational instructions are tied. -/
def spike1AArch64LinuxArtifact : LinuxAArch64Artifact := {
  executable := spike1AArch64LinuxExecutable
  instructions := spike1AArch64LinuxInstructions
}

def spike1AArch64LinuxArtifactCertificate :
    ProgramArtifactCertificate (LinuxAArch64 AnyEvent) where
  artifact := spike1AArch64LinuxArtifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := by rfl

def spike1AArch64LinuxProviderCertificate :
    ProgramProviderCertificate (LinuxAArch64 AnyEvent)
      (aarch64LinuxHostCapabilities AnyEvent) spike1AArch64LinuxArtifact where
  importsCovered := by
    intro imported himported
    change imported ∈ ([] : List Unit) at himported
    contradiction
  providersLinked := by
    intro provider
    exact nomatch provider

def spike1AArch64LinuxEntryCertificate :
    ProgramEntryCertificate (LinuxAArch64 AnyEvent)
      (aarch64LinuxHostCapabilities AnyEvent) spike1AArch64LinuxArtifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

def spike1AArch64LinuxAdmissibilityCertificate :
    ProgramAdmissibilityCertificate (LinuxAArch64 AnyEvent)
      (aarch64LinuxHostCapabilities AnyEvent) spike1AArch64LinuxArtifact
      spike1AArch64LinuxEntryCertificate where
  platformAdmissible := by
    intro environment
    change (runAArch64Outcome (Event := AnyEvent) spike1AArch64LinuxExecutable.load.pc
      spike1AArch64LinuxInstructions 50000
      (spike1AArch64LinuxExecutable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible
    rw [spike1_aarch64_linux_outcome_external_input_frame]
    simp only [AArch64RunOutcome.withExternalInputs_isAdmissible]
    exact spike1AArch64LinuxTerminationCertificate.isAdmissible
      (selected := selectedNonInputAArch64LinuxCall)

def spike1AArch64LinuxBehaviorCertificate :
    ProgramBehaviorCertificate (LinuxAArch64 AnyEvent)
      (aarch64LinuxHostCapabilities AnyEvent) spike1AArch64LinuxArtifact
      spike1AArch64LinuxEntryCertificate where
  spec := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  traceEquivalence := by
    intro environment
    change runAArch64Trace (Event := AnyEvent) spike1AArch64LinuxInstructions
      (spike1AArch64LinuxExecutable.load.withExternalInputs environment.stdin
        environment.incomingRequests) = _
    rw [spike1_aarch64_linux_trace_external_input_frame]
    have h := spike1_aarch64_linux_canonical_effect_trace_equivalence
    simpa only [beq_iff_eq] using h

/-- Sole universal whole-program contract for Spike 1 AArch64 Linux Hello World. -/
def spike1AArch64LinuxVerifiedProgram :
    VerifiedProgram (LinuxAArch64 AnyEvent) (aarch64LinuxHostCapabilities AnyEvent) :=
  VerifiedProgram.compose "Spike 1: Linux AArch64 Hello World"
    spike1AArch64LinuxArtifactCertificate spike1AArch64LinuxProviderCertificate
    spike1AArch64LinuxEntryCertificate spike1AArch64LinuxAdmissibilityCertificate
    spike1AArch64LinuxBehaviorCertificate

end Spikes.Spike1Hello.AArch64Linux

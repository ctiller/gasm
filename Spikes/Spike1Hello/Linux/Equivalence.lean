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
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.Linux.Linker
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.Linux.Program

namespace Spikes.Spike1Hello.Linux

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.Linux

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered machine execution on Linux. -/
theorem spike1_canonical_effect_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike1Instructions spike1Executable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Spike 1 supplies an explicit evaluator proof bound.  It is not a runtime resource policy;
    the artifact proves its typed process exit before this bound is exhausted. -/
def spike1LinuxProofBudget : NativeProofBudget :=
  { evaluatorFuel := 50000 }

theorem spike1_selected_termination :
    selectedExecutionTerminates (Event := AnyEvent) false selectedNonInputPlatformCall
      (indexInstructions spike1Executable.load.rip spike1Instructions)
      spike1LinuxProofBudget.evaluatorFuel
      spike1Executable.load = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The canonical finite execution reaches Linux's typed process-exit outcome.  The
    observable keeps that terminal classification alongside the output trace. -/
theorem spike1_canonical_observable :
    (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
      spike1Instructions spike1LinuxProofBudget.evaluatorFuel spike1Executable.load).observable =
      .processExited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) := by
  decide

def spike1TerminationCertificate :
    SelectedTerminationCertificate (Event := AnyEvent) false selectedNonInputPlatformCall
      spike1Executable.load.rip spike1Instructions spike1Executable.load where
  fuel := spike1LinuxProofBudget.evaluatorFuel
  verifies := spike1_selected_termination

theorem spike1_outcome_external_input_frame (environment : Environment) :
    runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
        spike1Instructions spike1LinuxProofBudget.evaluatorFuel
        (spike1Executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
        spike1Instructions spike1LinuxProofBudget.evaluatorFuel spike1Executable.load).withExternalInputs
          environment.stdin environment.incomingRequests := by
  exact spike1TerminationCertificate.externalInputFrame
    (fun instr _ => instruction_preserves_external_input_frame instr)
    platformCallInterceptor_preserves_selected_external_input_frame
    environment.stdin environment.incomingRequests

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Complete Linux artifact whose emitted bytes and operational instructions are tied together. -/
def spike1LinuxArtifact : LinuxX86_64Artifact := {
  executable := spike1Executable
  instructions := spike1Instructions
}

def spike1LinuxArtifactCertificate :
    ProgramArtifactCertificate (LinuxX86_64 AnyEvent) where
  artifact := spike1LinuxArtifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := by rfl

def spike1LinuxProviderCertificate :
    ProgramProviderCertificate (LinuxX86_64 AnyEvent)
      (linuxHostCapabilities AnyEvent spike1LinuxProofBudget) spike1LinuxArtifact where
  importsCovered := by
    intro imported h
    change imported ∈ [] at h
    contradiction
  providersLinked := by
    intro provider h
    change provider ∈ [] at h
    contradiction

def spike1LinuxEntryCertificate :
    ProgramEntryCertificate (LinuxX86_64 AnyEvent)
      (linuxHostCapabilities AnyEvent spike1LinuxProofBudget) spike1LinuxArtifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

def spike1LinuxAdmissibilityCertificate :
    ProgramAdmissibilityCertificate (LinuxX86_64 AnyEvent)
      (linuxHostCapabilities AnyEvent spike1LinuxProofBudget) spike1LinuxArtifact
      spike1LinuxEntryCertificate where
  platformAdmissible := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
      spike1Instructions spike1LinuxProofBudget.evaluatorFuel
      (spike1Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible false
    rw [spike1_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    exact spike1TerminationCertificate.isAdmissible

def spike1LinuxBehaviorCertificate :
    ProgramBehaviorCertificate (LinuxX86_64 AnyEvent)
      (linuxHostCapabilities AnyEvent spike1LinuxProofBudget) spike1LinuxArtifact
      spike1LinuxEntryCertificate where
  spec := fun _ => .processExited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit))
  traceEquivalence := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
      spike1Instructions spike1LinuxProofBudget.evaluatorFuel
      (spike1Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).observable =
      .processExited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit))
    rw [spike1_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_observable]
    exact spike1_canonical_observable

/-- Sole universal whole-program contract for Spike 1 (Linux Hello World). -/
def spike1VerifiedProgram :
    VerifiedProgram (LinuxX86_64 AnyEvent) (linuxHostCapabilities AnyEvent spike1LinuxProofBudget) :=
  VerifiedProgram.compose "Spike 1: Linux Hello World"
    spike1LinuxArtifactCertificate spike1LinuxProviderCertificate
    spike1LinuxEntryCertificate spike1LinuxAdmissibilityCertificate
    spike1LinuxBehaviorCertificate

end Spikes.Spike1Hello.Linux

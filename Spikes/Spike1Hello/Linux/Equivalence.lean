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

theorem spike1_selected_termination :
    selectedExecutionTerminates (Event := AnyEvent) true selectedNonInputPlatformCall
      (indexInstructions spike1Executable.load.rip spike1Instructions) 50000
      spike1Executable.load = true := by
  decide

def spike1TerminationCertificate :
    SelectedTerminationCertificate (Event := AnyEvent) true selectedNonInputPlatformCall
      spike1Executable.load.rip spike1Instructions spike1Executable.load where
  fuel := 50000
  verifies := spike1_selected_termination

theorem spike1_outcome_external_input_frame (environment : Environment) :
    runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
        spike1Instructions 50000
        (spike1Executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
        spike1Instructions 50000 spike1Executable.load).withExternalInputs
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

/-- Sole universal whole-program contract for Spike 1 (Linux Hello World). -/
def spike1VerifiedProgram :
    VerifiedProgram (LinuxX86_64 AnyEvent) (linuxHostCapabilities AnyEvent) := {
  name             := "Spike 1: Linux Hello World"
  artifact         := spike1LinuxArtifact
  exports          := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact  := rfl
  artifactConnection := by rfl
  spec             := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  importsCovered   := by
    intro imported h
    change imported ∈ [] at h
    contradiction
  providersLinked := by
    intro provider h
    change provider ∈ [] at h
    contradiction
  entryContext     := fun _ => ()
  entryEstablished := by
    intro environment
    trivial
  platformAdmissible := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
      spike1Instructions 50000
      (spike1Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible true
    rw [spike1_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    exact spike1TerminationCertificate.isAdmissible
  traceEquivalence := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
      spike1Instructions 50000
      (spike1Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).events =
      runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
    rw [spike1_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_events]
    rw [runProgramOutcomeWithLoops_events]
    change runAsmTrace (Event := AnyEvent) spike1Instructions spike1Executable.load = _
    have h := spike1_canonical_effect_trace_equivalence
    simpa only [beq_iff_eq] using h
}

end Spikes.Spike1Hello.Linux

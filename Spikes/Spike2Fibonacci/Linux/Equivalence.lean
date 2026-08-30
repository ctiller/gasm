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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.Linux.Linker
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Linux.Program
import Spikes.Spike2Fibonacci.Linux.Row1
import Spikes.Spike2Fibonacci.Linux.DecimalLayout
import Spikes.Spike2Fibonacci.Linux.DecimalRuntime

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.Linux
open Spikes.Spike2Fibonacci

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Whole-program canonical effect trace equivalence for Linux Spike 2. -/
theorem spike2_canonical_effect_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load ==
     runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)) = true := by
  decide +kernel

theorem spike2_selected_termination :
    selectedExecutionTerminates (Event := AnyEvent) true selectedNonInputPlatformCall
      (indexInstructions spike2Executable.load.rip spike2Instructions) 50000
      spike2Executable.load = true := by
  native_decide

def spike2TerminationCertificate :
    SelectedTerminationCertificate (Event := AnyEvent) true selectedNonInputPlatformCall
      spike2Executable.load.rip spike2Instructions spike2Executable.load where
  fuel := 50000
  verifies := spike2_selected_termination

theorem spike2_outcome_external_input_frame (environment : Environment) :
    runProgramOutcomeWithLoops (Event := AnyEvent) spike2Executable.load.rip
        spike2Instructions 50000
        (spike2Executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (runProgramOutcomeWithLoops (Event := AnyEvent) spike2Executable.load.rip
        spike2Instructions 50000 spike2Executable.load).withExternalInputs
          environment.stdin environment.incomingRequests := by
  exact spike2TerminationCertificate.externalInputFrame
    (fun instr _ => instruction_preserves_external_input_frame instr)
    platformCallInterceptor_preserves_selected_external_input_frame
    environment.stdin environment.incomingRequests

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Complete Linux artifact whose emitted bytes and operational instructions are tied together. -/
def spike2LinuxArtifact : LinuxX86_64Artifact := {
  executable := spike2Executable
  instructions := spike2Instructions
}

/-- Sole universal whole-program contract for Spike 2 (Linux Fibonacci Driver). -/
def spike2VerifiedProgram :
    VerifiedProgram (LinuxX86_64 AnyEvent) (linuxHostCapabilities AnyEvent) := {
  name             := "Spike 2: Linux Fibonacci Driver"
  artifact         := spike2LinuxArtifact
  exports          := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact  := rfl
  artifactConnection := by rfl
  spec             := fun _ => runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)
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
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike2Executable.load.rip
      spike2Instructions 50000
      (spike2Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible true
    rw [spike2_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    exact spike2TerminationCertificate.isAdmissible
  traceEquivalence := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike2Executable.load.rip
      spike2Instructions 50000
      (spike2Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).events =
      runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)
    rw [spike2_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_events]
    rw [runProgramOutcomeWithLoops_events]
    change runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load = _
    have h := spike2_canonical_effect_trace_equivalence
    simpa only [beq_iff_eq] using h
}

end Spikes.Spike2Fibonacci.Linux

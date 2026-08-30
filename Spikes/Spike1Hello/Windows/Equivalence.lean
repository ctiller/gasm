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
import Gasm.Targets.Windows.Win32API
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.Windows.Program

namespace Spikes.Spike1Hello.Windows

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

local instance : ExternalCallInterceptor X86_64 AnyEvent :=
  standardWindowsRuntime AnyEvent

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered machine
    execution.

    **Oracle-debt retirement (2026-08-27): `native_decide` -> `decide`.** Spike 1 takes no input, so
    this is a closed-term claim (no `∀` to discharge) about one fixed program. Unlike the Wasm sibling
    of this theorem, `runAsmTrace` (`Gasm/Targets/X86_64/Semantics.lean`) is built entirely from
    ordinary structurally-recursive `def`s -- `runProgramTraceWithLoops` recurses on an explicit `Nat`
    fuel parameter, not `partial`, so it carries real kernel-unfoldable equations. `grep -rn "partial
    def" Gasm/Targets/X86_64 Gasm/Targets/Windows` returns nothing: there is no opaque interpreter
    core standing in the way here, so plain `decide` closes it directly with no oracle and no
    allowlist entry. -/
theorem spike1_canonical_effect_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike1Instructions spike1Executable.load ==
     runModelTrace (helloWorldWindowsSpec : TraceM AnyEvent Unit)) = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Spike 1 supplies an explicit evaluator proof bound rather than inheriting a target default. -/
def spike1WindowsProofBudget : NativeProofBudget :=
  { evaluatorFuel := 50000 }

/-- The concrete Spike 1 execution reaches only input-independent host boundaries and returns
    cleanly within the platform budget. -/
theorem spike1_selected_termination :
    selectedExecutionTerminates (Event := AnyEvent) false selectedNonInputWin32Call
      (indexInstructions spike1Executable.load.rip spike1Instructions)
      spike1WindowsProofBudget.evaluatorFuel
      spike1Executable.load = true := by
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The canonical finite execution reaches Win32's typed `ExitProcess` outcome. -/
theorem spike1_canonical_observable :
    (@runProgramOutcomeWithLoops AnyEvent (standardWindowsRuntime AnyEvent)
      spike1Executable.load.rip spike1Instructions spike1WindowsProofBudget.evaluatorFuel
      spike1Executable.load).observable =
      .processExited 0 (runModelTrace (helloWorldWindowsSpec : TraceM AnyEvent Unit)) := by
  decide

def spike1TerminationCertificate :
    SelectedTerminationCertificate (Event := AnyEvent) false selectedNonInputWin32Call
      spike1Executable.load.rip spike1Instructions spike1Executable.load where
  fuel := spike1WindowsProofBudget.evaluatorFuel
  verifies := spike1_selected_termination

theorem spike1_outcome_external_input_frame (environment : Environment) :
    runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
        spike1Instructions spike1WindowsProofBudget.evaluatorFuel
        (spike1Executable.load.withExternalInputs environment.stdin environment.incomingRequests) =
      (runProgramOutcomeWithLoops (Event := AnyEvent) spike1Executable.load.rip
        spike1Instructions spike1WindowsProofBudget.evaluatorFuel spike1Executable.load).withExternalInputs
          environment.stdin environment.incomingRequests := by
  exact spike1TerminationCertificate.externalInputFrame
    (fun instr _ => instruction_preserves_external_input_frame instr)
    (by
      intro address state stdin requests hselected
      exact win32CallIntercept_preserves_selected_external_input_frame
        address state stdin requests hselected)
    environment.stdin environment.incomingRequests

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Complete Windows artifact whose emitted bytes and operational instructions are tied together. -/
def spike1WindowsArtifact : WindowsX86_64Artifact := {
  executable := spike1Executable
  instructions := spike1Instructions
}

def spike1WindowsArtifactCertificate :
    ProgramArtifactCertificate (WindowsX86_64 AnyEvent) where
  artifact := spike1WindowsArtifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := by rfl

def spike1WindowsProviderCertificate :
    ProgramProviderCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike1WindowsProofBudget) spike1WindowsArtifact where
  importsCovered := by
    intro imported himported
    change imported ∈ [GetStdHandleDef, ReadFileDef, WriteFileDef, ExitProcessDef,
      VirtualAllocDef, VirtualFreeDef] at himported
    simp only [List.mem_cons, List.not_mem_nil, or_false] at himported
    rcases himported with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ⟨windowsProvider GetStdHandleDef 0 0, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider ReadFileDef 1 1, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider WriteFileDef 2 2, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider ExitProcessDef 3 3, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider VirtualAllocDef 4 4, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
      | exact ⟨windowsProvider VirtualFreeDef 5 5, by simp [standardWindowsHostCapabilities,
          standardWindowsProviders, windowsHostCapability], rfl⟩
  providersLinked := by
    intro provider hprovider
    simp only [standardWindowsHostCapabilities, standardWindowsProviders, windowsHostCapability,
      List.mem_cons, List.not_mem_nil, or_false] at hprovider
    rcases hprovider with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change (_ = _) ∧ _
      constructor
      · decide
      · rfl

def spike1WindowsEntryCertificate :
    ProgramEntryCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike1WindowsProofBudget) spike1WindowsArtifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

def spike1WindowsAdmissibilityCertificate :
    ProgramAdmissibilityCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike1WindowsProofBudget) spike1WindowsArtifact
      spike1WindowsEntryCertificate where
  platformAdmissible := by
    intro environment
    change (@runProgramOutcomeWithLoops AnyEvent (standardWindowsRuntime AnyEvent)
      spike1Executable.load.rip
      spike1Instructions spike1WindowsProofBudget.evaluatorFuel
      (spike1Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible false
    rw [spike1_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_isAdmissible]
    exact spike1TerminationCertificate.isAdmissible

def spike1WindowsBehaviorCertificate :
    ProgramBehaviorCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike1WindowsProofBudget) spike1WindowsArtifact
      spike1WindowsEntryCertificate where
  spec := fun _ => .processExited 0 (runModelTrace (helloWorldWindowsSpec : TraceM AnyEvent Unit))
  traceEquivalence := by
    intro environment
    change (@runProgramOutcomeWithLoops AnyEvent (standardWindowsRuntime AnyEvent)
      spike1Executable.load.rip
      spike1Instructions spike1WindowsProofBudget.evaluatorFuel
      (spike1Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).observable =
      .processExited 0 (runModelTrace (helloWorldWindowsSpec : TraceM AnyEvent Unit))
    rw [spike1_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_observable]
    exact spike1_canonical_observable

/-- Sole universal whole-program contract for Spike 1 (Windows Hello World). -/
def spike1VerifiedProgram :
    VerifiedProgram (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike1WindowsProofBudget) :=
  VerifiedProgram.compose "Spike 1: Windows Hello World"
    spike1WindowsArtifactCertificate spike1WindowsProviderCertificate
    spike1WindowsEntryCertificate spike1WindowsAdmissibilityCertificate
    spike1WindowsBehaviorCertificate

end Spikes.Spike1Hello.Windows

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
import Gasm.Targets.Windows.Win32API
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Windows.Program
import Spikes.Spike2Fibonacci.Windows.CanonicalTrace
import Spikes.Spike2Fibonacci.Windows.LoopInvariant
import Spikes.Spike2Fibonacci.Windows.RowTermination

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForEquivalence :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 200000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Simulates execution of the iterative assembly routine on an initial state with RCX = n via target subroutine invocation. -/
def runFibIterAsm (n : Nat) : UInt64 :=
  callSubroutine fibIterInstructions [n.toUInt64]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **PA15.** The x86-64 assembly routine computes exact Fibonacci numbers, for every `n` the
    default `callSubroutine` fuel budget (`1000`) can complete within (`n ≤ 124`: two prologue
    instructions plus eight per iteration plus a three-instruction exit, `8*124 + 5 = 997 ≤ 1000 <
    8*125 + 5`). Discharged by `fibLoopInvariant_prologue` (establishing the loop invariant) and
    `loop_correct` (induction on the iteration count via `fibLoop_iteration`/`fibLoop_done`) --
    a genuine structural argument, not `native_decide` enumerating concrete inputs.

    This is a *different, more general* fact than the theorem this replaces: the previous
    `(List.range 91).all (...) = true` was a finite check over `n = 0..90`. The bound here (`n ≤
    124`) is **not** the `UInt64`-overflow point the allowlist entry this replaces assumed was the
    relevant limit (`fib 93` is the last value that fits in 64 bits without wrapping) -- both sides
    of this equation wrap `UInt64` arithmetic identically (`Nat.toUInt64` distributes over `+`,
    checked as `by simp [Nat.toUInt64]` throughout the induction), so the equation holds
    *regardless* of `UInt64` overflow. The actual bound is the machine model's own fuel budget:
    `callSubroutine`'s default `1000` steps, which the routine exhausts partway through iteration
    125. A caller needing `n > 124` would need to pass a larger `fuel` to `callSubroutine`;
    `loop_correct` already supports that (it is stated for arbitrary `fuel ≥ 8*m + 3`), only this
    corollary fixes it at the default. -/
theorem fib_iter_asm_soundness (n : Nat) (hn : n ≤ 124) :
    runFibIterAsm n = (fibIter n).toUInt64 := by
  unfold runFibIterAsm callSubroutine
  obtain ⟨s2, hinv, heq⟩ := fibLoopInvariant_prologue n 998
  have h : (runProgramWithLoops 0x1000 fibIterInstructions 1000
      (initMachineState 0x1000 [n.toUInt64])).gprs .rax = (fibNat (0 + n)).toUInt64 := by
    rw [show (1000 : Nat) = 998 + 2 from rfl, heq]
    exact loop_correct 0 n 998 s2 hinv (by omega) (by omega)
  rw [h, show 0 + n = n from by omega, ← fibIter_eq_fibNat]

/-- Closed reference certificate: all reached host boundaries are input-independent and the
    complete 90-row driver returns before the platform budget is exhausted. -/
theorem spike2_selected_termination :
    selectedExecutionTerminates (Event := AnyEvent) false selectedNonInputPlatformCall
      (indexInstructions spike2Executable.load.rip spike2Instructions) 50000
      spike2Executable.load = true := by
  exact spike2_selected_termination_constructive_indexed

def spike2TerminationCertificate :
    SelectedTerminationCertificate (Event := AnyEvent) false selectedNonInputPlatformCall
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
    (by
      intro address state stdin requests selected
      exact win32CallIntercept_preserves_selected_external_input_frame
        address state stdin requests selected)
    environment.stdin environment.incomingRequests

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Complete Windows artifact whose emitted bytes and operational instructions are tied together. -/
def spike2WindowsArtifact : WindowsX86_64Artifact := {
  executable := spike2Executable
  instructions := spike2Instructions
}

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Spike 2's fixed platform evaluator budget.  Prefix certificates justify the used portion;
    unused fuel is admitted only after the typed `ExitProcess` transition. -/
def spike2WindowsProofBudget : NativeProofBudget :=
  { evaluatorFuel := 50000 }

/-- The compositional prefix proof determines both successful termination and the complete
    caller-visible observation under the exact Windows runtime used by the platform profile. -/
theorem spike2_canonical_observable :
    (@runProgramOutcomeWithLoops AnyEvent spike2WindowsRuntime
      spike2Executable.load.rip spike2Instructions spike2WindowsProofBudget.evaluatorFuel
      spike2Executable.load).observable =
      .processExited 0 (runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)) := by
  rcases spike2_selected_outcome_constructive with ⟨final, outcome⟩
  change (@runProgramOutcomeWithLoops AnyEvent spike2WindowsRuntime
    spike2Executable.load.rip spike2Instructions 50000 spike2Executable.load).observable = _
  rw [outcome, runModelTrace_fibonacciSpec, spike2ExpectedEventsRev_eq_reverse]
  change NativeObservable.processExited 0
      (fibonacciEventsFrom 1 90 ++ [Inject.inject (ProcessEvent.exit 0)]) = _
  rfl

def spike2WindowsArtifactCertificate :
    ProgramArtifactCertificate (WindowsX86_64 AnyEvent) where
  artifact := spike2WindowsArtifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := by rfl

def spike2WindowsProviderCertificate :
    ProgramProviderCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike2WindowsProofBudget) spike2WindowsArtifact where
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

def spike2WindowsEntryCertificate :
    ProgramEntryCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike2WindowsProofBudget) spike2WindowsArtifact where
  entryContext := fun _ => ()
  entryEstablished := by intro; trivial

def spike2WindowsAdmissibilityCertificate :
    ProgramAdmissibilityCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike2WindowsProofBudget) spike2WindowsArtifact
      spike2WindowsEntryCertificate where
  platformAdmissible := by
    intro environment
    rcases spike2_selected_outcome_constructive with ⟨final, outcome⟩
    apply windowsX86_64Admissible_of_execution
      (execution := (NativeRunOutcome.terminated (.processExit 0) final
        ((spike2ExpectedEventsRev 90).reverse ++
          [Inject.inject (ProcessEvent.exit 0)]) : NativeRunOutcome AnyEvent).withExternalInputs
            environment.stdin environment.incomingRequests)
    · change (@runProgramOutcomeWithLoops AnyEvent (standardWindowsRuntime AnyEvent)
        spike2Executable.load.rip spike2Instructions 50000
        (spike2Executable.load.withExternalInputs environment.stdin
          environment.incomingRequests)) = _
      rw [spike2_outcome_external_input_frame]
      rw [outcome]
    · exact (NativeRunOutcome.withExternalInputs_isAdmissible
        (outcome := (NativeRunOutcome.terminated (.processExit 0) final
          ((spike2ExpectedEventsRev 90).reverse ++
            [Inject.inject (ProcessEvent.exit 0)]) : NativeRunOutcome AnyEvent))
        false environment.stdin environment.incomingRequests).2 (by trivial)

def spike2WindowsBehaviorCertificate :
    ProgramBehaviorCertificate (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike2WindowsProofBudget) spike2WindowsArtifact
      spike2WindowsEntryCertificate where
  spec := fun _ => .processExited 0 (runModelTrace (fibonacciSpec : TraceM AnyEvent Unit))
  traceEquivalence := by
    intro environment
    change (@runProgramOutcomeWithLoops AnyEvent (standardWindowsRuntime AnyEvent)
      spike2Executable.load.rip spike2Instructions 50000
      (spike2Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).observable =
      .processExited 0 (runModelTrace (fibonacciSpec : TraceM AnyEvent Unit))
    rw [spike2_outcome_external_input_frame]
    simp only [NativeRunOutcome.withExternalInputs_observable]
    exact spike2_canonical_observable

/-- Sole universal whole-program contract for Spike 2 (Fibonacci Driver). -/
def spike2VerifiedProgram :
    VerifiedProgram (WindowsX86_64 AnyEvent)
      (standardWindowsHostCapabilities AnyEvent spike2WindowsProofBudget) :=
  VerifiedProgram.compose "Spike 2: Fibonacci Sequence Driver"
    spike2WindowsArtifactCertificate spike2WindowsProviderCertificate
    spike2WindowsEntryCertificate spike2WindowsAdmissibilityCertificate
    spike2WindowsBehaviorCertificate

end Spikes.Spike2Fibonacci.Windows

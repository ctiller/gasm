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
import Spikes.Spike2Fibonacci.Windows.LoopInvariant
import Spikes.Spike2Fibonacci.Windows.RowTermination

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

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

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Whole-program canonical effect trace equivalence for Spike 2. -/
theorem spike2_canonical_effect_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load ==
     runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)) = true := by
  decide +kernel

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
    platformCallInterceptor_preserves_selected_external_input_frame
    environment.stdin environment.incomingRequests

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Complete Windows artifact whose emitted bytes and operational instructions are tied together. -/
def spike2WindowsArtifact : WindowsX86_64Artifact := {
  executable := spike2Executable
  instructions := spike2Instructions
}

/-- Sole universal whole-program contract for Spike 2 (Fibonacci Driver). -/
def spike2VerifiedProgram :
    VerifiedProgram (WindowsX86_64 AnyEvent) (windowsHostCapabilities AnyEvent) := {
  name             := "Spike 2: Fibonacci Sequence Driver"
  artifact         := spike2WindowsArtifact
  exports          := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact  := rfl
  artifactConnection := by rfl
  spec             := fun _ => runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)
  importsCovered   := by
    intro imported _
    trivial
  providersLinked := by simp [windowsHostCapabilities, windowsHostCapability]
  entryContext     := fun _ => ()
  entryEstablished := by
    intro environment
    trivial
  platformAdmissible := by
    intro environment
    change (runProgramOutcomeWithLoops (Event := AnyEvent) spike2Executable.load.rip
      spike2Instructions 50000
      (spike2Executable.load.withExternalInputs environment.stdin
        environment.incomingRequests)).isAdmissible false
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

end Spikes.Spike2Fibonacci.Windows

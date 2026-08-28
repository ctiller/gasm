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

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
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
  native_decide

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedLinuxProgram contract instantiation for Spike 2 (Linux Fibonacci Driver). -/
def spike2VerifiedProgram : VerifiedLinuxProgram Unit AnyEvent := {
  name             := "Spike 2: Linux Fibonacci Driver"
  executable       := spike2Executable
  instructions     := spike2Instructions
  spec             := fun _ => runModelTrace (fibonacciSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike2_canonical_effect_trace_equivalence
}

end Spikes.Spike2Fibonacci.Linux

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
open Gasm.Targets.X86_64
open Gasm.Targets.Linux

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered machine execution on Linux. -/
theorem spike1_canonical_effect_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike1Instructions spike1Executable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  decide

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedLinuxProgram contract instantiation for Spike 1 (Linux Hello World). -/
def spike1VerifiedProgram : VerifiedLinuxProgram Unit AnyEvent := {
  name             := "Spike 1: Linux Hello World"
  executable       := spike1Executable
  instructions     := spike1Instructions
  spec             := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike1_canonical_effect_trace_equivalence
}

end Spikes.Spike1Hello.Linux

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
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Executable
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.BareMetal.Program

namespace Spikes.Spike1Hello.BareMetal

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.BareMetal

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered bare-metal execution. -/
theorem spike1_baremetal_canonical_effect_trace_equivalence :
    (runBareMetalTrace spike1BareMetalInstructions spike1BareMetalExecutable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  native_decide

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedBareMetalProgram contract instantiation for Spike 1 (Bare Metal Hello World). -/
def spike1VerifiedBareMetalProgram : VerifiedBareMetalProgram Unit AnyEvent := {
  name             := "Spike 1: Bare Metal x86-64 Hello World"
  executable       := spike1BareMetalExecutable
  instructions     := spike1BareMetalInstructions
  spec             := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike1_baremetal_canonical_effect_trace_equivalence
}

end Spikes.Spike1Hello.BareMetal

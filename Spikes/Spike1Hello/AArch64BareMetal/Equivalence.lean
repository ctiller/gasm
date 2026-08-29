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
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Executable
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.AArch64BareMetal.Program

namespace Spikes.Spike1Hello.AArch64BareMetal

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.BareMetal

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered bare-metal AArch64 execution. -/
theorem spike1_aarch64_baremetal_canonical_effect_trace_equivalence :
    (runBareMetalTrace spike1AArch64BareMetalInstructions spike1AArch64BareMetalExecutable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  set_option maxRecDepth 4000 in
  decide

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedBareMetalProgram contract instantiation for Spike 1 (Bare Metal AArch64 Hello World). -/
def spike1AArch64VerifiedBareMetalProgram : VerifiedBareMetalProgram Unit AnyEvent := {
  name             := "Spike 1: Bare Metal AArch64 Hello World"
  executable       := spike1AArch64BareMetalExecutable
  instructions     := spike1AArch64BareMetalInstructions
  spec             := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike1_aarch64_baremetal_canonical_effect_trace_equivalence
}

end Spikes.Spike1Hello.AArch64BareMetal

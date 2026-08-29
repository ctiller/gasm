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
import Gasm.Targets.AArch64.Linux.Linker
import Gasm.Targets.Dispatcher
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.AArch64Linux.Program

namespace Spikes.Spike1Hello.AArch64Linux

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Linux

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered static Linux ELF64 execution on AArch64. -/
theorem spike1_aarch64_linux_canonical_effect_trace_equivalence :
    (runAArch64Trace (Event := AnyEvent) spike1AArch64LinuxInstructions spike1AArch64LinuxExecutable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  set_option maxRecDepth 4000 in
  decide

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedAArch64LinuxProgram contract instantiation for Spike 1 (Linux AArch64 Hello World). -/
def spike1AArch64LinuxVerifiedProgram : VerifiedAArch64LinuxProgram Unit AnyEvent := {
  name             := "Spike 1: Linux AArch64 Hello World"
  executable       := spike1AArch64LinuxExecutable
  instructions     := spike1AArch64LinuxInstructions
  spec             := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike1_aarch64_linux_canonical_effect_trace_equivalence
}

end Spikes.Spike1Hello.AArch64Linux

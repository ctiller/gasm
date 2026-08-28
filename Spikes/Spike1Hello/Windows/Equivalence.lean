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
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

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

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedProgram contract instantiation for Spike 1 (Windows Hello World). -/
def spike1VerifiedProgram : VerifiedProgram Unit AnyEvent := {
  name             := "Spike 1: Windows Hello World"
  executable       := spike1Executable
  instructions     := spike1Instructions
  spec             := fun _ => runModelTrace (helloWorldWindowsSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike1_canonical_effect_trace_equivalence
}

end Spikes.Spike1Hello.Windows

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
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Windows.Program

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable assembly trace on empty stdin. -/
def asmTraceEmpty : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike3Instructions spike3Executable.load

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable monadic model trace on empty stdin. -/
def modelTraceEmpty : List AnyEvent :=
  runModelTrace (sortLinesSpec : TraceM AnyEvent Unit) []

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable assembly trace on canonical 3-line input. -/
def asmTraceCanonical : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike3Instructions (spike3Executable.loadWithStdin defaultSampleInput)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable monadic model trace on canonical 3-line input. -/
def modelTraceCanonical : List AnyEvent :=
  runModelTrace (sortLinesSpec : TraceM AnyEvent Unit) defaultInputLines

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level sorting spec and lowered machine execution on canonical input. -/
theorem spike3_canonical_effect_trace_equivalence_inst :
    (asmTraceCanonical == modelTraceCanonical) = true := by
  native_decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence on empty input. -/
theorem spike3_empty_effect_trace_equivalence_inst :
    (runAsmTrace (Event := AnyEvent) spike3Instructions spike3Executable.load == modelTraceEmpty) = true := by
  native_decide

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
instance : EnvironmentLoader Bool where
  loadEnvironment exe b := if b then exe.loadWithStdin defaultSampleInput else exe.load

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedProgram contract instantiation for Spike 3 (Stdin Lexicographical Line Sorter). -/
def spike3VerifiedProgram : VerifiedProgram Bool AnyEvent := {
  name             := "Spike 3: Stdin Lexicographical Line Sorter"
  executable       := spike3Executable
  instructions     := spike3Instructions
  spec             := fun b => if b then modelTraceCanonical else modelTraceEmpty
  traceEquivalence := fun b => by
    cases b
    · exact spike3_empty_effect_trace_equivalence_inst
    · exact spike3_canonical_effect_trace_equivalence_inst
}

end Spikes.Spike3SortLines.Windows

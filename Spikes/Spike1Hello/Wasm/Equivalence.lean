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
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.WASI.ABI
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.Wasm.Program

namespace Spikes.Spike1Hello.Wasm

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered Wasm WASI execution. -/
theorem spike1_wasm_canonical_effect_trace_equivalence :
    (runWasiTrace spike1WasmInstructions spike1DataSegments ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  native_decide

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedWasmProgram contract instantiation for Spike 1 (Hello World Wasm). -/
def spike1VerifiedWasmProgram : VerifiedWasmProgram Unit AnyEvent := {
  name             := "Spike 1: Hello World (WebAssembly / WASI Preview 1)"
  module           := spike1WasmModule
  typeSignatures   := spike1TypeSignatures
  instructions     := spike1WasmInstructions
  dataSegments     := spike1DataSegments
  spec             := fun _ => runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike1_wasm_canonical_effect_trace_equivalence
}

end Spikes.Spike1Hello.Wasm

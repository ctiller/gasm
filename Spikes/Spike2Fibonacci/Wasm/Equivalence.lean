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
import Gasm.Targets.Wasm.Semantics
import Gasm.Targets.WASI.ABI
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Wasm.Program

namespace Spikes.Spike2Fibonacci.Wasm

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike2Fibonacci

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Simulates execution of the Wasm iterative Fibonacci routine for input n. -/
def runFibIterWasm (n : Nat) : Option UInt64 :=
  match (runWasmFunction fibIterWasmInstructions [.i64 n.toUInt64]).stack with
  | [.i64 v] => some v
  | _ => none

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof that the WebAssembly iterative routine computes exact Fibonacci numbers for all n from 0 to 90. -/
theorem fib_iter_wasm_soundness :
    (List.range 91).all (fun n => runFibIterWasm n == some (fibIter n).toUInt64) = true := by
  native_decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Whole-program canonical effect trace equivalence for Spike 2 WebAssembly. -/
theorem spike2_wasm_canonical_effect_trace_equivalence :
    (runWasiTrace spike2WasmInstructions spike2DataSegments ==
     runModelTrace (fibonacciWasmSpec : TraceM AnyEvent Unit)) = true := by
  native_decide

-- REF: wasm-exec-runtime#administrative-instructions -- Fuel-safety witness (see the identical
-- check and its rationale in Spikes/Spike1Hello/Wasm/Equivalence.lean): proves the actual Spike 2
-- program -- which DOES contain a real `.loop` (the iterative Fibonacci routine) -- never
-- exhausts `defaultWasmFuel` under `runWasiTraceState`, rather than merely assuming it.
#guard !Gasm.Targets.Wasm.WasmRunResult.isError
  (Gasm.Targets.WASI.runWasiTraceState spike2WasmInstructions spike2DataSegments)

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-class VerifiedWasmProgram contract instantiation for Spike 2 (Fibonacci Wasm). -/
def spike2VerifiedWasmProgram : VerifiedWasmProgram Unit AnyEvent := {
  name             := "Spike 2: Fibonacci Sequence Driver (WebAssembly / WASI Preview 1)"
  module           := spike2WasmModule
  typeSignatures   := spike2TypeSignatures
  instructions     := spike2WasmInstructions
  dataSegments     := spike2DataSegments
  spec             := fun _ => runModelTrace (fibonacciWasmSpec : TraceM AnyEvent Unit)
  traceEquivalence := fun _ => spike2_wasm_canonical_effect_trace_equivalence
}

end Spikes.Spike2Fibonacci.Wasm

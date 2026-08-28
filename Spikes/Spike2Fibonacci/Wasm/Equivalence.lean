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
import Spikes.Spike2Fibonacci.Wasm.LoopInvariant

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
/-- **PA15.** The WebAssembly iterative routine computes exact Fibonacci numbers, for every `n` the
    interpreter's default fuel budget (`defaultWasmFuel = 100000000`) can complete within. Discharged
    by `fibIterWasm_run` (`Spikes/Spike2Fibonacci/Wasm/LoopInvariant.lean`), whose content is
    `loop_correct`: an induction on the remaining iteration count against the loop invariant
    `FibLocals`, established by the routine's prologue and preserved by one pass through the
    `loop` body. A genuine structural argument -- not `native_decide` executing the interpreter on
    concrete inputs.

    This is a *different, more general* fact than the theorem it replaces: the previous
    `(List.range 91).all (...) = true` was a finite check over `n = 0..90`. The bound here is **not**
    the `UInt64`-overflow point the allowlist entry this replaces assumed was the relevant limit
    (`fib 93` is the last value that fits in 64 bits without wrapping) -- both sides of this equation
    wrap `UInt64` arithmetic identically (`Nat.toUInt64` distributes over `+`, discharged as
    `by simp [Nat.toUInt64]` inside `loop_correct`), so the equation holds *regardless* of `UInt64`
    overflow. The actual bound is the interpreter's own fuel budget: the routine consumes one unit
    per loop iteration plus a fixed prologue/epilogue cost, so `n + 26 ≤ defaultWasmFuel`.
    `fibIterWasm_run` is stated for arbitrary `fuel`, so a caller needing a larger `n` passes more;
    only this corollary fixes it at the default. -/
theorem fib_iter_wasm_soundness (n : Nat) (hn : n ≤ 99999974) :
    runFibIterWasm n = some (fibIter n).toUInt64 := by
  unfold runFibIterWasm
  rw [fibIterWasm_run n defaultWasmFuel (by omega)
    (show n + 26 ≤ 100000000 by omega), fibIter_eq_fibNat]

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

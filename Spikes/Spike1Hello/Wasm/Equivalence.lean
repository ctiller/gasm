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
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered Wasm WASI
    execution.

    **Why this still needs `native_decide` (checked 2026-08-27, oracle-debt retirement pass).**
    Spike 1 takes no input, so unlike the other spikes this is a closed-term claim with no `∀`
    to discharge -- exactly the shape that should be `decide`/`rfl`-able in the kernel, and indeed
    the Windows and BareMetal siblings of this theorem now close that way (see their
    `Equivalence.lean` files). This one does not, and the reason is architectural, not a matter of
    finding the right tactic: `runWasiTrace` bottoms out in `evalInstrs`/`evalLoop`/`evalInstrMatch`
    (`Gasm/Targets/Wasm/Semantics.lean`), a `mutual partial` group that Lean compiles to a genuine
    `opaque` constant -- confirmed here with `#print evalInstrs` (`opaque Gasm.Targets.Wasm.evalInstrs
    : ...`, no defining term at all) and by `unfold evalInstrs`/`rfl` both failing even on the
    trivial base case `evalInstrs [] s hc = (s, .next)`. This is not "kernel reduction gets stuck
    partway through a real term" (which `decide` can sometimes push through with more fuel, as the
    BareMetal sibling needed via `maxRecDepth`) -- there is no term to reduce at all, for any tactic,
    on any input, including single-instruction cases. `evalInstrMatch` and `evalLoop` are equally
    `opaque`. PA12 (`Gasm/Targets/Wasm/SemanticsFuzzer.lean`'s `evalInstr_trapped_next`) already hit
    and documented this exact wall for the trap-guard theorem: the only escape is a `Fuel`/`CCPO`-style
    rewrite of the whole interpreter's control-flow evaluation, because a real Wasm `loop` must be
    able to not terminate, so no structural/well-founded measure exists for `evalLoop` across ALL
    instruction lists (Spike 1's own list happens to contain no `.loop`, but that fact is invisible
    to the kernel without a defining equation to case on in the first place -- there is nothing to
    induct over). Such a rewrite would change `evalInstrs`/`evalLoop`'s definitions themselves, which
    are shared by every Wasm-target spike (2-5) and the fuzzers, not something scoped to Spike 1 --
    out of scope for this pass. `native_decide` remains the correct, honestly-labelled tool here. -/
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

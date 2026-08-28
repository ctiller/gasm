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

    **Oracle-debt retirement (2026-08-27): `native_decide` -> `decide +kernel`, fuel conversion.**
    Spike 1 takes no input, so this is a closed-term claim with no `∀` to discharge -- exactly the
    shape the Windows and BareMetal siblings of this theorem already close with plain `decide`.
    This one previously could not: `runWasiTrace` bottomed out in
    `evalInstrs`/`evalLoop`/`evalInstrMatch` (`Gasm/Targets/Wasm/Semantics.lean`), a `mutual
    partial` group Lean compiled to a genuine `opaque` constant with no defining equations at all
    for any tactic, on any input -- not "kernel reduction gets stuck partway through a real term,"
    but literally no term to reduce (confirmed via `#print evalInstrs` and `unfold
    evalInstrs`/`rfl` both failing on the trivial base case). That group has now been converted to
    fuel-based structural recursion on an explicit `Nat` (`defaultWasmFuel`, following
    `Gasm/Targets/X86_64/Semantics.lean`'s `runProgramTraceWithLoops` shape exactly), so it is an
    ordinary total `def` with real kernel-unfoldable equations (confirmed: `#print evalInstrs` now
    shows a `Nat.brecOn`-based definition, not `opaque`).

    **Why `+kernel`, not plain `decide`.** Plain `decide` (and `rfl`) still fail here -- not with
    the old "no term to reduce" opacity, but because the ELABORATOR's own `whnf` (a different
    reduction engine from the kernel's, used by `decide`/`isDefEq` by default) gets stuck on the
    `Nat.brecOn`-compiled matcher applications the fuel conversion introduces, reporting "reduction
    got stuck" at the top-level `Bool` equality regardless of `maxHeartbeats` (confirmed empirically:
    still stuck at 40 million heartbeats, ruling out "just needs more budget"). `#reduce` on the
    same expression, and `native_decide` (the tactic this replaces), both fully evaluate it to
    `true` -- proving the claim genuinely holds and the elaborator-`whnf` path is an incompleteness
    in that specific reduction strategy, not a defect in this proof or the interpreter. `decide
    +kernel` (Lean's flag for routing the same `Decidable` reduction through the KERNEL's `whnf`
    instead, which has direct, GMP-accelerated support for `Nat.rec`/`Nat.brecOn` on literals) finds
    the same answer directly -- confirmed to complete in ~13s with no `set_option` tuning needed at
    all, faster and simpler than the Windows/BareMetal siblings' plain `decide` (BareMetal still
    needs `set_option maxRecDepth 4000`; this one needs nothing beyond `+kernel`). Still zero
    oracle, zero allowlist entry: `+kernel` selects a reduction STRATEGY, not a different axiom or
    trust boundary -- the produced proof term is still independently re-checked by the kernel like
    any other, exactly as plain `decide`'s is. -/
theorem spike1_wasm_canonical_effect_trace_equivalence :
    (runWasiTrace spike1WasmInstructions spike1DataSegments ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  decide +kernel

-- REF: wasm-exec-runtime#administrative-instructions -- Fuel-safety witness for
-- `spike1_wasm_canonical_effect_trace_equivalence` above: proves `runWasiTraceState` (the
-- un-collapsed `WasmRunResult` this theorem's `runWasiTrace` is built on -- see its own
-- docstring in `Gasm/Targets/WASI/ABI.lean`) genuinely reaches a stopping point for Spike 1's
-- actual program, rather than merely assuming `defaultWasmFuel` (100 million) is enough. Spike
-- 1's Wasm program contains no `.loop` at all (`grep -c '\.loop' Program.lean` returns 0), so
-- this is not a close call, but the check is a real, executed proof rather than an assumption --
-- exactly the anti-vacuity discipline TCB.md's "Fuel exhaustion indistinguishable from clean
-- termination" finding asks for.
#guard !Gasm.Targets.Wasm.WasmRunResult.isError
  (Gasm.Targets.WASI.runWasiTraceState spike1WasmInstructions spike1DataSegments)

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

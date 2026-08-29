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
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Wasm.Program
import Spikes.Spike3SortLines.Wasm.Outcome

namespace Spikes.Spike3SortLines.Wasm

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike3SortLines

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Default sample test input string for standard verified execution. -/
def defaultSampleInput : ByteArray :=
  "cherry\r\napple\r\nbanana\r\n".toUTF8

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Finite capability selected at the Spike 3 WASI boundary.  It does not constrain stdin: an
    allocation or execution shortfall is represented in `WasiObservable`, rather than converted
    to a partial output trace. -/
def spike3WasiResources : WasiResourceBudget :=
  { fuel := defaultWasmFuel, memoryPages := 65536 }

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Explicit resource-aware result for the canonical executable trace. -/
def spike3WasmCanonicalOutcome : WasiRunOutcome :=
  runSpike3WasiOutcome defaultSampleInput spike3WasiResources

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Observable Wasm trace on canonical 3-line input. -/
def wasmTraceCanonical : List AnyEvent :=
  runWasiTrace spike3WasmInstructions spike3DataSegments defaultSampleInput ["fd_read", "fd_write", "proc_exit"]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- High-level model specification trace on canonical 3-line input. -/
def specTraceCanonical : List AnyEvent := [
  Inject.inject (ConsoleEvent.out "apple"),
  Inject.inject (ConsoleEvent.out "\r\n"),
  Inject.inject (ConsoleEvent.out "banana"),
  Inject.inject (ConsoleEvent.out "\r\n"),
  Inject.inject (ConsoleEvent.out "cherry"),
  Inject.inject (ConsoleEvent.out "\r\n"),
  Inject.inject (ProcessEvent.exit 0)
]

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Canonical high-level outcome.  Other finite resource outcomes remain representable by
    `WasiObservable.memoryExhausted` and `.fuelExhausted` in the verified-program contract. -/
def specOutcomeCanonical : WasiObservable AnyEvent :=
  .exited 0 specTraceCanonical

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Formally verified theorem: WebAssembly operational trace on canonical stdin matches specification trace. -/
theorem spike3_wasm_canonical_effect_trace_equivalence :
    (spike3WasmCanonicalOutcome.observable == specOutcomeCanonical) = true := by
  native_decide

-- REF: wasm-exec-runtime#administrative-instructions -- Fuel-safety witness (see the identical
-- check and its rationale in Spikes/Spike1Hello/Wasm/Equivalence.lean): proves the actual Spike 3
-- program on its canonical sample input never exhausts `defaultWasmFuel` under
-- `runWasiTraceState`, rather than merely assuming it.
#guard !Gasm.Targets.Wasm.WasmRunResult.isError
  (runWasiTraceState spike3WasmInstructions spike3DataSegments defaultSampleInput ["fd_read", "fd_write", "proc_exit"])

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Test environment domain for Spike 3 WebAssembly execution. -/
inductive Spike3SampleEnv where
  | canonical

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
instance : WasiEnvironmentLoader Spike3SampleEnv where
  loadWasiEnvironment _ := (defaultSampleInput, [])

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- First-class verified WebAssembly program instance for Spike 3. -/
def spike3VerifiedWasmProgram : VerifiedWasmProgram Spike3SampleEnv AnyEvent := {
  name             := "spike3_sort_lines_wasm"
  module           := spike3WasmModule
  typeSignatures   := spike3TypeSignatures
  instructions     := spike3WasmInstructions
  dataSegments     := spike3DataSegments
  imports          := ["fd_read", "fd_write", "proc_exit"]
  resources        := spike3WasiResources
  spec             := fun _ => specOutcomeCanonical
  traceEquivalence := fun _ => spike3_wasm_canonical_effect_trace_equivalence
}

end Spikes.Spike3SortLines.Wasm

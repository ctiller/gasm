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

import Gasm.Targets.WASI.ABI
import Spikes.Spike3SortLines.Wasm.Program

namespace Spikes.Spike3SortLines.Wasm

open Gasm.Targets.WASI
open Gasm.Targets.Wasm

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- The explicit WASI execution outcome for the line sorter.  Unlike the historical trace-only
    runner, this value makes a finite resource budget observable to its caller. -/
def runSpike3WasiOutcome (stdin : ByteArray) (budget : WasiResourceBudget) : WasiRunOutcome :=
  runWasiOutcome spike3WasmInstructions spike3DataSegments stdin
    ["fd_read", "fd_write", "proc_exit"] [] budget

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Complete finite-resource observation of the Spike 3 CLI.  The resource-failure arm is
    deliberately separate from generic Wasm traps and fuel exhaustion: it is selected only by
    the program's explicit `proc_exit spike3ResourceFailureExitCode`, emitted after a checked
    SmolAlloc failure.  Consumers therefore cannot mistake an allocation limit for a successfully
    sorted (possibly partial) output. -/
inductive Spike3FiniteOutcome where
  | completed (state : WasmMachineState) (signal : ControlSignal)
  | resourceFailure (state : WasmMachineState)
  | exited (state : WasmMachineState) (code : UInt32)
  | trapped (state : WasmMachineState)
  | fuelExhausted (partialState : WasmMachineState)
  | memoryExhausted (state : WasmMachineState) (requestedPages availablePages : Nat)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Classifies every bounded execution without collapsing either interpreter fuel or the CLI's
    specified allocator failure. -/
def Spike3FiniteOutcome.ofWasi : WasiRunOutcome → Spike3FiniteOutcome
  | .completed state signal => .completed state signal
  | .exited state code =>
    if code == spike3ResourceFailureExitCode then .resourceFailure state else .exited state code
  | .trapped state => .trapped state
  | .fuelExhausted state => .fuelExhausted state
  | .memoryExhausted state requested available =>
    .memoryExhausted state requested available

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- The caller-facing result for arbitrary finite stdin and an explicit finite execution budget. -/
def runSpike3Finite (stdin : ByteArray) (budget : WasiResourceBudget) : Spike3FiniteOutcome :=
  Spike3FiniteOutcome.ofWasi (runSpike3WasiOutcome stdin budget)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- The allocator-failure process exit is definitionally classified as the deterministic resource
    result, never as clean completion or a generic trap. -/
theorem spike3_resource_exit_is_observable (state : WasmMachineState) :
    Spike3FiniteOutcome.ofWasi (.exited state spike3ResourceFailureExitCode) =
      .resourceFailure state := by
  simp [Spike3FiniteOutcome.ofWasi]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Finite platform capability used by an invocation of the line sorter.  Arbitrary stdin bytes
    are still passed to the program; if they demand more than this capability supplies, the
    outcome is explicitly `.memoryExhausted` or `.fuelExhausted`, never a forged output trace. -/
abbrev Spike3WasiResources := WasiResourceBudget

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Focused soundness lemma: output events are unavailable on either finite-resource failure.
    This is the trace-level property the future universal `VerifiedProgram` consumes. -/
theorem spike3_memory_exhaustion_has_no_trace (state : WasmMachineState)
    (requested available : Nat) :
    (WasiRunOutcome.memoryExhausted state requested available).events? = none := rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- The same holds for a finite interpreter-fuel exhaustion. -/
theorem spike3_fuel_exhaustion_has_no_trace (state : WasmMachineState) :
    (WasiRunOutcome.fuelExhausted state).events? = none := rfl

end Spikes.Spike3SortLines.Wasm

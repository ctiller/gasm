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

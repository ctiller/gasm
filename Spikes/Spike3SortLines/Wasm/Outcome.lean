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
def runSpike3WasiOutcome (stdin : ByteArray) (fuel : Nat) : WasiRunOutcome :=
  runWasiOutcome spike3WasmInstructions spike3DataSegments stdin
    ["fd_read", "fd_write", "proc_exit"] [] fuel

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- A completed line-sorter invocation, obtained only from a proof-carrying dynamic fuel budget.
    This is the interface used by the universal-input migration: a fixed interpreter default is
    not part of the program's semantics. -/
def runSpike3WasiCompleted (stdin : ByteArray)
    (budget : WasiFuelCertificate spike3WasmInstructions spike3DataSegments stdin
      ["fd_read", "fd_write", "proc_exit"] []) : WasiCompletedRun :=
  runWasiCompleted spike3WasmInstructions spike3DataSegments stdin
    ["fd_read", "fd_write", "proc_exit"] [] budget

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- A universal finite-input resource policy for the line sorter gives every byte stream a
    terminating interpreter budget.  Constructing this policy is the remaining quantitative
    proof obligation; downstream trace equivalence cannot bypass it. -/
abbrev Spike3WasiFuelStrategy :=
  WasiFuelStrategy spike3WasmInstructions spike3DataSegments ["fd_read", "fd_write", "proc_exit"]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Executes the sorter under an all-finite-input policy.  The strategy is chosen once, while its
    budget is selected from the actual input bytes for each run. -/
def runSpike3WasiWithStrategy (strategy : Spike3WasiFuelStrategy) (stdin : ByteArray) :
    WasiCompletedRun :=
  runSpike3WasiCompleted stdin (strategy.certificate stdin [])

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Focused soundness lemma: any supplied line-sorter budget rules out the resource-exhausted
    outcome for that exact finite input. -/
theorem spike3_budget_not_resource (stdin : ByteArray)
    (budget : WasiFuelCertificate spike3WasmInstructions spike3DataSegments stdin
      ["fd_read", "fd_write", "proc_exit"] [])
    (partialState : WasmMachineState) :
    runSpike3WasiOutcome stdin budget.fuel ≠ .resourceExhausted partialState := by
  exact budget.not_resource partialState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- The strategy path is definitionally backed by a certificate for the concrete finite input,
    so its completed-run result has no hidden exhaustion branch. -/
theorem spike3_strategy_not_resource (strategy : Spike3WasiFuelStrategy) (stdin : ByteArray)
    (partialState : WasmMachineState) :
    runSpike3WasiOutcome stdin (strategy.fuelFor stdin []) ≠ .resourceExhausted partialState := by
  exact (strategy.certificate stdin []).not_resource partialState

end Spikes.Spike3SortLines.Wasm

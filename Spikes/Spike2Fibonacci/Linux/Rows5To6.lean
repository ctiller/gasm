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

import Spikes.Spike2Fibonacci.Linux.Row5
import Spikes.Spike2Fibonacci.Linux.Row6

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- Rows five and six cached together, with only the accumulator rebased between their
independently checked selected prefixes. -/
theorem spike2_rows5_to6_selected_prefix :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 104
        spike2Row4AfterRecurrence ([] : List AnyEvent) spike2Row6AfterRecurrence eventsRev emitted := by
  have row6 := spike2_row6_selected_prefix.rebaseEvents_empty spike2Row5WriteEventsRev
  have rows56 := ProductionPrefix.SelectedPrefix.append spike2_row5_selected_prefix row6
  exact ⟨
    (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2).reverse ++
    spike2Row5WriteEventsRev,
    emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row5BeforeWriteSyscall)).2 ++
    emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2,
    by simpa using rows56⟩

end Spikes.Spike2Fibonacci.Linux

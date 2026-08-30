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

import Spikes.Spike2Fibonacci.Linux.Row1
import Spikes.Spike2Fibonacci.Linux.Row2
import Spikes.Spike2Fibonacci.Linux.Row3
import Spikes.Spike2Fibonacci.Linux.Row4

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- Rows one through four, joined from their independently checked exact certificates. -/
theorem spike2_rows1_to4_selected_prefix :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 208
        spike2AfterPrologue ([] : List AnyEvent) spike2Row4AfterRecurrence eventsRev emitted := by
  have row2 := spike2_row2_selected_prefix.rebaseEvents_empty spike2Row1WriteEventsRev
  have rows12 := ProductionPrefix.SelectedPrefix.append spike2_row1_selected_prefix row2
  have row3 := spike2_row3_selected_prefix.rebaseEvents_empty
    ((emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
      spike2Row1WriteEventsRev)
  have rows123 := ProductionPrefix.SelectedPrefix.append rows12 row3
  have row4 := spike2_row4_selected_prefix.rebaseEvents_empty
    ((emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
      spike2Row1WriteEventsRev)
  have rows1234 := ProductionPrefix.SelectedPrefix.append rows123 row4
  exact ⟨
    (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row4BeforeWriteSyscall)).2).reverse ++
    (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2).reverse ++
    (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
    spike2Row1WriteEventsRev,
    emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row1BeforeWriteSyscall)).2 ++
    emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2 ++
    emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2 ++
    emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row4BeforeWriteSyscall)).2,
    by simpa using rows1234⟩

/-- The actual Linux prologue followed by the first four selected output rows.  This is a
cached, executable prefix from the production load state, not a model-side loop summary. -/
theorem spike2_prologue_to_row4_selected_prefix :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 212
        spike2Executable.load ([] : List AnyEvent) spike2Row4AfterRecurrence eventsRev emitted := by
  rcases spike2_rows1_to4_selected_prefix with ⟨eventsRev, emitted, rows⟩
  exact ⟨eventsRev, emitted,
    ProductionPrefix.SelectedPrefix.append spike2_prologue_selected_prefix rows⟩

end Spikes.Spike2Fibonacci.Linux

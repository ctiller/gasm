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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexOnePath

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

structure Spike2FramedSliceResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (fuel : Nat) (endRip : UInt64) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  rip : final.rip = endRip
  rsp : final.rsp = spike2AfterPrologue.rsp
  fault : final.fault = none
  lowMemory : Spike2RowLowMemory final

structure Spike2MemoryPreservingSliceResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (fuel : Nat) (endRip : UInt64)
    extends Spike2FramedSliceResult initial eventsRev fuel endRip where
  memory : final.memory = initial.memory

private theorem index_two_rip (state : X86_64MachineState)
    (hrip : state.rip = 5368713297)
    (twoDigit : X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state)) :
    (spike2AfterIndexHeader state).rip = 5368713344 := by
  simp only [X86BranchCondition.holds] at twoDigit
  unfold spike2AfterIndexHeader
  rw [step_jge_rel8_taken_rip _ _ (decide_eq_true_iff.mpr twoDigit)]
  unfold spike2AfterIndexCompare
  change state.rip + 4 + 2 + signExtend8To64 41 = 5368713344
  rw [hrip]
  rfl

opaque spike2_two_digit_branch_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (lower : 9 ≤ completed) (upper : completed < 90)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1))
    (hrip : state.rip = 5368713297) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    Spike2MemoryPreservingSliceResult state eventsRev 2 5368713344 := by
  let final := spike2AfterIndexHeader state
  have twoDigit := spike2_index_counter_two_digit state completed lower upper counter
  have finalRip : final.rip = 5368713344 := index_two_rip state hrip twoDigit
  have frame := spike2_index_header_registerFrame state
  have finalLow : Spike2RowLowMemory final := low.of_memory_eq (by rfl)
  have text : final.read64 5368713344 ≠ 5368713344 := by
    rw [finalLow 5368713344 (by decide)]
    exact spike2_initial_text_3344_not_selfref
  have boundary := spike2_selected_silent_nonIat final 5368713344 finalRip (by decide) text
  exact {
    final := final
    certificate := spike2_index_header_two_digit_selected_prefix state eventsRev hrip twoDigit
      (by rw [finalRip]; exact boundary.1) (by rw [finalRip]; exact boundary.2) safe
    registers := frame
    fibRegisters := by constructor <;> rfl
    rip := finalRip
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := finalLow
    memory := rfl }

end Spikes.Spike2Fibonacci.Windows

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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexTwoTens

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

opaque spike2_two_digit_second_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713377)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) :
    Spike2FramedSliceResult state eventsRev 2 5368713384 := by
  let final := spike2AfterTwoDigitHead state
  have frame := spike2_two_digit_head_registerFrame state
  have finalRip : final.rip = 5368713384 := by
    change state.rip + 5 + 2 = 5368713384
    rw [hrip]
    rfl
  have finalLow := spike2_two_digit_head_lowMemory state low rsp
  have text : final.read64 5368713384 ≠ 5368713384 := by
    rw [finalLow 5368713384 (by decide)]
    exact spike2_initial_text_3384_not_selfref
  have boundary := spike2_selected_silent_nonIat final 5368713384 finalRip (by decide) text
  exact {
    final := final
    certificate := spike2_two_digit_head_selected_prefix state eventsRev hrip safe
      (by rw [finalRip]; exact boundary.1) (by rw [finalRip]; exact boundary.2)
    registers := frame
    fibRegisters := by constructor <;> rfl
    rip := finalRip
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := finalLow }

end Spikes.Spike2Fibonacci.Windows

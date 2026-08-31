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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexTwoDivision

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets.X86_64

structure Spike2TwoDigitTensResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent)
    extends Spike2FramedSliceResult initial eventsRev 4 5368713377 where
  realizes : final = spike2AfterTwoDigitTens initial

opaque spike2_two_digit_tens_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713362)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) :
    Spike2TwoDigitTensResult state eventsRev := by
  let final := spike2AfterTwoDigitTens state
  have frame := spike2_two_digit_tens_registerFrame state
  exact {
    final := final
    certificate := spike2_two_digit_tens_selected_prefix state eventsRev hrip safe
    registers := frame
    fibRegisters := by constructor <;> rfl
    rip := by
      change state.rip + 4 + 4 + 5 + 2 = 5368713377
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := spike2_two_digit_tens_lowMemory state low rsp
    realizes := rfl }

end Spikes.Spike2Fibonacci.Windows

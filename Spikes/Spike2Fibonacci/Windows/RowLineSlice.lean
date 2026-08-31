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
-/import Spikes.Spike2Fibonacci.Windows.RowDecimalSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

opaque spike2_line_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713457) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (cursorAbove : spike2RowLowMemoryTop ≤ (state.gprs .rdi).toNat)
    (cursorRoom : (state.gprs .rdi).toNat + 2 ≤ 2 ^ 64) :
    Spike2FramedSliceResult state eventsRev 6 5368713489 := by
  let final := spike2AfterLineTerminator state
  have frame := spike2_line_terminator_registerFrame state
  exact {
    final := final
    certificate := spike2_line_terminator_selected_prefix state eventsRev hrip safe
    registers := frame
    fibRegisters := by constructor <;> rfl
    rip := by
      change state.rip + 10 + 2 + 4 + 10 + 2 + 4 = 5368713489
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := spike2_line_terminator_lowMemory state low cursorAbove cursorRoom }

end Spikes.Spike2Fibonacci.Windows

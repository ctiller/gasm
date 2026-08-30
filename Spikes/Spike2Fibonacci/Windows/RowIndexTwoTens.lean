/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowIndexTwoDivision

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets.X86_64

opaque spike2_two_digit_tens_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713362)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) :
    Spike2FramedSliceResult state eventsRev 4 5368713377 := by
  let final := spike2AfterTwoDigitTens state
  have frame := spike2_two_digit_tens_registerFrame state
  exact {
    final := final
    certificate := spike2_two_digit_tens_selected_prefix state eventsRev hrip safe
    registers := frame
    rip := by
      change state.rip + 4 + 4 + 5 + 2 = 5368713377
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := spike2_two_digit_tens_lowMemory state low rsp }

end Spikes.Spike2Fibonacci.Windows

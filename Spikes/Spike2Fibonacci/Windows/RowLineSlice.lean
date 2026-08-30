/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowDecimalSlice

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
    rip := by
      change state.rip + 10 + 2 + 4 + 10 + 2 + 4 = 5368713489
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := spike2_line_terminator_lowMemory state low cursorAbove cursorRoom }

end Spikes.Spike2Fibonacci.Windows

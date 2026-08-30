/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowIndexTwoHead

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

opaque spike2_two_digit_tail_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713384)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) : Spike2CursorSliceResult state eventsRev 5 := by
  have tailPrefix := spike2_two_digit_tail_selected_prefix state eventsRev hrip safe
  have tailFrame := spike2_two_digit_tail_registerFrame state
  have tailLow := spike2_two_digit_tail_lowMemory state low rsp
  have bounds := spike2_two_digit_cursor_bounds state rsp
  exact {
    fuel := 5
    final := spike2AfterTwoDigitIndex state
    fuelBound := by decide
    certificate := tailPrefix
    registers := tailFrame
    lowMemory := tailLow
    cursorAboveStack := by
      rw [tailFrame.rsp, spike2_two_digit_cursor, rsp, spike2_after_prologue_rsp_eq]
      decide
    cursorAbove := bounds.1
    cursorRoom := bounds.2 }

end Spikes.Spike2Fibonacci.Windows

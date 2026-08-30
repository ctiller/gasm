/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRegisterFrameDivision

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64

theorem spike2_two_digit_tens_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitTens state) := by
  constructor <;> rfl

theorem spike2_two_digit_head_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitHead state) := by
  constructor <;> rfl

theorem spike2_two_digit_tail_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitIndex state) := by
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows

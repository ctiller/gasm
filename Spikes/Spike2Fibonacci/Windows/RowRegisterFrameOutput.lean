/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRegisterFrameBase

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64

theorem spike2_decimal_setup_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterDecimalSetup state) := by
  constructor <;> rfl

theorem spike2_line_terminator_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterLineTerminator state) := by
  constructor <;> rfl

theorem spike2_write_setup_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2BeforeWriteFile state) := by
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows

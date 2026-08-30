/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceRegister2
import Spikes.Spike2Fibonacci.Windows.RowRecurrence3

namespace Spikes.Spike2Fibonacci.Windows
open Gasm.Targets.X86_64
theorem spike2_recurrence_move14_registers (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterRecurrenceMove14 state) := by
  constructor <;> rfl
end Spikes.Spike2Fibonacci.Windows

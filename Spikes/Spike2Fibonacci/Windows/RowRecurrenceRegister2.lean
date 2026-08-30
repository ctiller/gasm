/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceRegister1
import Spikes.Spike2Fibonacci.Windows.RowRecurrence2

namespace Spikes.Spike2Fibonacci.Windows
open Gasm.Targets.X86_64
theorem spike2_recurrence_add_registers (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterRecurrenceAdd state) := by
  constructor <;> rfl
end Spikes.Spike2Fibonacci.Windows

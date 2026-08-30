/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowOutputSlice

namespace Spikes.Spike2Fibonacci.Windows
open Gasm.Targets.X86_64
theorem spike2_recurrence_move_registers (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterRecurrenceMove state) := by
  constructor <;> rfl
end Spikes.Spike2Fibonacci.Windows

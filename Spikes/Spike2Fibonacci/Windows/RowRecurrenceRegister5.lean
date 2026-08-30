/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceRegister4
import Spikes.Spike2Fibonacci.Windows.RowRecurrence5

namespace Spikes.Spike2Fibonacci.Windows
open Gasm.Targets.X86_64
theorem spike2_recurrence_increment_registers (state : X86_64MachineState) :
    (spike2AfterRecurrenceIncrement state).rsp = state.rsp ∧
    (spike2AfterRecurrenceIncrement state).gprs .r13 = state.gprs .r13 + 1 ∧
    (spike2AfterRecurrenceIncrement state).fault = state.fault := by
  exact ⟨rfl, rfl, rfl⟩
end Spikes.Spike2Fibonacci.Windows

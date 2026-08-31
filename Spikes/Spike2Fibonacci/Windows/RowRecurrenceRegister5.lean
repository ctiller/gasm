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
-/import Spikes.Spike2Fibonacci.Windows.RowRecurrenceRegister4
import Spikes.Spike2Fibonacci.Windows.RowRecurrence5

namespace Spikes.Spike2Fibonacci.Windows
open Gasm.Targets.X86_64
theorem spike2_recurrence_increment_registers (state : X86_64MachineState) :
    (spike2AfterRecurrenceIncrement state).rsp = state.rsp ∧
    (spike2AfterRecurrenceIncrement state).gprs .r13 = state.gprs .r13 + 1 ∧
    (spike2AfterRecurrenceIncrement state).fault = state.fault := by
  exact ⟨rfl, rfl, rfl⟩
end Spikes.Spike2Fibonacci.Windows

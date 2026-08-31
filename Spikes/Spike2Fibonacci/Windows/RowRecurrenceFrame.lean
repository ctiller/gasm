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
-/import Spikes.Spike2Fibonacci.Windows.RowFrame

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRecurrenceFrame :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Targets.X86_64

/-- The six recurrence instructions are register/flag/control-flow only. -/
theorem spike2_recurrence_tail_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state) :
    Spike2RowLowMemory (spike2AfterRecurrenceTail state) := by
  have h1 : Spike2RowLowMemory (spike2AfterRecurrenceMove state) :=
    holds.of_memory_eq (by rfl)
  have h2 : Spike2RowLowMemory
      (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state)) :=
    h1.of_memory_eq (by rfl)
  have h3 : Spike2RowLowMemory
      (spike2AfterRecurrenceMove14
        (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))) :=
    h2.of_memory_eq (by rfl)
  have h4 : Spike2RowLowMemory
      (spike2AfterRecurrenceMove15
        (spike2AfterRecurrenceMove14
          (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state)))) :=
    h3.of_memory_eq (by rfl)
  have h5 : Spike2RowLowMemory
      (spike2AfterRecurrenceIncrement
        (spike2AfterRecurrenceMove15
          (spike2AfterRecurrenceMove14
            (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))))) :=
    h4.of_memory_eq (by rfl)
  exact h5.of_memory_eq (by rfl)

end Spikes.Spike2Fibonacci.Windows

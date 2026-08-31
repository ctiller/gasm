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
-/import Spikes.Spike2Fibonacci.Windows.RowRecurrenceIncrementSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

theorem spike2_recurrence_backedge_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713539)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    ∃ final,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
        state eventsRev final eventsRev [] ∧
      Spike2RowRegisterFrame state final ∧
      Spike2FibRegisterFrame state final ∧
      Spike2RowLowMemory final ∧
      final.rip = spike2WindowsMainLoopRip ∧ final.fault = none := by
  have boundary := spike2_recurrence_backedge_boundary state hrip safe
  exact ⟨spike2AfterRecurrenceBackedge state,
    spike2_recurrence_backedge_selected_prefix state eventsRev hrip safe,
    { rsp := boundary.2.2.1
      r13 := boundary.2.2.2.1
      fault := boundary.2.1.trans safe.symm },
    (by constructor <;> rfl),
    low.of_memory_eq boundary.2.2.2.2,
    boundary.1, boundary.2.1⟩

end Spikes.Spike2Fibonacci.Windows

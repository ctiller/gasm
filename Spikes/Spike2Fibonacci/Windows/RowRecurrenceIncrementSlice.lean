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
-/import Spikes.Spike2Fibonacci.Windows.RowRecurrencePreSlice

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRecurrenceIncrementSlice :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2RecurrenceIncrementResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
    initial eventsRev final eventsRev []
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713539
  rsp : final.rsp = spike2AfterPrologue.rsp
  counter : final.gprs .r13 = initial.gprs .r13 + 1
  fibRegisters : Spike2FibRegisterFrame initial final
  fault : final.fault = none

opaque spike2_recurrence_increment_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713535)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) : Spike2RecurrenceIncrementResult state eventsRev := by
  have observations := spike2_recurrence_increment_registers state
  have boundary := spike2_recurrence_increment_boundary state hrip safe
  exact {
    final := spike2AfterRecurrenceIncrement state
    certificate := spike2_recurrence_increment_selected_prefix state eventsRev hrip safe
    lowMemory := low.of_memory_eq (by rfl)
    rip := boundary.1
    rsp := observations.1.trans rsp
    counter := observations.2.1
    fibRegisters := by constructor <;> rfl
    fault := boundary.2 }

end Spikes.Spike2Fibonacci.Windows

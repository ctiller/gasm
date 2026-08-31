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
-/import Spikes.Spike2Fibonacci.Windows.RowWriteHookSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2RecurrencePreResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 4
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibA : final.gprs .r14 = initial.gprs .r15
  fibB : final.gprs .r15 = initial.gprs .r14 + initial.gprs .r15
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713535
  rsp : final.rsp = spike2AfterPrologue.rsp
  fault : final.fault = none

opaque spike2_recurrence_pre_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713523) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    Spike2RecurrencePreResult state eventsRev := by
  let s1 := spike2AfterRecurrenceMove state
  let s2 := spike2AfterRecurrenceAdd s1
  let s3 := spike2AfterRecurrenceMove14 s2
  let final := spike2AfterRecurrenceMove15 s3
  have b1 := spike2_recurrence_move_boundary state hrip safe
  have b2 := spike2_recurrence_add_boundary s1 b1.1 b1.2
  have b3 := spike2_recurrence_move14_boundary s2 b2.1 b2.2
  have b4 := spike2_recurrence_move15_boundary s3 b3.1 b3.2
  have p1 := spike2_recurrence_move_selected_prefix state eventsRev hrip safe
  have p2 := spike2_recurrence_add_selected_prefix s1 eventsRev b1.1 b1.2
  have p3 := spike2_recurrence_move14_selected_prefix s2 eventsRev b2.1 b2.2
  have p4 := spike2_recurrence_move15_selected_prefix s3 eventsRev b3.1 b3.2
  have h1 := spike2_recurrence_move_registers state
  have h2 := spike2_recurrence_add_registers s1
  have h3 := spike2_recurrence_move14_registers s2
  have h4 := spike2_recurrence_move15_registers s3
  have l1 : Spike2RowLowMemory s1 := low.of_memory_eq (by rfl)
  have l2 : Spike2RowLowMemory s2 := l1.of_memory_eq (by rfl)
  have l3 : Spike2RowLowMemory s3 := l2.of_memory_eq (by rfl)
  exact {
    final := final
    certificate := by simpa using ((p1.append p2).append p3).append p4
    registers := ((h1.trans h2).trans h3).trans h4
    fibA := by rfl
    fibB := by rfl
    lowMemory := l3.of_memory_eq (by rfl)
    rip := b4.1
    rsp := h4.rsp.trans (h3.rsp.trans (h2.rsp.trans (h1.rsp.trans rsp)))
    fault := b4.2 }

end Spikes.Spike2Fibonacci.Windows

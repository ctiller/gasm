/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrencePreSlice

namespace Spikes.Spike2Fibonacci.Windows

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
    fault := boundary.2 }

end Spikes.Spike2Fibonacci.Windows

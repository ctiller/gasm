/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceIncrementSlice

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
      Spike2RowLowMemory final ∧
      final.rip = spike2WindowsMainLoopRip ∧ final.fault = none := by
  have boundary := spike2_recurrence_backedge_boundary state hrip safe
  exact ⟨spike2AfterRecurrenceBackedge state,
    spike2_recurrence_backedge_selected_prefix state eventsRev hrip safe,
    { rsp := boundary.2.2.1
      r13 := boundary.2.2.2.1
      fault := boundary.2.1.trans safe.symm },
    low.of_memory_eq boundary.2.2.2.2,
    boundary.1, boundary.2.1⟩

end Spikes.Spike2Fibonacci.Windows

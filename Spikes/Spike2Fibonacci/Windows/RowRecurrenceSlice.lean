/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceBackedgeSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

theorem spike2_recurrence_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713523) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    ∃ final,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
        state eventsRev final eventsRev [] ∧
      Spike2RowLowMemory final ∧
      final.rip = spike2WindowsMainLoopRip ∧
      final.rsp = spike2AfterPrologue.rsp ∧
      final.gprs .r13 = state.gprs .r13 + 1 ∧
      final.fault = none := by
  let pre := spike2_recurrence_pre_slice state eventsRev hrip rsp safe low
  let increment := spike2_recurrence_increment_slice pre.final eventsRev pre.rip pre.rsp
    pre.fault pre.lowMemory
  rcases spike2_recurrence_backedge_slice increment.final eventsRev increment.rip
      increment.fault increment.lowMemory with
    ⟨final, backedgePrefix, backedgeRegisters, finalLow, finalRip, finalFault⟩
  refine ⟨final, ?_, finalLow, finalRip, backedgeRegisters.rsp.trans increment.rsp,
    backedgeRegisters.r13.trans (increment.counter.trans
      (congrArg (fun counter => counter + 1) pre.registers.r13)), finalFault⟩
  simpa using (pre.certificate.append increment.certificate).append backedgePrefix

end Spikes.Spike2Fibonacci.Windows

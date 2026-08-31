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
-/import Spikes.Spike2Fibonacci.Windows.RowRecurrenceBackedgeSlice

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
      final.gprs .r14 = state.gprs .r15 ∧
      final.gprs .r15 = state.gprs .r14 + state.gprs .r15 ∧
      final.fault = none := by
  let pre := spike2_recurrence_pre_slice state eventsRev hrip rsp safe low
  let increment := spike2_recurrence_increment_slice pre.final eventsRev pre.rip pre.rsp
    pre.fault pre.lowMemory
  rcases spike2_recurrence_backedge_slice increment.final eventsRev increment.rip
      increment.fault increment.lowMemory with
    ⟨final, backedgePrefix, backedgeRegisters, backedgeFib, finalLow, finalRip, finalFault⟩
  refine ⟨final, ?_, finalLow, finalRip, backedgeRegisters.rsp.trans increment.rsp,
    backedgeRegisters.r13.trans (increment.counter.trans
      (congrArg (fun counter => counter + 1) pre.registers.r13)),
    backedgeFib.r14.trans (increment.fibRegisters.r14.trans pre.fibA),
    backedgeFib.r15.trans (increment.fibRegisters.r15.trans pre.fibB), finalFault⟩
  simpa using (pre.certificate.append increment.certificate).append backedgePrefix

end Spikes.Spike2Fibonacci.Windows

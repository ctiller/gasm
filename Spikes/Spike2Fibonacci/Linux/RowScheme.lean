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
-/

import Spikes.Spike2Fibonacci.Linux.Row7

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- The compact semantic interface required to start a continuing Fibonacci row.  It deliberately
contains projections only: no equality to a generated checkpoint and no whole-memory premise. -/
structure Spike2LinuxRowEntry (completed : Nat) (current next : UInt64)
    (state : X86_64MachineState) : Prop where
  completed_lt : completed < 90
  rip : state.rip = spike2MainLoopRip
  counter : state.gprs .r13 = (completed + 1).toUInt64
  current_value : state.gprs .r14 = current
  next_value : state.gprs .r15 = next
  safe : state.fault = none

/-- The existing main-header certificate is the parametric first slice of every continuing row.
Its endpoint is expressed directly from the supplied predecessor state. -/
theorem spike2_row_header_from_entry {completed : Nat} {current next : UInt64}
    {state : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next state) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2
      state eventsRev (spike2AfterMainHeader state) eventsRev [] :=
  spike2_main_header_selected_prefix completed state eventsRev entry.completed_lt entry.rip
    entry.counter entry.safe

/-- Row 7 instantiates the generic entry interface with its actual production endpoint.  The
join is syntactic: no generated boundary-data state is compared or unfolded. -/
theorem spike2_row7_to_header_selected_prefix :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 66
        spike2Row6AfterRecurrence ([] : List AnyEvent)
        (spike2AfterMainHeader spike2Row7AfterRecurrence) eventsRev emitted := by
  rcases spike2_row7_after_recurrence_boundary with
    ⟨hrip, hcounter, hcurrent, hnext, hrsp, hsafe⟩
  let entry : Spike2LinuxRowEntry 7 21 34 spike2Row7AfterRecurrence :=
    ⟨by omega, hrip, by simpa using hcounter, hcurrent, hnext, hsafe⟩
  have header := spike2_row_header_from_entry (eventsRev := spike2Row7WriteEventsRev) entry
  have joined := ProductionPrefix.SelectedPrefix.append spike2_row7_selected_prefix header
  exact ⟨_, _, by simpa using joined⟩

end Spikes.Spike2Fibonacci.Linux

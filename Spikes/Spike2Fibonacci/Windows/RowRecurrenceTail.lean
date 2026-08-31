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
-/import Spikes.Spike2Fibonacci.Windows.RowRecurrence1
import Spikes.Spike2Fibonacci.Windows.RowRecurrence2
import Spikes.Spike2Fibonacci.Windows.RowRecurrence3
import Spikes.Spike2Fibonacci.Windows.RowRecurrence4
import Spikes.Spike2Fibonacci.Windows.RowRecurrence5
import Spikes.Spike2Fibonacci.Windows.RowRecurrence6

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64

/-- The fixed six-instruction recurrence tail, expressed only as transitions between opaque
producer boundaries. -/
def spike2AfterRecurrenceTail (state : X86_64MachineState) : X86_64MachineState :=
  spike2AfterRecurrenceBackedge
    (spike2AfterRecurrenceIncrement
      (spike2AfterRecurrenceMove15
        (spike2AfterRecurrenceMove14
          (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state)))))

/-- Append-only composition of the six separately compiled recurrence producers. -/
theorem spike2_recurrence_tail_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713523) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6 state eventsRev
      (spike2AfterRecurrenceTail state) eventsRev [] := by
  have b1 := spike2_recurrence_move_boundary state hrip hsafe
  have b2 := spike2_recurrence_add_boundary (spike2AfterRecurrenceMove state) b1.1 b1.2
  have b3 := spike2_recurrence_move14_boundary (spike2AfterRecurrenceAdd
    (spike2AfterRecurrenceMove state)) b2.1 b2.2
  have b4 := spike2_recurrence_move15_boundary (spike2AfterRecurrenceMove14
    (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))) b3.1 b3.2
  have b5 := spike2_recurrence_increment_boundary (spike2AfterRecurrenceMove15
    (spike2AfterRecurrenceMove14 (spike2AfterRecurrenceAdd
      (spike2AfterRecurrenceMove state)))) b4.1 b4.2
  have p1 := spike2_recurrence_move_selected_prefix state eventsRev hrip hsafe
  have p2 := spike2_recurrence_add_selected_prefix (spike2AfterRecurrenceMove state) eventsRev b1.1 b1.2
  have p3 := spike2_recurrence_move14_selected_prefix (spike2AfterRecurrenceAdd
    (spike2AfterRecurrenceMove state)) eventsRev b2.1 b2.2
  have p4 := spike2_recurrence_move15_selected_prefix (spike2AfterRecurrenceMove14
    (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))) eventsRev b3.1 b3.2
  have p5 := spike2_recurrence_increment_selected_prefix (spike2AfterRecurrenceMove15
    (spike2AfterRecurrenceMove14 (spike2AfterRecurrenceAdd
      (spike2AfterRecurrenceMove state)))) eventsRev b4.1 b4.2
  have p6 := spike2_recurrence_backedge_selected_prefix (spike2AfterRecurrenceIncrement
    (spike2AfterRecurrenceMove15 (spike2AfterRecurrenceMove14
      (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))))) eventsRev b5.1 b5.2
  have p12 := ProductionPrefix.SelectedPrefix.append p1 p2
  have p123 := ProductionPrefix.SelectedPrefix.append p12 p3
  have p1234 := ProductionPrefix.SelectedPrefix.append p123 p4
  have p12345 := ProductionPrefix.SelectedPrefix.append p1234 p5
  have p123456 := ProductionPrefix.SelectedPrefix.append p12345 p6
  simpa [spike2AfterRecurrenceTail] using p123456

/-- The tail returns to the typed driver-header address and cannot introduce a fault. -/
theorem spike2_recurrence_tail_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713523) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceTail state).rip = spike2WindowsMainLoopRip ∧
    (spike2AfterRecurrenceTail state).fault = none := by
  have b1 := spike2_recurrence_move_boundary state hrip hsafe
  have b2 := spike2_recurrence_add_boundary (spike2AfterRecurrenceMove state) b1.1 b1.2
  have b3 := spike2_recurrence_move14_boundary (spike2AfterRecurrenceAdd
    (spike2AfterRecurrenceMove state)) b2.1 b2.2
  have b4 := spike2_recurrence_move15_boundary (spike2AfterRecurrenceMove14
    (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))) b3.1 b3.2
  have b5 := spike2_recurrence_increment_boundary (spike2AfterRecurrenceMove15
    (spike2AfterRecurrenceMove14 (spike2AfterRecurrenceAdd
      (spike2AfterRecurrenceMove state)))) b4.1 b4.2
  have b6 := spike2_recurrence_backedge_boundary (spike2AfterRecurrenceIncrement
    (spike2AfterRecurrenceMove15 (spike2AfterRecurrenceMove14
      (spike2AfterRecurrenceAdd (spike2AfterRecurrenceMove state))))) b5.1 b5.2
  exact ⟨by simpa [spike2AfterRecurrenceTail] using b6.1,
    by simpa [spike2AfterRecurrenceTail] using b6.2.1⟩

end Spikes.Spike2Fibonacci.Windows

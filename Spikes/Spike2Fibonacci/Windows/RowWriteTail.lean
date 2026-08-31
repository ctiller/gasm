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
import Spikes.Spike2Fibonacci.Windows.RowWrite
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceTail

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowWriteTail :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.X86_64

/-- Exact selected body suffix from the real `WriteFile` import through the recurrence back edge.
The formatter need only establish the linked call/IAT boundary; all subsequent transitions remain
opaque producers composed through their small observations. -/
theorem spike2_write_tail_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713517)
    (iatTarget : (spike2AfterWriteFileCall state).rip = 0x140003010)
    (iatIndex : Gasm.Targets.Windows.findIatIndex (spike2AfterWriteFileCall state)
      (spike2AfterWriteFileCall state).rip = some 2)
    (steppedSafe : (spike2AfterWriteFileCall state).fault = none)
    (nextRip : (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1.rip = 5368713523)
    (nextSafe : (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7 state eventsRev
      (spike2AfterRecurrenceTail (writeFileHook (Event := AnyEvent)
        (spike2AfterWriteFileCall state)).1)
      (accumulateEvent eventsRev (writeFileHook (Event := AnyEvent)
        (spike2AfterWriteFileCall state)).2)
      (emittedBy (writeFileHook (Event := AnyEvent)
        (spike2AfterWriteFileCall state)).2) := by
  have write := spike2_writeFile_selected_prefix state eventsRev hrip iatTarget iatIndex steppedSafe
  have tail := spike2_recurrence_tail_selected_prefix
    (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1
    (accumulateEvent eventsRev (writeFileHook (Event := AnyEvent)
      (spike2AfterWriteFileCall state)).2) nextRip nextSafe
  simpa using ProductionPrefix.SelectedPrefix.append write tail

end Spikes.Spike2Fibonacci.Windows

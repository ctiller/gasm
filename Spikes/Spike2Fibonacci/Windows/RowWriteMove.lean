/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowWrite
import Spikes.Spike2Fibonacci.Windows.RowRecurrence1

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.X86_64

/-- Minimal append-only consumer: it does not inspect either producer's proof term.  It joins
the exact WriteFile import transition to the first opaque recurrence transition. -/
theorem spike2_write_move_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713517)
    (iatTarget : (spike2AfterWriteFileCall state).rip = 0x140003010)
    (iatIndex : Gasm.Targets.Windows.findIatIndex (spike2AfterWriteFileCall state)
      (spike2AfterWriteFileCall state).rip = some 2)
    (steppedSafe : (spike2AfterWriteFileCall state).fault = none)
    (nextRip : (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1.rip = 5368713523)
    (nextSafe : (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterRecurrenceMove (writeFileHook (Event := AnyEvent)
        (spike2AfterWriteFileCall state)).1)
      (accumulateEvent eventsRev (writeFileHook (Event := AnyEvent)
        (spike2AfterWriteFileCall state)).2)
      (emittedBy (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).2) := by
  have write := spike2_writeFile_selected_prefix state eventsRev hrip iatTarget iatIndex steppedSafe
  have move := spike2_recurrence_move_selected_prefix
    (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1
    (accumulateEvent eventsRev (writeFileHook (Event := AnyEvent)
      (spike2AfterWriteFileCall state)).2) nextRip nextSafe
  simpa using ProductionPrefix.SelectedPrefix.append write move

end Spikes.Spike2Fibonacci.Windows

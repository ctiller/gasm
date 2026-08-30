/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowExit

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets.X86_64

/-- Constructive 90-row selected termination for the complete linked Windows executable. -/
theorem spike2_selected_termination_constructive :
    selectedExecutionTerminates (Event := AnyEvent) false
      Gasm.Targets.selectedNonInputPlatformCall
      spike2Indexed 50000 spike2Executable.load = true := by
  rcases spike2_row_step.iterate spike2AfterPrologue ([] : List AnyEvent)
      spike2_initial_row_invariant with
    ⟨loopFinal, loopEventsRev, loopEmitted, loopFuel, loopPrefix, loopBound,
      loopInvariant⟩
  rcases spike2_exit_tail.run loopFinal loopEventsRev loopInvariant with
    ⟨result, tailBound⟩
  have usedWithin : 7 + loopFuel + result.fuel + 1 ≤ 50000 := by
    have loopLimit : loopFuel ≤ 90 * 285 := loopBound
    have tailLimit : result.fuel ≤ 3 := tailBound
    omega
  let slack := 50000 - (7 + loopFuel + result.fuel + 1)
  have totalFuel : (7 + loopFuel) + result.fuel + 1 + slack = 50000 := by
    dsimp [slack]
    omega
  rw [← totalFuel]
  have wholePrefix :=
    (spike2_prologue_selected_prefix.append loopPrefix).append result.certificate
  exact ProductionPrefix.SelectedPrefix.selectedExecutionTerminates_of_processExit_with_slack
    (allowHalted := false) wholePrefix result.exitStep slack

/-- The same certificate at the public executable-index expression, without simplifying it. -/
theorem spike2_selected_termination_constructive_indexed :
    selectedExecutionTerminates (Event := AnyEvent) false
      Gasm.Targets.selectedNonInputPlatformCall
      (indexInstructions spike2Executable.load.rip spike2Instructions) 50000
      spike2Executable.load = true := by
  change selectedExecutionTerminates (Event := AnyEvent) false
    Gasm.Targets.selectedNonInputPlatformCall spike2Indexed 50000 spike2Executable.load = true
  exact spike2_selected_termination_constructive

end Spikes.Spike2Fibonacci.Windows

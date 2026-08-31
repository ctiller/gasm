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
-/import Spikes.Spike2Fibonacci.Windows.RowExit

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowTermination :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Effects Gasm.Targets.X86_64

/-- Exact outcome of the complete selected Windows program.  The high-level proof composes the
    prologue, the bounded row transition, and the typed exit edge; instruction placement and
    branch widths remain sealed in those lower-level certificates. -/
theorem spike2_selected_outcome_constructive :
    ∃ final,
      @runProgramOutcomeWithLoops AnyEvent
          (Gasm.Core.Verification.standardWindowsRuntime AnyEvent)
          spike2Executable.load.rip spike2Instructions 50000 spike2Executable.load =
        .terminated (.processExit 0) final
          ((spike2ExpectedEventsRev 90).reverse ++
            [Inject.inject (ProcessEvent.exit 0)]) := by
  rcases spike2_row_step.iterate spike2AfterPrologue ([] : List AnyEvent)
      spike2_initial_row_invariant with
    ⟨loopFinal, loopEventsRev, loopEmitted, loopFuel, loopPrefix, loopBound,
      loopInvariant⟩
  rcases htail : spike2_exit_tail.run loopFinal loopEventsRev loopInvariant with
    ⟨result, tailBound⟩
  have usedWithin : 7 + loopFuel + result.fuel + 1 ≤ 50000 := by
    have loopLimit : loopFuel ≤ 90 * 285 := loopBound
    have tailLimit : result.fuel ≤ 3 := tailBound
    omega
  let slack := 50000 - (7 + loopFuel + result.fuel + 1)
  have totalFuel : (7 + loopFuel) + result.fuel + 1 + slack = 50000 := by
    dsimp [slack]
    omega
  let wholePrefix :=
    (spike2_prologue_selected_prefix.append loopPrefix).append result.certificate
  have outcome := wholePrefix.runProgramOutcomeLoop_of_processExit_with_slack
    result.exitStep slack
  have exitEvent : result.exitStep.event =
      some (Inject.inject (ProcessEvent.exit 0)) := by
    have := spike2_exit_tail_event loopFinal loopEventsRev loopInvariant
    rw [htail] at this
    exact this
  have exitSummary := spike2_exit_tail_summary loopFinal loopEventsRev loopInvariant
  rw [htail] at exitSummary
  change result.finalEventsRev = loopEventsRev ∧ result.code = 0 at exitSummary
  have finalEvents : result.finalEventsRev = spike2ExpectedEventsRev 90 :=
    exitSummary.1.trans loopInvariant.events
  refine ⟨result.exitStep.hooked, ?_⟩
  unfold runProgramOutcomeWithLoops
  change runProgramOutcomeLoop spike2Indexed 50000 spike2Executable.load [] = _
  rw [← totalFuel]
  rw [outcome]
  simp [exitEvent, exitSummary.2, finalEvents, accumulateEvent, List.reverse_cons]

/-- Constructive 90-row selected termination for the complete linked Windows executable. -/
theorem spike2_selected_termination_constructive :
    selectedExecutionTerminates (Event := AnyEvent) false
      selectedNonInputPlatformCall
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
      selectedNonInputPlatformCall
      (indexInstructions spike2Executable.load.rip spike2Instructions) 50000
      spike2Executable.load = true := by
  change selectedExecutionTerminates (Event := AnyEvent) false
    selectedNonInputPlatformCall spike2Indexed 50000 spike2Executable.load = true
  exact spike2_selected_termination_constructive

end Spikes.Spike2Fibonacci.Windows

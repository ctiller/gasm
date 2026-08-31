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

import Gasm.Targets.X86_64.SelectedLoopTermination
import Spikes.Spike2Fibonacci.Linux.NativeAdapter
import Spikes.Spike2Fibonacci.Linux.RowDecimalIteration
import Spikes.Spike2Fibonacci.Linux.Rows1To9

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64

/-- Minimal fixed-point boundary consumed after exactly ninety Linux Fibonacci rows.  The row
    producer remains responsible for establishing these projections; the exit adapter needs no
    whole-memory equality or closed evaluator result. -/
structure Spike2LinuxExitInvariant (state : X86_64MachineState)
    (_eventsRev : List AnyEvent) : Prop where
  rip : state.rip = spike2MainLoopRip
  counter : state.gprs .r13 = (91 : UInt64)
  fault : state.fault = none

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- Execute row 90 from the iterator's `Spike2LinuxRowEntry 89` endpoint and establish the exact
three-projection boundary consumed by the existing typed process-exit tail. -/
theorem row90Prefix_exitInvariant {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry 89 current next predecessor)
    (evidence : RowDecimalIteration.TwoDigitRowEvidence 89 current next predecessor eventsRev) :
    ∃ fuel finalEventsRev emitted final,
      0 < fuel ∧ fuel ≤ 285 ∧
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
        predecessor eventsRev final finalEventsRev emitted ∧
      Spike2LinuxExitInvariant final finalEventsRev := by
  rcases RowDecimalSchedule.twoDigitRowPrefix entry (by omega) evidence.opening
      evidence.openingRest evidence.realization with
    ⟨fuel, formatted, emitted, positive, fuelBound, certificate, _rsp, preservesR13,
      _preservesR14, _preservesR15, tailFrame⟩
  have formattedCounter : formatted.gprs .r13 = (90 : Nat).toUInt64 :=
    preservesR13.trans evidence.setupCounter
  have boundary := RowTailParametric.afterRecurrence_boundary formattedCounter tailFrame
  refine ⟨fuel, accumulateEvent eventsRev (RowTailParametric.writeEvent formatted),
    emitted ++ emittedBy (RowTailParametric.writeEvent formatted),
    RowTailParametric.afterRecurrence formatted, positive, ?_, certificate, ?_⟩
  · have digits := Stdlib.Fmt.decimalDigitCount_le_twenty current
    omega
  · exact ⟨boundary.1, by simpa using boundary.2.1, boundary.2.2⟩

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Typed terminal edge from the ninety-row Linux loop boundary.  Four ordinary selected steps
    reach the linked `SYSCALL`; the syscall itself is retained as a classified process-exit step. -/
def spike2_exit_tail : SelectedProcessExitTail selectedNonInputPlatformCall spike2Indexed
    Spike2LinuxExitInvariant where
  maxFuel := 4
  run state eventsRev holds := by
    have header := spike2_exit_header_selected_prefix state eventsRev
      holds.rip holds.counter holds.fault
    have exitRip := spike2_after_exit_header_rip state holds.rip holds.counter
    have setup := spike2_exit_setup_selected_prefix state eventsRev exitRip holds.fault
    exact ⟨{
      fuel := 4
      final := spike2BeforeExitSyscall state
      finalEventsRev := eventsRev
      emitted := []
      code := 0
      certificate := by simpa using header.append setup
      exitStep := spike2_exit_syscall_selected_step state exitRip holds.fault },
      Nat.le_refl 4⟩

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Close any structural prefix which reaches the ninety-row boundary into the unchanged public
    50,000-step termination judgment.  This is the final composition seam: the remaining row proof
    need only produce the prefix and the three boundary projections above. -/
theorem spike2_selected_termination_of_prefix {fuel : Nat} {state : X86_64MachineState}
    {eventsRev emitted : List AnyEvent}
    (certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
      spike2Executable.load ([] : List AnyEvent) state eventsRev emitted)
    (holds : Spike2LinuxExitInvariant state eventsRev)
    (within : fuel + 5 ≤ 50000) :
    selectedExecutionTerminates (Event := AnyEvent) true selectedNonInputPlatformCall
      spike2Indexed 50000 spike2Executable.load = true := by
  rcases spike2_exit_tail.run state eventsRev holds with ⟨result, tailBound⟩
  have usedWithin : fuel + result.fuel + 1 ≤ 50000 := by
    have : result.fuel ≤ 4 := tailBound
    omega
  let slack := 50000 - (fuel + result.fuel + 1)
  have totalFuel : fuel + result.fuel + 1 + slack = 50000 := by
    dsimp [slack]
    omega
  rw [← totalFuel]
  exact (certificate.append result.certificate).selectedExecutionTerminates_of_processExit_with_slack
    result.exitStep slack

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- Compose an exact load-through-row-9 prefix, eighty constructive arbitrary-digit rows, the
separate row-90 producer, and the existing typed exit tail into the unchanged public termination
judgment.  The remaining work is explicit in the arguments: concrete callers must construct the
per-row physical decimal evidence and account for the initial prefix fuel. -/
theorem spike2_selected_termination_of_decimal_rows
    {initialFuel : Nat} {row10State : X86_64MachineState}
    {row10EventsRev initialEmitted : List AnyEvent}
    (initialPrefix : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed
      initialFuel spike2Executable.load ([] : List AnyEvent) row10State row10EventsRev
      initialEmitted)
    (initialHolds : RowDecimalIteration.TwoDigitIterationInvariant 0 row10State row10EventsRev)
    (evidence : ∀ completed current next predecessor eventsRev,
      completed < 80 →
      Spike2LinuxRowEntry (completed + 9) current next predecessor →
      RowDecimalIteration.TwoDigitRowEvidence (completed + 9) current next predecessor eventsRev)
    (finalEvidence : ∀ current next final finalEventsRev,
      Spike2LinuxRowEntry 89 current next final →
      RowDecimalIteration.TwoDigitRowEvidence 89 current next final finalEventsRev)
    (within : initialFuel + 80 * 285 + 285 + 5 ≤ 50000) :
    selectedExecutionTerminates (Event := AnyEvent) true selectedNonInputPlatformCall
      spike2Indexed 50000 spike2Executable.load = true := by
  rcases RowDecimalIteration.iterateRows10Through89 evidence row10State row10EventsRev
      initialHolds with
    ⟨row90State, row90EventsRev, loopEmitted, loopFuel, loopPrefix, loopBound, row90Holds⟩
  rcases (RowDecimalIteration.invariantEighty_iff_rowNinetyEntry
      row90State row90EventsRev).mp row90Holds with ⟨current, next, row90Entry⟩
  rcases row90Prefix_exitInvariant row90Entry
      (finalEvidence current next row90State row90EventsRev row90Entry) with
    ⟨row90Fuel, finalEventsRev, row90Emitted, final, row90Positive, row90Bound,
      row90Prefix, exitInvariant⟩
  have fullPrefix := initialPrefix.append (loopPrefix.append row90Prefix)
  have fullWithin : initialFuel + (loopFuel + row90Fuel) + 5 ≤ 50000 := by
    omega
  exact spike2_selected_termination_of_prefix fullPrefix exitInvariant fullWithin

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- Close the unchanged termination proposition from the concrete load-through-row-9 prefix and
the remaining parameterized physical row evidence.  The fixed initial fuel is ordinary arithmetic
over the exact 380-transition prefix and two 64-transition parametric rows. -/
theorem spike2_selected_termination_of_row_evidence
    (row8Needs : Row8Parametric.LocalRowNeeds spike2Row7AfterRecurrence)
    (row9Needs : Row8Parametric.LocalRowNeeds
      (Row8Parametric.afterRecurrence spike2Row7AfterRecurrence))
    (evidence : ∀ completed current next predecessor eventsRev,
      completed < 80 →
      Spike2LinuxRowEntry (completed + 9) current next predecessor →
      RowDecimalIteration.TwoDigitRowEvidence (completed + 9) current next predecessor eventsRev)
    (finalEvidence : ∀ current next final finalEventsRev,
      Spike2LinuxRowEntry 89 current next final →
      RowDecimalIteration.TwoDigitRowEvidence 89 current next final finalEventsRev) :
    selectedExecutionTerminates (Event := AnyEvent) true selectedNonInputPlatformCall
      spike2Indexed 50000 spike2Executable.load = true := by
  rcases spike2_prologue_to_row10_entry row8Needs row9Needs with
    ⟨row10EventsRev, initialEmitted, initialPrefix, initialHolds⟩
  exact spike2_selected_termination_of_decimal_rows initialPrefix initialHolds evidence finalEvidence
    (by omega)

end Spikes.Spike2Fibonacci.Linux

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

import Spikes.Spike2Fibonacci.Linux.RowTwoDigitIndex
import Spikes.Spike2Fibonacci.Linux.RowTailParametric
import Spikes.Spike2Fibonacci.Linux.DecimalAuthority

/-!
# Bounded two-digit-index row producer for Linux Spike 2

Rows 10 through 90 share a fixed 26-transition opening, an arbitrary-digit UInt64 decimal
schedule, and a fixed 19-transition tail.  This module joins those three independently checked
producers and retains the schedule's quantitative fuel bound.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.DecimalSchedule
open Spikes.Spike2Fibonacci
open Stdlib.Fmt

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

namespace RowDecimalSchedule

open Row8Parametric

/-- The decimal realization ends precisely where the arbitrary-endpoint row tail has its local
execution evidence. -/
abbrev TailReadyCallerFrame : CallerFrame :=
  fun _ formatted => RowTailParametric.Frame formatted

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- A continuing two-digit-index row has a selected prefix bounded by its fixed opening/tail
cost plus twelve transitions for each value digit. -/
theorem twoDigitRowPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (twoDigit : 10 ≤ completed + 1)
    (openingFrame : OpeningFrame predecessor)
    (openingRestFrame : RowTwoDigitIndex.TwoDigitOpeningRestFrame predecessor)
    (realization : UInt64DecimalScheduleRealization selectedNonInputPlatformCall spike2Indexed 20
      current (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor) eventsRev
      TailReadyCallerFrame) :
    ∃ requiredFuel formatted emitted,
      0 < requiredFuel ∧
      requiredFuel ≤ 45 + 12 * decimalDigitCount current ∧
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed requiredFuel
        predecessor eventsRev (RowTailParametric.afterRecurrence formatted)
        (accumulateEvent eventsRev (RowTailParametric.writeEvent formatted))
        (emitted ++ emittedBy (RowTailParametric.writeEvent formatted)) ∧
      formatted.rsp = (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).rsp ∧
      formatted.gprs .r13 =
        (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r13 ∧
      formatted.gprs .r14 =
        (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r14 ∧
      formatted.gprs .r15 =
        (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r15 ∧
      RowTailParametric.Frame formatted := by
  have opening := RowTwoDigitIndex.openingPrefix (eventsRev := eventsRev)
    entry twoDigit openingFrame
  have rest := RowTwoDigitIndex.openingRestPrefix (eventsRev := eventsRev) openingRestFrame
  rcases realization.selectedPrefix_bounded with
    ⟨decimalFuel, formatted, finalEventsRev, emitted, decimalBound, decimalPrefix,
      eventsPreserved, restoredRsp, _advancedCursor, _clearedCount, _formatBytes,
      _preservesR12, preservesR13, preservesR14, preservesR15, tailFrame⟩
  subst finalEventsRev
  have tail := RowTailParametric.selectedPrefix (eventsRev := eventsRev) tailFrame
  refine ⟨26 + decimalFuel + 19, formatted, emitted, by omega, ?_, ?_, restoredRsp,
    preservesR13, preservesR14, preservesR15, tailFrame⟩
  · omega
  · simpa using ((opening.append rest).append decimalPrefix).append tail

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
/-- The bounded arbitrary-digit row producer also exposes the typed successor entry.  The three
opening projections are explicit because reducing the full two-digit opening merely to rediscover
register preservation is itself an unbounded elaboration trap; concrete callers can establish
these local facts once at their boundary. -/
theorem twoDigitRowPrefix_successor {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (twoDigit : 10 ≤ completed + 1)
    (nextContinues : completed + 1 < 90)
    (openingFrame : OpeningFrame predecessor)
    (openingRestFrame : RowTwoDigitIndex.TwoDigitOpeningRestFrame predecessor)
    (setupCounter : (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r13 =
      (completed + 1).toUInt64)
    (setupCurrent : (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r14 = current)
    (setupNext : (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r15 = next)
    (realization : UInt64DecimalScheduleRealization selectedNonInputPlatformCall spike2Indexed 20
      current (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor) eventsRev
      TailReadyCallerFrame) :
    ∃ requiredFuel formatted emitted,
      0 < requiredFuel ∧
      requiredFuel ≤ 45 + 12 * decimalDigitCount current ∧
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed requiredFuel
        predecessor eventsRev (RowTailParametric.afterRecurrence formatted)
        (accumulateEvent eventsRev (RowTailParametric.writeEvent formatted))
        (emitted ++ emittedBy (RowTailParametric.writeEvent formatted)) ∧
      Spike2LinuxRowEntry (completed + 1) next (current + next)
        (RowTailParametric.afterRecurrence formatted) := by
  rcases twoDigitRowPrefix entry twoDigit openingFrame openingRestFrame realization with
    ⟨requiredFuel, formatted, emitted, positive, fuelBound, rowCertificate, _rsp, preservesR13,
      preservesR14, preservesR15, tailFrame⟩
  have formattedCounter : formatted.gprs .r13 = (completed + 1).toUInt64 := by
    exact preservesR13.trans setupCounter
  have formattedCurrent : formatted.gprs .r14 = current := by
    exact preservesR14.trans setupCurrent
  have formattedNext : formatted.gprs .r15 = next := by
    exact preservesR15.trans setupNext
  exact ⟨requiredFuel, formatted, emitted, positive, fuelBound, rowCertificate,
    RowTailParametric.afterRecurrence_entry formattedCounter formattedCurrent formattedNext
      tailFrame nextContinues⟩

end RowDecimalSchedule

end Spikes.Spike2Fibonacci.Linux

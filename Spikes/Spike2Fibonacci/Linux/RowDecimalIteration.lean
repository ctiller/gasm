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
import Spikes.Spike2Fibonacci.Linux.RowDecimalSchedule

/-!
# Bounded iteration for Spike 2 Linux two-digit rows

This module turns the arbitrary-digit row producer into the quantitative loop interface consumed
by the termination proof.  Concrete physical decimal realizations remain explicit inputs: the
iterator neither evaluates the machine nor hides boundary states behind definitional equality.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.DecimalSchedule
open Spikes.Spike2Fibonacci
open Stdlib.Fmt

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

namespace RowDecimalIteration

open Row8Parametric
open RowDecimalSchedule

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- The exact local evidence consumed by one row in the two-digit-index schedule.  Its decimal
realization is tied to the production index and begins at the actual opening endpoint. -/
structure TwoDigitRowEvidence (completed : Nat) (current next : UInt64)
    (predecessor : X86_64MachineState) (eventsRev : List AnyEvent) : Prop where
  opening : OpeningFrame predecessor
  openingRest : RowTwoDigitIndex.TwoDigitOpeningRestFrame predecessor
  setupCounter : (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r13 =
    (completed + 1).toUInt64
  setupCurrent : (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r14 = current
  setupNext : (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor).gprs .r15 = next
  realization : UInt64DecimalScheduleRealization selectedNonInputPlatformCall spike2Indexed 20
    current (RowTwoDigitIndex.afterTwoDigitValueSetup predecessor) eventsRev
    TailReadyCallerFrame

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
/-- Zero-based iteration state for rows 10 through 89.  At iteration `completed`, exactly
`completed + 9` rows have finished, and the six projection-only facts in `Spike2LinuxRowEntry`
describe the next production row. -/
def TwoDigitIterationInvariant (completed : Nat) (state : X86_64MachineState)
    (_eventsRev : List AnyEvent) : Prop :=
  ∃ current next, Spike2LinuxRowEntry (completed + 9) current next state

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Construct the bounded production-loop step for rows 10 through 89.  Each row uses at most
`45 + 12 * 20 = 285` selected transitions; after eighty iterations the invariant is the typed
entry for row 90. -/
def twoDigitRowLoopStep
    (evidence : ∀ completed current next predecessor eventsRev,
      completed < 80 →
      Spike2LinuxRowEntry (completed + 9) current next predecessor →
      TwoDigitRowEvidence (completed + 9) current next predecessor eventsRev) :
    SelectedFuelBoundedInvariantLoopStep selectedNonInputPlatformCall spike2Indexed 80
      TwoDigitIterationInvariant where
  maxFuel := 285
  run completed predecessor eventsRev within holds := by
    rcases holds with ⟨current, next, entry⟩
    have rowEvidence := evidence completed current next predecessor eventsRev within entry
    rcases twoDigitRowPrefix_successor entry (by omega) (by omega) rowEvidence.opening
        rowEvidence.openingRest rowEvidence.setupCounter rowEvidence.setupCurrent
        rowEvidence.setupNext rowEvidence.realization with
      ⟨fuel, formatted, emitted, positive, fuelBound, certificate, successor⟩
    refine ⟨fuel, RowTailParametric.afterRecurrence formatted,
      accumulateEvent eventsRev (RowTailParametric.writeEvent formatted),
      emitted ++ emittedBy (RowTailParametric.writeEvent formatted), positive, ?_, certificate, ?_⟩
    · have digits := decimalDigitCount_le_twenty current
      omega
    · exact ⟨next, current + next, by simpa [Nat.add_assoc] using successor⟩

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Iterate the constructive row evidence exactly eighty times, retaining an exact selected prefix,
the global fuel bound, and the row-90 entry boundary. -/
theorem iterateRows10Through89
    (evidence : ∀ completed current next predecessor eventsRev,
      completed < 80 →
      Spike2LinuxRowEntry (completed + 9) current next predecessor →
      TwoDigitRowEvidence (completed + 9) current next predecessor eventsRev)
    (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (holds : TwoDigitIterationInvariant 0 state eventsRev) :
    ∃ final finalEventsRev emitted totalFuel,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed totalFuel
        state eventsRev final finalEventsRev emitted ∧
      totalFuel ≤ 80 * 285 ∧
      TwoDigitIterationInvariant 80 final finalEventsRev := by
  exact (twoDigitRowLoopStep evidence).iterate state eventsRev holds

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
/-- `Spike2LinuxRowEntry 89` means that 89 rows are already complete and execution is positioned
at the main-loop header before row 90.  This makes the iterator's endpoint explicit and prevents
an off-by-one interpretation of the zero-based iteration index. -/
theorem invariantEighty_iff_rowNinetyEntry (state : X86_64MachineState)
    (eventsRev : List AnyEvent) :
    TwoDigitIterationInvariant 80 state eventsRev ↔
      ∃ current next, Spike2LinuxRowEntry 89 current next state := by
  simp [TwoDigitIterationInvariant]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Rows 10 through 89, row 90 at the same per-pass bound, the four-step exit tail, and the typed
exit transition consume at most 23,090 steps.  A whole-program closure must additionally account
for the exact load-through-row-9 prefix; this theorem deliberately does not erase that cost. -/
theorem decimalRowsAndExit_fuel :
    80 * 285 + 285 + 4 + 1 = 23090 := by
  omega

end RowDecimalIteration

end Spikes.Spike2Fibonacci.Linux

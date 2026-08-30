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

import Spikes.Spike2Fibonacci.Linux.Row8Parametric
import Spikes.Spike2Fibonacci.Linux.DecimalAuthority

/-!
# Projection-only invariant for continuing Spike 2 Linux rows

This module names the weakest local premises consumed by the parametric row slices.  The live
Fibonacci boundary is re-established from the recurrence instructions themselves.  No theorem
compares memories or whole machine states across a row boundary.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

namespace Row8Parametric

/-- One-past the final byte observed by a 64-bit read at the linked row back-edge.  Row-local
writes must begin at or above this boundary before row-code observations can be immutable. -/
def spike2RowLinkedTextUpper : Nat := 4198709

/-- Projection-only physical bounds which advance the accepted decimal text authority through
the concrete two extraction and two reverse-write passes. -/
structure FormatterAuthorityFrame (predecessor : X86_64MachineState) : Prop where
  entry : Spike2DecimalTextAuthority (afterValueSetup predecessor)
  extractionFirstNoWrap : ((afterValueSetup predecessor).rsp - 8).toNat + 8 ≤ 2 ^ 64
  extractionFirstAbove : spike2RowLinkedTextUpper ≤ ((afterValueSetup predecessor).rsp - 8).toNat
  extractionSecondNoWrap : ((afterExtractionFirst predecessor).rsp - 8).toNat + 8 ≤ 2 ^ 64
  extractionSecondAbove : spike2RowLinkedTextUpper ≤ ((afterExtractionFirst predecessor).rsp - 8).toNat
  writeFirstNoWrap : ((afterExtraction predecessor).gprs .rdi).toNat + 1 ≤ 2 ^ 64
  writeFirstAbove : spike2RowLinkedTextUpper ≤ ((afterExtraction predecessor).gprs .rdi).toNat
  writeSecondNoWrap : ((afterWriteFirst predecessor).gprs .rdi).toNat + 1 ≤ 2 ^ 64
  writeSecondAbove : spike2RowLinkedTextUpper ≤ ((afterWriteFirst predecessor).gprs .rdi).toNat

/-- Exact byte-write bounds for the CR/LF suffix. -/
structure TailAuthorityFrame (predecessor : X86_64MachineState) : Prop where
  carriageNoWrap : ((beforeCarriageReturnStore predecessor).gprs .rdi).toNat + 1 ≤ 2 ^ 64
  carriageAbove : spike2RowLinkedTextUpper ≤ ((beforeCarriageReturnStore predecessor).gprs .rdi).toNat
  lineFeedNoWrap : ((beforeLineFeedStore predecessor).gprs .rdi).toNat + 1 ≤ 2 ^ 64
  lineFeedAbove : spike2RowLinkedTextUpper ≤ ((beforeLineFeedStore predecessor).gprs .rdi).toNat

/-- The local instruction, safety, and physical authority projections consumed by a continuing
one-digit/two-value-digit row.  This is the backward-collected weakest-premise boundary for
`rowPrefix`; it contains no total-memory or total-state equality. -/
structure LocalRowNeeds (predecessor : X86_64MachineState) : Prop where
  opening : OpeningFrame predecessor
  openingRest : OpeningRestFrame predecessor
  formatter : FormatterFrame predecessor
  tail : TailFrame predecessor
  formatterAuthority : FormatterAuthorityFrame predecessor
  tailAuthority : TailAuthorityFrame predecessor

/-- The live loop boundary paired with the exact local physical needs of the next row. -/
structure OneDigitTwoPassInvariant (completed : Nat) (current next : UInt64)
    (predecessor : X86_64MachineState) : Prop where
  entry : Spike2LinuxRowEntry completed current next predecessor
  oneDigit : completed + 1 < 10
  needs : LocalRowNeeds predecessor

private theorem recurrence_counter_local (state : X86_64MachineState) :
    (X86_64Instruction.step (jmp_rel32 4294967027)
      (runLocalSteps recurrenceHeadCode state)).gprs .r13 = state.gprs .r13 + 1 := by
  rfl

private theorem recurrence_current_local (state : X86_64MachineState) :
    (X86_64Instruction.step (jmp_rel32 4294967027)
      (runLocalSteps recurrenceHeadCode state)).gprs .r14 = state.gprs .r15 := by
  rfl

private theorem recurrence_next_local (state : X86_64MachineState) :
    (X86_64Instruction.step (jmp_rel32 4294967027)
      (runLocalSteps recurrenceHeadCode state)).gprs .r15 =
        state.gprs .r14 + state.gprs .r15 := by
  rfl

private theorem backEdge_rip_local (state : X86_64MachineState)
    (rip : state.rip = 4198701) :
    (X86_64Instruction.step (jmp_rel32 4294967027) state).rip = spike2MainLoopRip := by
  change state.rip + 5 + signExtend32To64 4294967027 = _
  rw [rip]
  decide

theorem afterRecurrence_rip (predecessor : X86_64MachineState)
    (tail : TailFrame predecessor) :
    (afterRecurrence predecessor).rip = spike2MainLoopRip := by
  exact backEdge_rip_local (beforeBackEdge predecessor) tail.backRip

theorem afterRecurrence_counter {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (tail : TailFrame predecessor) :
    (afterRecurrence predecessor).gprs .r13 = (completed + 2).toUInt64 := by
  change (X86_64Instruction.step (jmp_rel32 4294967027)
    (runLocalSteps recurrenceHeadCode (afterWriteSyscall predecessor))).gprs .r13 = _
  rw [recurrence_counter_local, tail.liveR13, entry.counter]
  calc
    UInt64.ofNat (completed + 1) + 1 =
        UInt64.ofNat ((completed + 1) + 1) := by
      exact (UInt64.ofNat_add (completed + 1) 1).symm
    _ = UInt64.ofNat (completed + 2) := by congr 1 <;> omega

theorem afterRecurrence_current {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (tail : TailFrame predecessor) :
    (afterRecurrence predecessor).gprs .r14 = next := by
  change (X86_64Instruction.step (jmp_rel32 4294967027)
    (runLocalSteps recurrenceHeadCode (afterWriteSyscall predecessor))).gprs .r14 = _
  rw [recurrence_current_local, tail.liveR15, entry.next_value]

theorem afterRecurrence_next {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (tail : TailFrame predecessor) :
    (afterRecurrence predecessor).gprs .r15 = current + next := by
  change (X86_64Instruction.step (jmp_rel32 4294967027)
    (runLocalSteps recurrenceHeadCode (afterWriteSyscall predecessor))).gprs .r15 = _
  rw [recurrence_next_local, tail.liveR14, tail.liveR15,
    entry.current_value, entry.next_value]

/-- The recurrence and back edge re-establish the live next-row entry using only local register,
RIP, and fault projections. -/
theorem afterRecurrence_entry {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (tail : TailFrame predecessor)
    (nextContinues : completed + 1 < 90) :
    Spike2LinuxRowEntry (completed + 1) next (current + next)
      (afterRecurrence predecessor) where
  completed_lt := nextContinues
  rip := afterRecurrence_rip predecessor tail
  counter := by simpa [Nat.add_assoc] using afterRecurrence_counter entry tail
  current_value := afterRecurrence_current entry tail
  next_value := afterRecurrence_next entry tail
  safe := tail.backSafe

/-- Consume exactly the backward-collected needs for one continuing row. -/
theorem OneDigitTwoPassInvariant.rowPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (invariant : OneDigitTwoPassInvariant completed current next predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 64
      predecessor eventsRev (afterRecurrence predecessor)
      (accumulateEvent eventsRev (writeEvent predecessor))
      (emittedBy (writeEvent predecessor)) :=
  Row8Parametric.rowPrefix invariant.entry invariant.oneDigit invariant.needs.opening
    invariant.needs.openingRest invariant.needs.formatter invariant.needs.tail

/-- Forward half of the invariant discipline: after consuming a row, the recurrence supplies
the next live entry; only the next row's local physical frame remains to be provided. -/
theorem OneDigitTwoPassInvariant.next {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    (invariant : OneDigitTwoPassInvariant completed current next predecessor)
    (nextContinues : completed + 1 < 90)
    (nextOneDigit : completed + 2 < 10)
    (nextNeeds : LocalRowNeeds (afterRecurrence predecessor)) :
    OneDigitTwoPassInvariant (completed + 1) next (current + next)
      (afterRecurrence predecessor) where
  entry := afterRecurrence_entry invariant.entry invariant.needs.tail nextContinues
  oneDigit := by simpa [Nat.add_assoc] using nextOneDigit
  needs := nextNeeds

/-- Row 9 reuses the same symbolic 64-step producer at Row 8's exact endpoint.  No Row 8 state is
unfolded and the endpoint joins syntactically through `afterRecurrence`. -/
theorem row9_reuse {row8Predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (row8 : OneDigitTwoPassInvariant 7 21 34 row8Predecessor)
    (row9Needs : LocalRowNeeds (afterRecurrence row8Predecessor)) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 64
      (afterRecurrence row8Predecessor)
      (accumulateEvent eventsRev (writeEvent row8Predecessor))
      (afterRecurrence (afterRecurrence row8Predecessor))
      (accumulateEvent (accumulateEvent eventsRev (writeEvent row8Predecessor))
        (writeEvent (afterRecurrence row8Predecessor)))
      (emittedBy (writeEvent (afterRecurrence row8Predecessor))) := by
  have row9 := row8.next (by omega) (by omega) row9Needs
  exact row9.rowPrefix

/-- A schedule-sized two-row producer.  The Row 8 endpoint is definitionally the Row 9 entry,
so the two opaque 64-step rows append without a state transport premise. -/
theorem rows8And9_reuse {row8Predecessor : X86_64MachineState}
    {eventsRev : List AnyEvent}
    (row8 : OneDigitTwoPassInvariant 7 21 34 row8Predecessor)
    (row9Needs : LocalRowNeeds (afterRecurrence row8Predecessor)) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 128
      row8Predecessor eventsRev
      (afterRecurrence (afterRecurrence row8Predecessor))
      (accumulateEvent (accumulateEvent eventsRev (writeEvent row8Predecessor))
        (writeEvent (afterRecurrence row8Predecessor)))
      (emittedBy (writeEvent row8Predecessor) ++
        emittedBy (writeEvent (afterRecurrence row8Predecessor))) := by
  have first := row8.rowPrefix (eventsRev := eventsRev)
  have second := row9_reuse (eventsRev := eventsRev) row8 row9Needs
  simpa using first.append second

end Row8Parametric

end Spikes.Spike2Fibonacci.Linux

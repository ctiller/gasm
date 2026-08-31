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

import Spikes.Spike2Fibonacci.Linux.Rows1To6
import Spikes.Spike2Fibonacci.Linux.Row7
import Spikes.Spike2Fibonacci.Linux.RowLoopInvariant
import Spikes.Spike2Fibonacci.Linux.RowDecimalIteration

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Spikes.Spike2Fibonacci

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Local proposition-level composition for independently cached closed row producers.  The result
retains the exact chronological delta `firstEmitted ++ secondEmitted`; only accumulator expressions
are existential because no later Spike 2 phase observes their syntax.  Incompatible machine
endpoints cannot be supplied: both premises share the same `middle` index. -/
private theorem appendClosedRow {firstFuel secondFuel : Nat}
    {initial middle final : X86_64MachineState}
    {secondFinalEventsRev secondEmitted : List AnyEvent}
    (first : ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed firstFuel
        initial ([] : List AnyEvent) middle eventsRev emitted)
    (second : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed secondFuel
      middle ([] : List AnyEvent) final secondFinalEventsRev secondEmitted) :
    ∃ eventsRev firstEmitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed
        (firstFuel + secondFuel) initial ([] : List AnyEvent) final eventsRev
        (firstEmitted ++ secondEmitted) := by
  rcases first with ⟨eventsRev, firstEmitted, certificate⟩
  exact ⟨_, firstEmitted, certificate.append (second.rebaseEvents_empty eventsRev)⟩

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Existential view of `appendClosedRow` for consumers which do not inspect the exact emitted
delta retained by the underlying certificate. -/
private theorem appendClosedRowExists {firstFuel secondFuel : Nat}
    {initial middle final : X86_64MachineState}
    {secondFinalEventsRev secondEmitted : List AnyEvent}
    (first : ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed firstFuel
        initial ([] : List AnyEvent) middle eventsRev emitted)
    (second : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed secondFuel
      middle ([] : List AnyEvent) final secondFinalEventsRev secondEmitted) :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed
        (firstFuel + secondFuel) initial ([] : List AnyEvent) final eventsRev emitted := by
  rcases appendClosedRow first second with ⟨eventsRev, firstEmitted, certificate⟩
  exact ⟨eventsRev, firstEmitted ++ secondEmitted, certificate⟩

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- The production prologue and rows 1 through 7 reach the actual Row 7 endpoint in exactly 380
selected transitions. -/
theorem spike2_prologue_to_row7_selected_prefix :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 380
        spike2Executable.load ([] : List AnyEvent) spike2Row7AfterRecurrence eventsRev emitted := by
  exact appendClosedRowExists
    (firstFuel := 316) (secondFuel := 64)
    (initial := spike2Executable.load)
    (middle := spike2Row6AfterRecurrence)
    (final := spike2Row7AfterRecurrence)
    (secondFinalEventsRev := spike2Row7WriteEventsRev)
    (secondEmitted := emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).2)
    spike2_prologue_to_row6_selected_prefix spike2_row7_selected_prefix

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
/-- The reviewed Row 7 boundary is the projection-only entry before executing row 8. -/
theorem spike2_row8_entry : Spike2LinuxRowEntry 7 21 34 spike2Row7AfterRecurrence := by
  rcases spike2_row7_after_recurrence_boundary with
    ⟨rip, counter, current, next, _rsp, fault⟩
  exact ⟨by omega, rip, by simpa using counter, current, next, fault⟩

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- Extend the exact real-state prefix through parametric rows 8 and 9.  The endpoint is iteration
zero for the bounded rows-10-through-89 producer: nine rows are complete and row 10 is next. -/
theorem spike2_prologue_to_row10_entry
    (row8Needs : Row8Parametric.LocalRowNeeds spike2Row7AfterRecurrence)
    (row9Needs : Row8Parametric.LocalRowNeeds
      (Row8Parametric.afterRecurrence spike2Row7AfterRecurrence)) :
    ∃ eventsRev emitted,
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 508
        spike2Executable.load ([] : List AnyEvent)
        (Row8Parametric.afterRecurrence
          (Row8Parametric.afterRecurrence spike2Row7AfterRecurrence)) eventsRev emitted ∧
      RowDecimalIteration.TwoDigitIterationInvariant 0
        (Row8Parametric.afterRecurrence
          (Row8Parametric.afterRecurrence spike2Row7AfterRecurrence)) eventsRev := by
  rcases spike2_prologue_to_row7_selected_prefix with ⟨events7, emitted7, rows17⟩
  let row8 : Row8Parametric.OneDigitTwoPassInvariant 7 21 34
      spike2Row7AfterRecurrence := ⟨spike2_row8_entry, by omega, row8Needs⟩
  have rows89 := Row8Parametric.rows8And9_reuse (eventsRev := events7) row8 row9Needs
  have rows19 := rows17.append rows89
  have row9Entry : Spike2LinuxRowEntry 8 34 (21 + 34)
      (Row8Parametric.afterRecurrence spike2Row7AfterRecurrence) :=
    Row8Parametric.afterRecurrence_entry spike2_row8_entry row8Needs.tail (by omega)
  have row10Entry : Spike2LinuxRowEntry 9 (21 + 34) (34 + (21 + 34))
      (Row8Parametric.afterRecurrence
        (Row8Parametric.afterRecurrence spike2Row7AfterRecurrence)) :=
    Row8Parametric.afterRecurrence_entry row9Entry row9Needs.tail (by omega)
  exact ⟨_, _, by simpa using rows19, ⟨21 + 34, 34 + (21 + 34), row10Entry⟩⟩

end Spikes.Spike2Fibonacci.Linux

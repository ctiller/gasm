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

import Spikes.Spike2Fibonacci.Linux.DecimalPhases
import Spikes.Spike2Fibonacci.Linux.Row1

/-!
# Row-one validation of the linked decimal bridge

This is deliberately an anchor, not an alternate formatter proof: it instantiates the new
actual-index layout/runtime bridge at the existing first reachable decimal entry.  It confirms
the bridge's stateful ordinary-code condition against real Linux text memory.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_row1_extraction_ordinary :
    Spike2ExtractionOrdinary 236 spike2Row1AfterValueSetup := by
  constructor <;> constructor <;> decide

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
private theorem spike2_row1_write_ordinary :
    Spike2WriteOrdinary 243 spike2Row1AfterExtraction := by
  constructor <;> constructor <;> decide

/-- The existing row-one extraction state satisfies the generic final-link bridge. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2_row1_extraction_selected_prefix_via_layout :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7
      spike2Row1AfterValueSetup ([] : List AnyEvent) spike2Row1AfterExtraction [] [] := by
  have pass := spike2ExtractionLinkedLayout_selectedPass (stackLower := 0)
    spike2Row1AfterValueSetup rfl
    (by
      refine ⟨rfl, ?_, by decide, rfl⟩
      change 8 ≤ 140737488289656
      omega) (by constructor <;> decide)
    spike2_row1_extraction_ordinary (Or.inr (by
      simp only [X86BranchCondition.holds]
      decide))
  exact pass.selectedPrefix

/-- The existing row-one reverse write state satisfies the generic final-link bridge. -/
/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2_row1_write_selected_prefix_via_layout :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5
      spike2Row1AfterExtraction ([] : List AnyEvent) spike2Row1AfterWrite [] [] := by
  have pass := spike2WriteLinkedLayout_selectedPass
    (stackUpper := 18446744073709551615) (outputLimit := 18446744073709551615)
    spike2Row1AfterExtraction rfl
    (by
      refine ⟨?_, ?_, by decide, rfl⟩
      · change 140737488289648 + 8 ≤ 18446744073709551615
        omega
      · change 140737488289729 < 18446744073709551615
        omega) (by constructor <;> decide)
    spike2_row1_write_ordinary (Or.inr (by
      simp only [X86BranchCondition.holds]
      decide))
  exact pass.selectedPrefix

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
private theorem spike2_row1_completed_zero (completed : Nat)
    (within : completed < Stdlib.Fmt.decimalDigitCount (1 : UInt64)) : completed = 0 := by
  have digits : Stdlib.Fmt.decimalDigitCount (1 : UInt64) = 1 := by
    rw [Stdlib.Fmt.decimalDigitCount_eq_digits_length]
    change (Stdlib.Fmt.digits 1).length = 1
    rw [Stdlib.Fmt.digits_single 1 (by omega)]
    rfl
  omega

/-- The one-digit row-one extraction frame validates the phase witness at its only pass. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
private theorem spike2_row1_extraction_loop_witness :
    Spike2ExtractionLoopWitness 1 0 spike2Row1AfterValueSetup ([] : List AnyEvent) := by
  constructor
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    rfl
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    refine ⟨rfl, ?_, by decide, rfl⟩
    change 8 ≤ 140737488289656
    omega
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    constructor <;> decide
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    exact spike2_row1_extraction_ordinary
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    exact Or.inr (by
      simp only [X86BranchCondition.holds]
      decide)

/-- The one-digit row-one write frame validates the phase witness at its only pass. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
private theorem spike2_row1_write_loop_witness :
    Spike2WriteLoopWitness 1 18446744073709551615 18446744073709551615
      spike2Row1AfterExtraction ([] : List AnyEvent) := by
  constructor
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    rfl
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    refine ⟨?_, ?_, by decide, rfl⟩
    · change 140737488289648 + 8 ≤ 18446744073709551615
      omega
    · change 140737488289729 < 18446744073709551615
      omega
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    constructor <;> decide
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    exact spike2_row1_write_ordinary
  · intro completed within
    have hzero := spike2_row1_completed_zero completed within
    subst completed
    exact Or.inr (by
      simp only [X86BranchCondition.holds]
      decide)

/-- The generic extraction phase is realized by the actual one-digit Linux row-one frame. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem spike2_row1_extraction_phase :
    DecimalExtractionPhase selectedNonInputPlatformCall spike2Indexed 1
      (spike2ExtractionInvariant spike2Row1AfterValueSetup ([] : List AnyEvent)) :=
  spike2ExtractionPhase 1 0 spike2Row1AfterValueSetup [] spike2_row1_extraction_loop_witness

/-- The generic reverse-write phase is realized by the actual one-digit Linux row-one frame. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem spike2_row1_write_phase :
    DecimalWritePhase selectedNonInputPlatformCall spike2Indexed 1
      (spike2WriteInvariant spike2Row1AfterExtraction ([] : List AnyEvent)) :=
  spike2WritePhase 1 18446744073709551615 18446744073709551615
    spike2Row1AfterExtraction [] spike2_row1_write_loop_witness

end Spikes.Spike2Fibonacci.Linux

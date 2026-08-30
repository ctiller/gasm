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

import Spikes.Spike3SortLines.VecIngestion
import Spikes.Spike3SortLines.Model

/-!
Pure composition laws for the Spike 3 line sorter.

The capacity here models only the already-decoded line store.  A concrete
target bridge still establishes the whole preparation capability, including
its sort-table grant, before selecting `.ready`.  These lemmas deliberately
make no platform-execution claim: they say exactly how a bounded ingestion
result selects the independent byte-total outcome specification.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Classify one explicit ingestion result, then perform the total, allocation-free sort and
serialization only after all lines were retained.  A first refusal has no trace payload, so it
cannot be mistaken for a complete output or an emitted prefix. -/
def lineSortOutcomeOfIngestion (ingestion : AppendLinesResult (List UInt8))
    (output : Spike3OutputOutcome) : Spike3ByteSortOutcome :=
  match ingestion with
  | .refused _ _ _ => .preparationFailure
  | .completed stored =>
    match output with
    | .accepted => .completed (byteSortOutput (sortByteLines stored))
    | .refused => .outputRefused

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Classify bounded decoded-line ingestion using the list-level semantic result. -/
def boundedLineSortOutcome (capacity : Nat) (lines : List (List UInt8))
    (output : Spike3OutputOutcome) : Spike3ByteSortOutcome :=
  lineSortOutcomeOfIngestion (appendLinesResult capacity [] lines) output

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The executable contiguous-vector storage realization selects behavior through the same
explicit ingestion result as the list-level specification. -/
def boundedVecLineSortOutcome (capacity : Nat) {size : Nat}
    (stored : Stdlib.Vec (List UInt8) size) (fits : size ≤ capacity)
    (lines : List (List UInt8)) (output : Spike3OutputOutcome) : Spike3ByteSortOutcome :=
  lineSortOutcomeOfIngestion (appendLinesVec capacity stored fits lines).toAppendLinesResult output

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The selected Vec realization refines the list-level classified sorter exactly. -/
theorem boundedVecLineSortOutcome_refines (capacity : Nat) {size : Nat}
    (stored : Stdlib.Vec (List UInt8) size) (fits : size ≤ capacity)
    (lines : List (List UInt8)) (output : Spike3OutputOutcome) :
    boundedVecLineSortOutcome capacity stored fits lines output =
      lineSortOutcomeOfIngestion (appendLinesResult capacity stored.toList lines) output := by
  unfold boundedVecLineSortOutcome
  rw [appendLinesVec_refines]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- If every decoded line fits, accepted output serializes precisely the canonical byte sort. -/
theorem boundedLineSortOutcome_of_fits_accepted (capacity : Nat) (lines : List (List UInt8))
    (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .accepted =
      .completed (byteSortOutput (sortByteLines lines)) := by
  unfold boundedLineSortOutcome
  rw [appendLinesResult_of_fits capacity [] lines]
  · rfl
  · simpa using fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The completed branch retains every input line and orders the retained lines
lexicographically before serialization.  This is the reusable content/order
invariant of the deterministic insertion sort; identities of byte-equal
lines are intentionally not observable in the byte-list model. -/
theorem boundedLineSortOutcome_of_fits_accepted_sorted_permutation
    (capacity : Nat) (lines : List (List UInt8)) (_fits : lines.length ≤ capacity) :
    (sortByteLines lines).Perm lines ∧
      List.Pairwise (fun left right : List UInt8 => left ≤ right) (sortByteLines lines) :=
  ⟨sortByteLines_perm lines, sortByteLines_pairwise_le lines⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A refusal by the selected output API remains distinct after successful bounded ingestion. -/
theorem boundedLineSortOutcome_of_fits_refused (capacity : Nat) (lines : List (List UInt8))
    (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .refused = .outputRefused := by
  unfold boundedLineSortOutcome
  rw [appendLinesResult_of_fits capacity [] lines]
  · rfl
  · simpa using fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A capacity-filling prefix forces the first following line to select the explicit
preparation-abort classification, leaving its untouched tail outside the result. -/
theorem boundedLineSortOutcome_first_refusal (capacity : Nat) (prior : List (List UInt8))
    (first : List UInt8) (tail : List (List UInt8)) (output : Spike3OutputOutcome)
    (fills : prior.length = capacity) :
    boundedLineSortOutcome capacity (prior ++ first :: tail) output = .preparationFailure := by
  unfold boundedLineSortOutcome
  rw [appendLinesResult_first_refusal capacity [] prior first tail]
  · rfl
  · simpa using fills

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The pure successful-ingestion branch agrees with the independent whole-program
specification when the caller's environment supplies these decoded input lines. -/
theorem boundedLineSortOutcome_of_fits_agrees_ready_accepted
    (environment : Environment) (capacity : Nat) (lines : List (List UInt8))
    (input : environmentInputLines environment = lines) (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .accepted =
      spike3ByteSortSpec environment .ready .accepted := by
  rw [boundedLineSortOutcome_of_fits_accepted capacity lines fits,
    spike3ByteSortSpec_ready_accepts, input]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- First refusal composes with the actual specification's exhausted branch.  In particular,
the result is neither a complete trace nor an output-refusal prefix classification. -/
theorem boundedLineSortOutcome_first_refusal_agrees_exhausted
    (environment : Environment) (capacity : Nat) (prior : List (List UInt8))
    (first : List UInt8) (tail : List (List UInt8)) (output : Spike3OutputOutcome)
    (fills : prior.length = capacity) :
    boundedLineSortOutcome capacity (prior ++ first :: tail) output =
      spike3ByteSortSpec environment .exhausted output := by
  rw [boundedLineSortOutcome_first_refusal capacity prior first tail output fills,
    spike3ByteSortSpec_exhausted]

end Spikes.Spike3SortLines

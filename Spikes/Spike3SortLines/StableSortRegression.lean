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

import Spikes.Spike3SortLines.Model

/-!
A non-vacuous executable witness for stable projected-key sorting.

The two records with byte key `[2]` have distinct origins and are separated by a record with
the smaller key `[1]`. Sorting moves the intervening record while preserving the two equal-key
records' origin order. This is stronger evidence than sorting untagged byte lines, where mutual
lexicographic precedence implies equality of the complete values.
-/

namespace Spikes.Spike3SortLines

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
structure TaggedLine where
  bytes : List UInt8
  origin : Nat
  deriving BEq, Repr

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def taggedStableSortInput : List TaggedLine :=
  [⟨[2], 0⟩, ⟨[1], 1⟩, ⟨[2], 2⟩]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def taggedStableSortOutput : List TaggedLine :=
  Stdlib.Sort.insertionSort
    (fun left right => byteLineLe left.bytes right.bytes) taggedStableSortInput

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def taggedStableSortExpected : List TaggedLine :=
  [⟨[1], 1⟩, ⟨[2], 0⟩, ⟨[2], 2⟩]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The universal stability theorem applies to distinct tagged records sharing byte keys. -/
theorem taggedStableSort_stable :
    Stdlib.Sort.StableOn TaggedLine.bytes byteLineLe
      taggedStableSortInput taggedStableSortOutput := by
  exact Stdlib.Sort.insertionSort_stableOn byteLineLe
    byteLineLawfulOrder.toLawfulTotalRelation TaggedLine.bytes taggedStableSortInput

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The concrete witness moves the smaller intervening key but retains origins `0, 2`. -/
theorem taggedStableSort_expected : taggedStableSortOutput = taggedStableSortExpected := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Runnable guard shared by every Spike 3 test executable. -/
def taggedStableSortRegressionPassed : Bool :=
  taggedStableSortOutput == taggedStableSortExpected

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
theorem taggedStableSortRegressionPassed_eq_true :
    taggedStableSortRegressionPassed = true := by
  rfl

end Spikes.Spike3SortLines

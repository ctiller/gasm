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

import Stdlib.Containers
import Spikes.Spike3SortLines.Ingestion

/-!
The thin contiguous-storage realization of Spike 3 ingestion.

`Stdlib.Vec` is the only executable line-store used here.  This module merely
adds the capacity proof and projects each execution result back to the
list-level `AppendLinesResult` specification; it does not introduce a second
container or an alternate authority for ingestion behavior.
-/

namespace Spikes.Spike3SortLines

open Stdlib

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The `Stdlib.Vec` realization retains the same completed/refused alternatives as the pure
line-store specification, with the successful prefix held in a contiguous indexed vector. -/
inductive VecAppendLinesResult (α : Type) (capacity : Nat) where
  | completed {size : Nat} (fits : size ≤ capacity) (stored : Vec α size)
  | refused {size : Nat} (fits : size ≤ capacity) (prepared : Vec α size)
      (first : α) (untouchedTail : List α)

namespace VecAppendLinesResult

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Forget only the selected representation, retaining the explicit refusal boundary. -/
def toAppendLinesResult : VecAppendLinesResult α capacity → AppendLinesResult α
  | .completed _ stored => .completed stored.toList
  | .refused _ prepared first tail => .refused prepared.toList first tail

end VecAppendLinesResult

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Execute bounded append with the selected indexed-vector store.  The recursive call is made
only after `Vec.push` and a proof that the enlarged vector still fits the caller's capacity. -/
def appendLinesVec {α : Type} (capacity : Nat) {size : Nat} (stored : Vec α size)
    (fits : size ≤ capacity) : List α → VecAppendLinesResult α capacity
  | [] => .completed fits stored
  | first :: tail =>
    if available : size < capacity then
      appendLinesVec capacity (stored.push first) (Nat.succ_le_of_lt available) tail
    else
      .refused fits stored first tail

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The vector execution realizes exactly the existing pure ingestion result.  In particular,
the vector representation cannot erase the prepared prefix, refused line, or untouched tail. -/
theorem appendLinesVec_refines {α : Type} (capacity : Nat) {size : Nat} (stored : Vec α size)
    (fits : size ≤ capacity) (lines : List α) :
    (appendLinesVec capacity stored fits lines).toAppendLinesResult =
      appendLinesResult capacity stored.toList lines := by
  induction lines generalizing size with
  | nil => simp [appendLinesVec, appendLinesResult, VecAppendLinesResult.toAppendLinesResult]
  | cons first tail ih =>
    by_cases available : size < capacity
    · simp only [appendLinesVec, dif_pos available, appendLinesResult]
      rw [show appendLine capacity stored.toList first = some (stored.toList ++ [first]) by
        simp [appendLine, available]]
      simpa using ih (stored := stored.push first) (Nat.succ_le_of_lt available)
    · simp [appendLinesVec, available, appendLinesResult, appendLine,
        VecAppendLinesResult.toAppendLinesResult]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- `ByteArray.toVec` is the lossless byte-storage boundary used when a concrete target supplies
a decoded line as a `ByteArray`; its vector observation is the same contiguous byte storage. -/
theorem byteArray_toVec_observes_storage (bytes : ByteArray) :
    bytes.toVec.toList = bytes.data.toList := by
  exact Stdlib.Vec.toList_toVec bytes

end Spikes.Spike3SortLines

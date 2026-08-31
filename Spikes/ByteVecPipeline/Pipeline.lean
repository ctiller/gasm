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

import Stdlib.Containers.ByteVec

/-! A target-neutral consumer of the public ByteVec/Vec boundary.

This source-level demonstration carries no target, emitted-storage, or `VerifiedProgram` authority.
-/

namespace Spikes.ByteVecPipeline

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The observable result of joining two byte sequences through the indexed-vector API. -/
structure Result where
  bytes : ByteArray
  boundary : Option UInt8
  deriving BEq

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Convert both inputs to indexed vectors, append them, observe the right boundary safely,
and return to specialized byte storage. -/
def run (leftBytes rightBytes : ByteArray) : Result :=
  let combined := leftBytes.toVec.append rightBytes.toVec
  { bytes := combined.toByteArray
    boundary := combined.get? leftBytes.size }

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Bounds-safe observation of any position in the same Vec-backed pipeline. -/
def observe? (leftBytes rightBytes : ByteArray) (index : Nat) : Option UInt8 :=
  (leftBytes.toVec.append rightBytes.toVec).get? index

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The Vec-backed pipeline returns exactly ordinary ByteArray append for all inputs. -/
@[simp] theorem run_bytes (leftBytes rightBytes : ByteArray) :
    (run leftBytes rightBytes).bytes = leftBytes ++ rightBytes := by
  simp [run]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Every valid left index observes the corresponding prefix byte. -/
theorem observe?_left (leftBytes rightBytes : ByteArray) (index : Fin leftBytes.size) :
    observe? leftBytes rightBytes index.val = some (leftBytes[index.val]'index.isLt) := by
  unfold observe?
  rw [Stdlib.Vec.get?_append_left _ _ index.isLt, ByteArray.toVec_get?]
  exact getElem?_pos leftBytes index.val index.isLt

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Every valid right index observes the corresponding payload byte after the boundary. -/
theorem observe?_right (leftBytes rightBytes : ByteArray) (index : Fin rightBytes.size) :
    observe? leftBytes rightBytes (leftBytes.size + index.val) =
      some (rightBytes[index.val]'index.isLt) := by
  unfold observe?
  rw [Stdlib.Vec.get?_append_right _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [ByteArray.toVec_get?]
  exact getElem?_pos rightBytes index.val index.isLt

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The boundary observation is exactly the optional first payload byte. -/
@[simp] theorem run_boundary (leftBytes rightBytes : ByteArray) :
    (run leftBytes rightBytes).boundary = rightBytes[0]? := by
  change (leftBytes.toVec.append rightBytes.toVec).get? leftBytes.size = rightBytes[0]?
  rw [Stdlib.Vec.get?_append_right _ _ (Nat.le_refl leftBytes.size)]
  simpa using ByteArray.toVec_get? rightBytes 0

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Observations at or beyond the combined length fail explicitly. -/
theorem observe?_out_of_bounds (leftBytes rightBytes : ByteArray) {index : Nat}
    (outOfBounds : leftBytes.size + rightBytes.size ≤ index) :
    observe? leftBytes rightBytes index = none := by
  exact Stdlib.Vec.get?_eq_none_of_le _ outOfBounds

end Spikes.ByteVecPipeline

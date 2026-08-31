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

/-! Runnable composition test for the representation-free Vec contract, its Array realization,
and the specialized ByteArray bridge. This is library evidence, not an end-to-end program proof. -/

namespace Stdlib.Vec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def regressionLeft : ByteArray := ByteArray.mk #[10, 20]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def regressionRight : ByteArray := ByteArray.mk #[30, 40]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def regressionAppended : Vec UInt8 4 := regressionLeft.toVec.append regressionRight.toVec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def regressionTransformed : Vec UInt8 5 :=
  (((regressionAppended.set ⟨1, by omega⟩ 21).swap
    ⟨0, by omega⟩ ⟨3, by omega⟩).push 50)

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The concrete append is observed through the representation-independent append model. -/
theorem regressionAppended_refines :
    regressionAppended.toModel =
      VecSpec.append regressionLeft.toVec.toModel regressionRight.toVec.toModel := by
  unfold regressionAppended
  exact toModel_append regressionLeft.toVec regressionRight.toVec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The composed concrete update pipeline refines the same composition of semantic operations. -/
theorem regressionTransformed_refines :
    regressionTransformed.toModel =
      VecSpec.push
        (VecSpec.swap
          (VecSpec.set regressionAppended.toModel ⟨1, by omega⟩ 21)
          ⟨0, by omega⟩ ⟨3, by omega⟩)
        50 := by
  simp [regressionTransformed]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The executable witness checks both sides of the append boundary, explicit out-of-bounds
failure, exact ByteArray append agreement, and the composed update result. -/
def regressionPassed : Bool :=
  regressionAppended.toByteArray == regressionLeft ++ regressionRight &&
  regressionAppended.get? 1 == some 20 &&
  regressionAppended.get? 2 == some 30 &&
  regressionAppended.get? 4 == none &&
  regressionTransformed.toList == [40, 21, 30, 10, 50]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem regressionPassed_eq_true : regressionPassed = true := by
  rfl

end Stdlib.Vec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def main : IO UInt32 := do
  if Stdlib.Vec.regressionPassed then
    IO.println "[PASS] Vec semantics, Array realization, and ByteVec bridge"
    return 0
  else
    IO.eprintln "[FAIL] Vec semantics, Array realization, or ByteVec bridge"
    return 1

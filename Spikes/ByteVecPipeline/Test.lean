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

import Spikes.ByteVecPipeline.Pipeline

/-! Runnable edge-case demonstration for the target-neutral ByteVec pipeline. -/

namespace Spikes.ByteVecPipeline

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def regressionPassed : Bool :=
  run ByteArray.empty (ByteArray.mk #[7, 8]) ==
      { bytes := ByteArray.mk #[7, 8], boundary := some 7 } &&
  run (ByteArray.mk #[1, 2]) ByteArray.empty ==
      { bytes := ByteArray.mk #[1, 2], boundary := none } &&
  run (ByteArray.mk #[1, 2]) (ByteArray.mk #[3, 4]) ==
      { bytes := ByteArray.mk #[1, 2, 3, 4], boundary := some 3 } &&
  observe? (ByteArray.mk #[1, 2]) (ByteArray.mk #[3, 4]) 1 == some 2 &&
  observe? (ByteArray.mk #[1, 2]) (ByteArray.mk #[3, 4]) 2 == some 3 &&
  observe? (ByteArray.mk #[1, 2]) (ByteArray.mk #[3, 4]) 4 == none

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem regressionPassed_eq_true : regressionPassed = true := by
  rfl

end Spikes.ByteVecPipeline

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def main : IO UInt32 := do
  if Spikes.ByteVecPipeline.regressionPassed then
    IO.println "[PASS] standalone ByteVec append and boundary pipeline"
    return 0
  else
    IO.eprintln "[FAIL] standalone ByteVec append or boundary pipeline"
    return 1

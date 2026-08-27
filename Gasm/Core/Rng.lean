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

import Lean

namespace Gasm.Core

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Simple pseudo-random number generator state (Xorshift64). -/
structure FuzzerRng where
  seed : UInt64 := 88172645463325252
  deriving Repr, DecidableEq, Inhabited

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates the next pseudo-random UInt64 and advanced RNG state. -/
def FuzzerRng.next (rng : FuzzerRng) : Prod UInt64 FuzzerRng :=
  let x := rng.seed
  let x1 := x ^^^ (x <<< 13)
  let x2 := x1 ^^^ (x1 >>> 7)
  let x3 := x2 ^^^ (x2 <<< 17)
  let finalSeed := if x3 == 0 then 88172645463325252 else x3
  (finalSeed, { seed := finalSeed })

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Selects a random natural number in range [0, bound - 1]. -/
def FuzzerRng.nextNat (bound : Nat) (rng : FuzzerRng) : Prod Nat FuzzerRng :=
  if bound <= 1 then (0, rng)
  else
    let (v, nextRng) := rng.next
    ((v.toNat % bound), nextRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates a random UInt32. -/
def FuzzerRng.nextUInt32 (rng : FuzzerRng) : Prod UInt32 FuzzerRng :=
  let (v, nextRng) := rng.next
  (v.toUInt32, nextRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates a random UInt8. -/
def FuzzerRng.nextUInt8 (rng : FuzzerRng) : Prod UInt8 FuzzerRng :=
  let (v, nextRng) := rng.next
  (v.toUInt8, nextRng)

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- Generates a random boolean flag. -/
def FuzzerRng.nextBool (rng : FuzzerRng) : Prod Bool FuzzerRng :=
  let (v, nextRng) := rng.next
  ((v &&& 1) != 0, nextRng)

end Gasm.Core

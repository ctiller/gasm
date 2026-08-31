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

/-!
Import-light observation laws for Lean's specialized `ByteArray` representation.

Lean core states the corresponding push laws for `[i]!`, while codec algorithms use the
separately implemented `.get!`. These lemmas connect the two observation surfaces without
assigning any PNG, Zlib, effect, target, or program authority.
-/

/- REF: docs/STDLIB_CONTAINERS.md#4-bytearray-observation-bridge -/
/-- `.get!` agrees with the `[i]!` notation for every in-bounds index. -/
theorem ByteArray.get!_eq_getElem_bang (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.get! i = data[i]! := by
  rw [getElem!_pos data i h]
  simp only [ByteArray.get!]
  rw [getElem!_pos data.data i h]
  rfl

/- REF: docs/STDLIB_CONTAINERS.md#4-bytearray-observation-bridge -/
/-- `.get!` agrees with proof-carrying `getElem` for every in-bounds index. -/
theorem ByteArray.get!_eq_getElem (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.get! i = data[i]'h := by
  rw [ByteArray.get!_eq_getElem_bang data i h, getElem!_pos data i h]

/- REF: docs/STDLIB_CONTAINERS.md#4-bytearray-observation-bridge -/
/-- Pushing one byte preserves every earlier `.get!` observation. -/
theorem ByteArray.get!_push_lt (data : ByteArray) (b : UInt8) (i : Nat) (hi : i < data.size) :
    (data.push b).get! i = data.get! i := by
  have hi' : i < (data.push b).size := by rw [ByteArray.size_push]; omega
  rw [ByteArray.get!_eq_getElem_bang (data.push b) i hi',
    ByteArray.get!_eq_getElem_bang data i hi, ByteArray.getElem!_push_lt data b i hi]

/- REF: docs/STDLIB_CONTAINERS.md#4-bytearray-observation-bridge -/
/-- Pushing one byte makes it the `.get!` observation at the old size. -/
theorem ByteArray.get!_push_eq (data : ByteArray) (b : UInt8) (i : Nat)
    (hi : i = data.size) : (data.push b).get! i = b := by
  subst hi
  have h : data.size < (data.push b).size := by rw [ByteArray.size_push]; omega
  rw [ByteArray.get!_eq_getElem_bang (data.push b) data.size h,
    ByteArray.getElem!_push_eq data b]

/- REF: docs/STDLIB_CONTAINERS.md#4-bytearray-observation-bridge -/
/-- Same-size byte arrays are equal when all their in-bounds `.get!` observations agree. -/
theorem ByteArray.ext_get! {a b : ByteArray} (hsize : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← ByteArray.get!_eq_getElem a i hi, ← ByteArray.get!_eq_getElem b i hi']
  exact h i hi

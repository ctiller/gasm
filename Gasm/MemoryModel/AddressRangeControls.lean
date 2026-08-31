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

import Gasm.MemoryModel.AddressRange

/-! Private positive and malformed-range controls for the target-neutral range algebra. -/

namespace Gasm.MemoryModel.AddressRangeControls

open Gasm.MemoryModel.AddressRange

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private def outer : AddressRange := ⟨0x1000, 16⟩

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private def middle : AddressRange := ⟨0x1004, 8⟩

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private def inner : AddressRange := ⟨0x1006, 2⟩

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem positive_wellFormed : outer.WellFormed := by
  refine ⟨?_, ?_⟩
  · change 0 < 16
    omega
  · change 0x1000 + 16 ≤ 2 ^ 64
    decide

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem positive_nested : outer.Contains middle ∧ middle.Contains inner := by
  simp [outer, middle, inner, Contains, endExclusive]

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem nested_transitive : outer.Contains inner := by
  exact contains_trans positive_nested.1 positive_nested.2

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem zero_length_rejected : ¬ (⟨0x1000, 0⟩ : AddressRange).WellFormed := by
  intro wellFormed
  exact (Nat.lt_irrefl 0 wellFormed.nonempty)

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem wrapping_range_rejected :
    ¬ (⟨0xFFFFFFFFFFFFFFFF, 2⟩ : AddressRange).WellFormed := by
  intro wellFormed
  have noWrap := wellFormed.noWrap
  change 18446744073709551615 + 2 ≤ 2 ^ 64 at noWrap
  omega

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem oversized_inner_rejected :
    ¬ outer.Contains ⟨0x1004, 16⟩ := by
  intro contained
  simp only [outer, Contains, endExclusive] at contained
  have outerNat : (0x1000 : UInt64).toNat = 0x1000 := by decide
  have innerNat : (0x1004 : UInt64).toNat = 0x1004 := by decide
  rw [outerNat, innerNat] at contained
  omega

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
private theorem endpoint_rejected : ¬ outer.ContainsAddress 0x1010 := by
  intro member
  simp only [outer, ContainsAddress, endExclusive] at member
  have outerNat : (0x1000 : UInt64).toNat = 0x1000 := by decide
  have endpointNat : (0x1010 : UInt64).toNat = 0x1010 := by decide
  rw [outerNat, endpointNat] at member
  omega

end Gasm.MemoryModel.AddressRangeControls

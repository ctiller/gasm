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

import Gasm.Core.Types

/-!
Target-neutral byte ranges for memory events, views, grants, and instruction descriptors.

`AddressRange` is deliberately only data. `WellFormed` separately proves that a selected access is
nonempty and does not wrap the 64-bit address space. Containment is arithmetic over mathematical
endpoints, never modulo arithmetic.

This module proves no provenance, liveness, mapping, permissions, target attributes, or execution
authority. Those remain separate selected-profile obligations.
-/

namespace Gasm.MemoryModel

open Gasm.Core

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A half-open byte range `[start, start + length)` in the 64-bit virtual address space. -/
structure AddressRange where
  start : Address
  length : Nat
  deriving DecidableEq, Repr

namespace AddressRange

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Mathematical exclusive endpoint. It is intentionally a `Nat`, so wrapping cannot be hidden. -/
def endExclusive (range : AddressRange) : Nat :=
  range.start.toNat + range.length

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Byte enumeration in increasing address order. It denotes a physical range only with a
    `WellFormed` certificate; without one, `UInt64` addition remains modular. -/
def addresses (range : AddressRange) : List Address :=
  (List.range range.length).map (fun offset => range.start + offset.toUInt64)

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- A selected access range is nonempty and has a mathematical endpoint within `2^64`. -/
structure WellFormed (range : AddressRange) : Prop where
  nonempty : 0 < range.length
  noWrap : range.endExclusive ≤ 2 ^ 64

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- Half-open containment using mathematical, non-modular endpoints. -/
def Contains (outer inner : AddressRange) : Prop :=
  outer.start.toNat ≤ inner.start.toNat ∧ inner.endExclusive ≤ outer.endExclusive

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- Address membership in a mathematical half-open range. -/
def ContainsAddress (range : AddressRange) (address : Address) : Prop :=
  range.start.toNat ≤ address.toNat ∧ address.toNat < range.endExclusive

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
theorem contains_refl (range : AddressRange) : range.Contains range := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
theorem contains_trans {outer middle inner : AddressRange}
    (outerMiddle : outer.Contains middle) (middleInner : middle.Contains inner) :
    outer.Contains inner := by
  exact ⟨Nat.le_trans outerMiddle.1 middleInner.1,
    Nat.le_trans middleInner.2 outerMiddle.2⟩

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- Containment in a non-wrapping outer range transfers non-wrapping to a nonempty inner range. -/
theorem wellFormed_of_contains {outer inner : AddressRange}
    (outerWellFormed : outer.WellFormed) (contained : outer.Contains inner)
    (innerNonempty : 0 < inner.length) : inner.WellFormed := by
  exact ⟨innerNonempty, Nat.le_trans contained.2 outerWellFormed.noWrap⟩

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- Mutual containment identifies the exact start and length, not merely the same address set. -/
theorem eq_of_contains_each_other {left right : AddressRange}
    (leftRight : left.Contains right) (rightLeft : right.Contains left) : left = right := by
  cases left with
  | mk leftStart leftLength =>
      cases right with
      | mk rightStart rightLength =>
          simp only [Contains, endExclusive] at leftRight rightLeft
          have startNat : leftStart.toNat = rightStart.toNat :=
            Nat.le_antisymm leftRight.1 rightLeft.1
          have start : leftStart = rightStart := UInt64.toNat_inj.mp startNat
          subst start
          have length : leftLength = rightLength := by omega
          subst length
          rfl

/- REF: docs/MEMORY_MODEL.md#61-regions-and-provenanced-pointers -/
/-- Membership is monotone under range containment. -/
theorem containsAddress_of_contains {outer inner : AddressRange} {address : Address}
    (contained : outer.Contains inner) (member : inner.ContainsAddress address) :
    outer.ContainsAddress address := by
  exact ⟨Nat.le_trans contained.1 member.1, Nat.lt_of_lt_of_le member.2 contained.2⟩

end AddressRange

end Gasm.MemoryModel

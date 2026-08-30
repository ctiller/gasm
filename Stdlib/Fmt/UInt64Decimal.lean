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

import Stdlib.Fmt.Basic

/-!
# Bounded UInt64 decimal formatting contract

This is the callable, platform-independent contract for formatting a `UInt64` into a finite
buffer.  It deliberately models finite capacity and its failure result; the extraction/reverse
schedule and every target ABI/assembly realization live in separate layers.
-/

namespace Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Decimal digit count for a machine unsigned 64-bit value.  Zero is explicitly one digit. -/
def decimalDigitCount (value : UInt64) : Nat :=
  if value = 0 then 1 else (digits value.toNat).length

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- The machine-width count agrees with the canonical codec's digit count, including zero. -/
theorem decimalDigitCount_eq_digits_length (value : UInt64) :
    decimalDigitCount value = (digits value.toNat).length := by
  unfold decimalDigitCount
  split
  · subst value
    change 1 = (digits 0).length
    rw [digits_single 0 (by omega)]
    rfl
  · rfl

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem decimalDigitCount_pos (value : UInt64) : 1 ≤ decimalDigitCount value := by
  rw [decimalDigitCount_eq_digits_length]
  have h := digits_ne_nil value.toNat
  cases hd : digits value.toNat with
  | nil => exact False.elim (h hd)
  | cons _ _ => simp

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem decimalDigitCount_le_twenty (value : UInt64) : decimalDigitCount value ≤ 20 := by
  rw [decimalDigitCount_eq_digits_length]
  exact digits_length_le_UInt64 value

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Finite-capacity result of the platform-neutral formatter.  Capacity exhaustion is a normal,
    explicit result and never silently truncates a decimal value. -/
inductive DecimalWriteResult where
  | written (bytes : List UInt8) (required : Nat)
  | insufficientCapacity (required available : Nat)
  deriving DecidableEq, Repr

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Writes only when the complete decimal representation fits the supplied frame capacity. -/
def writeUInt64Decimal (capacity : Nat) (value : UInt64) : DecimalWriteResult :=
  let required := decimalDigitCount value
  if required ≤ capacity then
    .written (formatDecimal value.toNat) required
  else
    .insufficientCapacity required capacity

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem writeUInt64Decimal_fits (capacity : Nat) (value : UInt64)
    (hfit : decimalDigitCount value ≤ capacity) :
    writeUInt64Decimal capacity value =
      .written (formatDecimal value.toNat) (decimalDigitCount value) := by
  unfold writeUInt64Decimal
  rw [if_pos hfit]

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem writeUInt64Decimal_exhausted (capacity : Nat) (value : UInt64)
    (hfit : ¬ decimalDigitCount value ≤ capacity) :
    writeUInt64Decimal capacity value =
      .insufficientCapacity (decimalDigitCount value) capacity := by
  unfold writeUInt64Decimal
  rw [if_neg hfit]

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Callable result/capacity contract consumed by target realizations.  It intentionally says
    nothing about implementation steps, scratch locations, registers, or stack layout. -/
structure UInt64DecimalContract (capacity : Nat) (value : UInt64) where
  result : DecimalWriteResult
  required : Nat
  required_eq : required = decimalDigitCount value
  result_eq : result = writeUInt64Decimal capacity value
  success : result = .written (formatDecimal value.toNat) required ↔ required ≤ capacity
  exhausted : result = .insufficientCapacity required capacity ↔ ¬ required ≤ capacity

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
def uint64DecimalContract (capacity : Nat) (value : UInt64) : UInt64DecimalContract capacity value where
  result := writeUInt64Decimal capacity value
  required := decimalDigitCount value
  required_eq := rfl
  result_eq := rfl
  success := by
    constructor
    · intro h
      by_cases hfit : decimalDigitCount value ≤ capacity
      · exact hfit
      · rw [writeUInt64Decimal_exhausted capacity value hfit] at h
        cases h
    · intro hfit
      exact writeUInt64Decimal_fits capacity value hfit
  exhausted := by
    constructor
    · intro h
      by_cases hfit : decimalDigitCount value ≤ capacity
      · rw [writeUInt64Decimal_fits capacity value hfit] at h
        cases h
      · exact hfit
    · intro hfit
      exact writeUInt64Decimal_exhausted capacity value hfit

end Stdlib.Fmt

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

import Stdlib.Fmt.UInt64Decimal

/-!
# UInt64 decimal extraction/reverse schedule

This optional implementation certificate refines the callable decimal contract with a portable
division/modulo extraction schedule.  Its work counts are schedule facts, not a production native
fuel budget: a target realization proves its own instruction/resource accounting separately.
-/

namespace Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Division/modulo extraction schedule, producing least-significant digits first. -/
def extractDecimalReversed (value : Nat) : List Nat :=
  if h : value < 10 then
    [value]
  else
    value % 10 :: extractDecimalReversed (value / 10)
termination_by value
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem extractDecimalReversed_eq (value : Nat) :
    extractDecimalReversed value = (digits value).reverse := by
  induction value using Nat.strongRecOn with
  | _ value ih =>
    unfold extractDecimalReversed digits
    split
    · rename_i h
      simp
    · rename_i h
      rw [ih (value / 10) (Nat.div_lt_self (by omega) (by omega))]
      simp

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Reverse-write phase for a previously extracted digit stack. -/
def reverseWriteDecimal (extracted : List Nat) : List UInt8 :=
  extracted.reverse.map byteOfDigit

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem reverseWriteDecimal_extract (value : Nat) :
    reverseWriteDecimal (extractDecimalReversed value) = formatDecimal value := by
  unfold reverseWriteDecimal formatDecimal
  rw [extractDecimalReversed_eq]
  simp

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Abstract scratch resources clobbered by this schedule, deliberately not physical ABI slots. -/
inductive DecimalScratch where
  | quotient | remainder | digitStack | writeCursor
  deriving DecidableEq, Repr

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
def decimalClobbers : List DecimalScratch :=
  [.quotient, .remainder, .digitStack, .writeCursor]

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
def decimalExtractionIterations (value : UInt64) : Nat :=
  (extractDecimalReversed value.toNat).length

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
def decimalReverseWriteIterations (value : UInt64) : Nat :=
  (extractDecimalReversed value.toNat).length

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem decimalExtractionIterations_eq_digitCount (value : UInt64) :
    decimalExtractionIterations value = decimalDigitCount value := by
  unfold decimalExtractionIterations
  rw [extractDecimalReversed_eq, List.length_reverse,
    ← decimalDigitCount_eq_digits_length]

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
theorem decimalReverseWriteIterations_eq_digitCount (value : UInt64) :
    decimalReverseWriteIterations value = decimalDigitCount value :=
  decimalExtractionIterations_eq_digitCount value

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Reusable schedule certificate layered over the result/capacity callable contract. -/
structure UInt64DecimalScheduleCertificate (capacity : Nat) (value : UInt64) where
  callable : UInt64DecimalContract capacity value
  extractionIterations : Nat
  reverseWriteIterations : Nat
  scheduleFuel : Nat
  clobbers : List DecimalScratch
  extractionIterations_eq : extractionIterations = decimalDigitCount value
  reverseWriteIterations_eq : reverseWriteIterations = decimalDigitCount value
  scheduleFuel_eq : scheduleFuel = 3 + extractionIterations + reverseWriteIterations
  clobbers_eq : clobbers = decimalClobbers
  implementation_eq : reverseWriteDecimal (extractDecimalReversed value.toNat) = formatDecimal value.toNat

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
def uint64DecimalScheduleCertificate (capacity : Nat) (value : UInt64) :
    UInt64DecimalScheduleCertificate capacity value where
  callable := uint64DecimalContract capacity value
  extractionIterations := decimalExtractionIterations value
  reverseWriteIterations := decimalReverseWriteIterations value
  scheduleFuel := 3 + decimalExtractionIterations value + decimalReverseWriteIterations value
  clobbers := decimalClobbers
  extractionIterations_eq := decimalExtractionIterations_eq_digitCount value
  reverseWriteIterations_eq := decimalReverseWriteIterations_eq_digitCount value
  scheduleFuel_eq := rfl
  clobbers_eq := rfl
  implementation_eq := reverseWriteDecimal_extract value.toNat

end Stdlib.Fmt

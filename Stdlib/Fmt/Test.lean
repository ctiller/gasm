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
import Stdlib.Fmt.Basic
import Stdlib.Fmt.UInt64Decimal
import Stdlib.Fmt.Parser
import Stdlib.Fmt.Roundtrip

/-
## Stdlib.Fmt.Test

Concrete regression vectors: `digits`/`formatDecimal` on witness values (`0`, single-digit,
two-digit, and `UInt64.size - 1` -- the largest value a machine register can hold), plus one
vector per `Error` rejection reason (`docs/STDLIB_FMT.md#31-error-taxonomy`).
`parseDecimal_formatDecimal`/`parseDecimal_reencode_stable` in `Roundtrip.lean` already prove the
parser inverts the formatter for *every* `Nat` -- what these `#guard`s cover instead is concrete
witness behavior (easy to misread from the proofs alone) and the parser's *rejection* behavior on
adversarial byte strings, which a universally-quantified round-trip theorem does not by itself
exercise.
-/

namespace Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- Converts an ASCII test string to the raw wire bytes `parseDecimal` consumes. -/
def s2b (s : String) : List UInt8 := s.toUTF8.toList

-- === `digits`/`formatDecimal` on witness values ===

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
#guard digits 0 = [0]

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
#guard digits 7 = [7]

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
#guard digits 42 = [4, 2]

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
#guard digits 1234567890 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
#guard formatDecimal 0 = s2b "0"

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
#guard formatDecimal 90 = s2b "90"

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
/- `UInt64.size - 1` (`18446744073709551615`) is the largest value a 64-bit register can hold;
   its decimal representation is 20 digits, matching `digits_length_le_UInt64`'s bound exactly. -/
#guard formatDecimal 18446744073709551615 = s2b "18446744073709551615"

#guard (digits 18446744073709551615).length = 20

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
#guard decimalDigitCount 0 = 1

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
#guard writeUInt64Decimal 1 7 = .written (s2b "7") 1

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
#guard writeUInt64Decimal 1 42 = .insufficientCapacity 2 1

-- === Well-formed input: must parse successfully ===

/- REF: docs/STDLIB_FMT.md#52-write-then-parse-roundtrip-theorem -/
#guard match parseDecimal (s2b "0") with | .ok n => n == 0 | .error _ => false

/- REF: docs/STDLIB_FMT.md#52-write-then-parse-roundtrip-theorem -/
#guard match parseDecimal (s2b "90") with | .ok n => n == 90 | .error _ => false

/- REF: docs/STDLIB_FMT.md#52-write-then-parse-roundtrip-theorem -/
#guard match parseDecimal (s2b "18446744073709551615") with
  | .ok n => n == 18446744073709551615
  | .error _ => false

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
/- A leading zero is not rejected: `parseDecimal` decodes the numeric value denoted by any
   digit run, canonical or not -- `formatDecimal` alone is responsible for never producing one
   (`docs/STDLIB_FMT.md#2-digit-grammar`). -/
#guard match parseDecimal (s2b "007") with | .ok n => n == 7 | .error _ => false

-- === Malformed input: one vector per `Error` rejection reason ===

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
#guard match parseDecimal [] with | .error .empty => true | _ => false

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
#guard match parseDecimal (s2b "12a4") with | .error .invalidDigit => true | _ => false

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
#guard match parseDecimal (s2b "-5") with | .error .invalidDigit => true | _ => false

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
#guard match parseDecimal (s2b " 5") with | .error .invalidDigit => true | _ => false

end Stdlib.Fmt

open Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#3-decoder-parser-behavior -/
/-- Every regression vector above is a `#guard`, checked at compile time (kernel-evaluated, not
    `native_decide`) -- if this executable built, every vector already passed. -/
def main : IO UInt32 := do
  IO.println "======================================================================"
  IO.println " Stdlib.Fmt Test Suite (total decimal digit formatter/parser)"
  IO.println "======================================================================"
  IO.println "[+] All #guard regression vectors passed at build time (19 checks: 8"
  IO.println "    digits/formatDecimal witnesses, 3 bounded-UInt64 capacity cases, 4"
  IO.println "    well-formed parses, 4 Error-taxonomy rejections)."
  IO.println "\n[+] ALL STDLIB.FMT TESTS PASSED (100% SUCCESS)."
  return 0

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

/-
## Stdlib.Fmt.Parser

`parseDecimal : List UInt8 → Except Error Nat` -- total (structural recursion on the input list,
no `partial def`), the honest counterpart to `Basic.lean`'s `formatDecimal`: an arbitrary byte
string either fails with a named `Error`, or decodes to the `Nat` it denotes. Matches the shape
`docs/STDLIB_FMT.md#3-decoder-parser-behavior` documents and that `Roundtrip.lean`'s
`parseDecimal_reencode_stable` (`docs/STDLIB_FMT.md#53-parse-reencode-stability-theorem`) needs:
"take an arbitrary bytestream; if it fails, fail; if it parses, re-encode and parse; assert the
first parse matches the second."
-/

namespace Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
/-- The only two ways `parseDecimal` rejects an input: an empty byte string, or a byte string
    containing a non-digit byte anywhere. -/
inductive Error
  | empty
  | invalidDigit
  deriving DecidableEq, Repr

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- `digitOfByte?` recovers exactly the digit `byteOfDigit` wrote, for every genuine digit value
    `d < 10`. -/
theorem digitOfByte?_byteOfDigit (d : Nat) (h : d < 10) :
    digitOfByte? (byteOfDigit d) = some d := by
  have h10 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  unfold digitOfByte? byteOfDigit
  rcases h10 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
/-- Left-fold accumulator for `parseDecimal`. Structurally recursive on `bs`. -/
def parseDecimalAux : List UInt8 → Nat → Except Error Nat
  | [], acc => .ok acc
  | b :: rest, acc =>
      match digitOfByte? b with
      | some d => parseDecimalAux rest (acc * 10 + d)
      | none => .error .invalidDigit

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
/-- Decodes a non-empty run of ASCII decimal digit bytes into the `Nat` it denotes; `.error
    .empty` on an empty input (an empty field is a parse error, not a silent zero), `.error
    .invalidDigit` on any non-digit byte anywhere in the run. Total: every input, well-formed or
    adversarial, reaches a result in finitely many (`bs.length`) steps. -/
def parseDecimal (bs : List UInt8) : Except Error Nat :=
  if bs.isEmpty then .error .empty else parseDecimalAux bs 0

/- REF: docs/STDLIB_FMT.md#31-error-taxonomy -/
/-- `parseDecimalAux` distributes over `List.append`: parsing `l ++ [x]` with accumulator `a` is
    parsing `l` with `a`, then folding the resulting accumulator against the one extra digit
    byte `x` -- the generic append lemma `digits_foldl_eq`'s parser-side counterpart needs to
    push `parseDecimalAux` through `digits n`'s own `digits (n / 10) ++ [n % 10]` recursion.
    Proved by structural induction on `l`. -/
theorem parseDecimalAux_append (l : List UInt8) (x : UInt8) (a : Nat) :
    parseDecimalAux (l ++ [x]) a =
      match parseDecimalAux l a with
      | .ok v => (match digitOfByte? x with
          | some d => .ok (v * 10 + d)
          | none => .error .invalidDigit)
      | .error e => .error e := by
  induction l generalizing a with
  | nil => simp [parseDecimalAux]
  | cons b t iht =>
    simp only [List.cons_append, parseDecimalAux]
    cases digitOfByte? b with
    | none => simp
    | some d => exact iht (a * 10 + d)

end Stdlib.Fmt

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

import Stdlib.Fmt.Parser

/-
## Stdlib.Fmt.Roundtrip

The two round-trip theorems, per `docs/STDLIB_FMT.md#5-formal-theorems`:

1. `parseDecimal_formatDecimal` (`docs/STDLIB_FMT.md#52-write-then-parse-roundtrip-theorem`):
   `∀ n, parseDecimal (formatDecimal n) = .ok n` -- universally quantified over *every* `Nat`,
   forbidding an always-failing parser.
2. `parseDecimal_reencode_stable` (`docs/STDLIB_FMT.md#53-parse-reencode-stability-theorem`):
   `∀ b n₁ n₂, parseDecimal b = .ok n₁ → parseDecimal (formatDecimal n₁) = .ok n₂ → n₁ = n₂` --
   ranging over *every* byte string (including adversarial ones), forbidding a lossy parser.
   This is a direct corollary of (1) plus `parseDecimal`'s own determinism (a plain function of
   its input): instantiating (1) at `n₁` gives `parseDecimal (formatDecimal n₁) = .ok n₁`
   unconditionally, which the second hypothesis then forces to equal `.ok n₂` by injectivity of
   `Except.ok`. (1) is this theorem's non-vacuity floor -- on its own, (2) would be satisfiable
   by a parser that always returns `.error` (its first hypothesis would simply never fire), but
   (1) independently forbids that. Exactly the shape `Stdlib.Http11.request_roundtrip` /
   `request_parse_reencode_stable` (`Stdlib/Http11/Roundtrip.lean`) already established for this
   library's HTTP counterpart.
-/

namespace Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#52-write-then-parse-roundtrip-theorem -/
/-- Auxiliary accumulator form of the round-trip lemma: parsing `formatDecimal n` with an
    arbitrary starting accumulator `acc` reproduces `acc * 10 ^ (digit count) + n`. Proved by
    strong induction on `n`, mirroring `digits`' own recursion -- the same shape
    `Stdlib.Http11.Basic.digitBytesToNatAux_natToDigitBytes` uses for the narrower
    `Content-Length` codec. -/
theorem parseDecimalAux_formatDecimal (n : Nat) :
    ∀ acc, parseDecimalAux (formatDecimal n) acc =
      .ok (acc * 10 ^ (formatDecimal n).length + n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    unfold formatDecimal digits
    split
    · rename_i h
      simp only [List.map_cons, List.map_nil, parseDecimalAux]
      rw [digitOfByte?_byteOfDigit n h]
      simp [Nat.pow_one]
    · rename_i h
      have hshape : (digits (n / 10) ++ [n % 10]).map byteOfDigit
          = formatDecimal (n / 10) ++ [byteOfDigit (n % 10)] := by
        rw [List.map_append]; rfl
      rw [hshape, parseDecimalAux_append]
      rw [ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) acc]
      rw [digitOfByte?_byteOfDigit (n % 10) (Nat.mod_lt n (by omega))]
      have hlen : (formatDecimal (n / 10) ++ [byteOfDigit (n % 10)]).length
          = (formatDecimal (n / 10)).length + 1 := by simp
      rw [hlen]
      have step : (acc * 10 ^ (formatDecimal (n / 10)).length + n / 10) * 10 + n % 10
          = acc * 10 ^ ((formatDecimal (n / 10)).length + 1) + n := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        generalize acc * 10 ^ (formatDecimal (n / 10)).length = k
        omega
      simpa using step

/- REF: docs/STDLIB_FMT.md#52-write-then-parse-roundtrip-theorem -/
/-- **Write-then-parse round trip.** Universally quantified over every `Nat` -- not a
    `native_decide` check over sample literals. Forbids an always-failing parser:
    `formatDecimal n` must parse back to exactly `n`, for every `n`. -/
theorem parseDecimal_formatDecimal (n : Nat) : parseDecimal (formatDecimal n) = .ok n := by
  have hne : ¬ (formatDecimal n).isEmpty := by
    have := formatDecimal_ne_nil n
    simpa using this
  unfold parseDecimal
  simp only [hne]
  have := parseDecimalAux_formatDecimal n 0
  simpa using this

/- REF: docs/STDLIB_FMT.md#53-parse-reencode-stability-theorem -/
/-- **Parse-reencode stability.** Ranges over *every* byte string `b` (including
    malformed/adversarial ones), not just ones `formatDecimal` produces. A direct corollary of
    `parseDecimal_formatDecimal` plus `parseDecimal`'s determinism. -/
theorem parseDecimal_reencode_stable (b : List UInt8) (n1 n2 : Nat)
    (_h1 : parseDecimal b = .ok n1) (h2 : parseDecimal (formatDecimal n1) = .ok n2) :
    n1 = n2 := by
  rw [parseDecimal_formatDecimal n1] at h2
  exact Except.ok.inj h2

end Stdlib.Fmt

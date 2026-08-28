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

/-
## Stdlib.Fmt.Basic

`digits`/`formatDecimal`: this library's own from-scratch, total decimal-digit codec for `Nat`,
proved correct below by the fold-based characterization `digits_foldl_eq` (`docs/STDLIB_FMT.md
#51-digit-list-correctness`) rather than by trusting `Nat.repr`/`toString`. It exists to give
`Spikes/Spike2Fibonacci`'s inline hardware itoa (`Spikes/Spike2Fibonacci/Windows/Program.lean`'s
`digit_extract_loop`/`digit_write_loop`) a proven specification to be checked against, instead of
each spike re-deriving its own unverified digit-extraction argument
(`docs/STDLIB_FMT.md#6-spike-2-migration-status`).

No `partial def` appears anywhere in this library (`Basic.lean`, `Parser.lean`, `Roundtrip.lean`):
`digits` is well-founded recursion on `n` with an explicit `termination_by`/`decreasing_by`
(`n / 10 < n` whenever `n ≥ 10`, the same measure `Stdlib.Http11.Basic.natToDigitBytes` uses for
its own, narrower-scoped `Content-Length` digit codec); `formatDecimal` is a plain `List.map` over
`digits`' output, hence structural.
-/

namespace Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- Decodes one ASCII decimal digit byte (`'0'..'9'`, `0x30..0x39`) to its numeric value, or
    `none` if `b` is not a digit byte. -/
def digitOfByte? (b : UInt8) : Option Nat :=
  if b ≥ 0x30 && b ≤ 0x39 then some (b - 0x30).toNat else none

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- Encodes a digit value `0..9` as its ASCII byte. Only meaningful for `d < 10` -- every call
    site in this library supplies a digit produced by `digits`, which `digits_lt_ten` proves is
    always `< 10`. -/
def byteOfDigit (d : Nat) : UInt8 :=
  (0x30 + d).toUInt8

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- The minimal (no leading zeros; `[0]` for zero), most-significant-digit-first decimal digit
    sequence for `n`. Well-founded recursion on `n` (`n / 10 < n` whenever `n ≥ 10`), not
    `partial def` -- see the module docstring. -/
def digits (n : Nat) : List Nat :=
  if h : n < 10 then
    [n]
  else
    digits (n / 10) ++ [n % 10]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- The canonical ASCII decimal encoding of `n`: `digits n`, each digit mapped to its byte. -/
def formatDecimal (n : Nat) : List UInt8 :=
  (digits n).map byteOfDigit

/-
### Digit-list facts (`docs/STDLIB_FMT.md#51-digit-list-correctness`)
-/

/- REF: docs/STDLIB_FMT.md#51-digit-list-correctness -/
/-- `digits` never produces an empty sequence -- every `Nat`, including `0`, has at least one
    digit. -/
theorem digits_ne_nil (n : Nat) : digits n ≠ [] := by
  unfold digits
  split <;> simp

/- REF: docs/STDLIB_FMT.md#51-digit-list-correctness -/
/-- Every digit `digits n` produces is a genuine decimal digit, `< 10`. Proved by strong
    induction on `n`, mirroring `digits`' own recursion. -/
theorem digits_lt_ten (n : Nat) : ∀ d ∈ digits n, d < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold digits
    split
    · rename_i h
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · rename_i h
      intro d hd
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with hd | hd
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) d hd
      · omega

/- REF: docs/STDLIB_FMT.md#51-digit-list-correctness -/
/-- **The digit-list correctness theorem.** Folding `digits n` back together with the standard
    positional-notation accumulator (`10 * acc + d`, starting at `0`) recovers exactly `n` --
    the checkable statement that `digits n` really is "the decimal representation of `n`", not
    merely some list of small numbers. Proved by strong induction on `n`, mirroring `digits`'
    own recursion: the base case is `10 * 0 + n = n`; the step uses `List.foldl_append` to split
    the fold across `digits (n / 10) ++ [n % 10]`, the induction hypothesis to resolve the first
    part to `n / 10`, and `Nat.div_add_mod`-shape arithmetic (closed by `omega`, which has
    built-in support for `Nat` `/`/`%` by numeral divisors) to recombine `10 * (n / 10) + n % 10`
    into `n`. -/
theorem digits_foldl_eq (n : Nat) :
    (digits n).foldl (fun acc d => 10 * acc + d) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold digits
    split
    · rename_i h
      simp
    · rename_i h
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) (Nat.div_lt_self (by omega) (by omega))]
      omega

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
/-- Every `n < 10` has exactly the one-digit representation `[n]` -- the case
    `Spikes.Spike2Fibonacci.Windows.Program`'s loop-index formatting (`i < 10`) branches on. -/
theorem digits_single (n : Nat) (h : n < 10) : digits n = [n] := by
  unfold digits
  rw [dif_pos h]

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
/-- Every `n` in `10..99` has exactly a two-digit representation -- the case
    `Spikes.Spike2Fibonacci.Windows.Program`'s loop-index formatting (`i ≥ 10`) branches on. -/
theorem digits_length_two (n : Nat) (h1 : 10 ≤ n) (h2 : n < 100) :
    (digits n).length = 2 := by
  unfold digits
  rw [dif_neg (by omega)]
  have : n / 10 < 10 := by omega
  rw [digits_single (n / 10) this]
  simp

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
/-- **The buffer-fit theorem.** If `n` fits in `k` decimal digits (`n < 10 ^ k`, `k ≥ 1`), then
    `digits n` (hence `formatDecimal n`, `formatDecimal_length_le` below) is at most `k` bytes
    long -- exactly the fact a stack-buffer itoa needs to know its write never overruns a
    `k`-byte reservation. Proved by strong induction on `n`: the base case (`n < 10`) needs only
    `k ≥ 1`; the step first shows `n ≥ 10` together with `n < 10 ^ k` forces `k ≥ 2` (`k = 1`
    would mean `10 ^ k = 10 > n ≥ 10`, absurd), then transports the bound to `n / 10 < 10 ^
    (k - 1)` via `10 ^ k = 10 ^ (k - 1) * 10` and `Nat.div_lt_iff_lt_mul`. -/
theorem digits_length_le (n k : Nat) (hk0 : 0 < k) (hk : n < 10 ^ k) :
    (digits n).length ≤ k := by
  induction n using Nat.strongRecOn generalizing k with
  | _ n ih =>
    unfold digits
    split
    · simp; omega
    · rename_i h
      have hk2 : 2 ≤ k := by
        have hne1 : k ≠ 1 := by
          intro hk1
          subst hk1
          simp at hk
          omega
        omega
      have hpow : (10:Nat) ^ k = 10 ^ (k - 1) * 10 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      have hstep : n < 10 ^ (k - 1) * 10 := by rw [← hpow]; exact hk
      have hdiv : n / 10 < 10 ^ (k - 1) := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        exact hstep
      have hrec := ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) (k - 1) (by omega) hdiv
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
/-- Specialization of `digits_length_le` to `UInt64`-range values (`n < 2 ^ 64 < 10 ^ 20`) --
    exactly the fact `Spikes.Spike2Fibonacci.Windows.Program`'s Fibonacci-value itoa
    (operating on a `UInt64` register) needs to know its digit-extraction loop writes at most
    20 bytes into the stack buffer. -/
theorem digits_length_le_UInt64 (n : UInt64) : (digits n.toNat).length ≤ 20 := by
  have hlt : n.toNat < 10 ^ 20 := by
    have h1 := n.toNat_lt_size
    have h2 : UInt64.size = 2 ^ 64 := rfl
    have h3 : (2:Nat) ^ 64 < 10 ^ 20 := by decide
    omega
  exact digits_length_le n.toNat 20 (by omega) hlt

/-
### Byte-level (`formatDecimal`) corollaries
-/

/- REF: docs/STDLIB_FMT.md#4-encoder-canonical-serialization -/
theorem formatDecimal_ne_nil (n : Nat) : formatDecimal n ≠ [] := by
  unfold formatDecimal
  simpa using digits_ne_nil n

/- REF: docs/STDLIB_FMT.md#4-encoder-canonical-serialization -/
theorem formatDecimal_length_eq (n : Nat) :
    (formatDecimal n).length = (digits n).length := by
  unfold formatDecimal
  simp

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
theorem formatDecimal_length_le (n k : Nat) (hk0 : 0 < k) (hk : n < 10 ^ k) :
    (formatDecimal n).length ≤ k := by
  rw [formatDecimal_length_eq]
  exact digits_length_le n k hk0 hk

/- REF: docs/STDLIB_FMT.md#54-length-and-buffer-fit-bounds -/
theorem formatDecimal_length_le_UInt64 (n : UInt64) : (formatDecimal n.toNat).length ≤ 20 := by
  rw [formatDecimal_length_eq]
  exact digits_length_le_UInt64 n

/- REF: docs/STDLIB_FMT.md#2-digit-grammar -/
/-- Every byte `formatDecimal` produces is an ASCII decimal digit (`0x30`-`0x39`). -/
theorem formatDecimal_range (n : Nat) : ∀ b ∈ formatDecimal n, 0x30 ≤ b ∧ b ≤ 0x39 := by
  unfold formatDecimal
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨d, hd, rfl⟩ := hb
  have hd10 := digits_lt_ten n d hd
  unfold byteOfDigit
  have h9 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases h9 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end Stdlib.Fmt

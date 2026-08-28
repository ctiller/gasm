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
## Stdlib.Http11.Basic

Byte-level primitives shared by `Stdlib/Http11/Request.lean` and
`Stdlib/Http11/Response.lean`: character classes, a decimal-digit codec for
`Content-Length`, and two structurally/well-founded-recursive line-splitting
functions (`takeLine`, `peelLines`) that both the parser and its roundtrip
proof are built from. Everything here operates on `List UInt8`, not
`ByteArray` or `String` -- see `docs/STDLIB_HTTP11.md#1-overview--scope` for
why: a byte-native representation keeps every structural-recursion and
`List.append` argument in this file a standard `List` induction, with no
UTF-8 encode/decode lemma required anywhere in the round-trip proof.

No `partial def` appears in this file or in `Request.lean`/`Response.lean`:
every recursive function here is either plain structural recursion (accepted
automatically by Lean's equation compiler) or well-founded recursion with an
explicit `termination_by`/`decreasing_by` (`peelLines`), matching the "total
functions, explicit termination measures" requirement for code that parses
untrusted network input -- see `docs/STDLIB_HTTP11.md#31-error-taxonomy`.
-/

namespace Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/-- Every way `parseRequest`/`parseResponse` can reject a byte string. -/
inductive Error
  | headersNotTerminated
  | malformedRequestLine
  | malformedStatusLine
  | unknownMethod
  | invalidTarget
  | unsupportedVersion
  | malformedHeaderLine
  | invalidHeaderName
  | invalidHeaderValue
  | missingContentLength
  | duplicateContentLength
  | malformedContentLength
  | bodyLengthMismatch
  | invalidStatusCode
  | invalidReasonPhrase
  deriving DecidableEq, Repr, BEq

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- ASCII CR (0x0D), the first byte of every line terminator this library recognizes. -/
def CR : UInt8 := 0x0D

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- ASCII LF (0x0A), the second byte of every line terminator this library recognizes. -/
def LF : UInt8 := 0x0A

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- ASCII SP (0x20), the request-line/status-line field separator. -/
def SP : UInt8 := 0x20

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- ASCII HTAB (0x09), permitted inside (but not synthesized by the writer at the edges of)
    a header field-value. -/
def HTAB : UInt8 := 0x09

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- ASCII COLON (0x3A), separating a header field-name from its field-value. -/
def COLON : UInt8 := 0x3A

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- RFC 9112 `tchar` -- the token character class used for `Method` names and header
    field-names: `DIGIT`, `ALPHA`, and `` !#$%&'*+-.^_`|~ ``. -/
def isTChar (b : UInt8) : Bool :=
  (b ≥ 0x41 && b ≤ 0x5A) || (b ≥ 0x61 && b ≤ 0x7A) || (b ≥ 0x30 && b ≤ 0x39) ||
  b == 0x21 || (b ≥ 0x23 && b ≤ 0x27) || b == 0x2A || b == 0x2B ||
  b == 0x2D || b == 0x2E || b == 0x5E || b == 0x5F || b == 0x60 ||
  b == 0x7C || b == 0x7E

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- Visible US-ASCII (0x21-0x7E): the request-target character class, and the core of the
    header field-value character class. Deliberately excludes obs-text (0x80-0xFF) -- see
    `docs/STDLIB_HTTP11.md#12-deliberate-omissions`. -/
def isVChar (b : UInt8) : Bool := b ≥ 0x21 && b ≤ 0x7E

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- Header field-value character class: visible US-ASCII plus internal SP/HTAB. -/
def isFieldValueByte (b : UInt8) : Bool := isVChar b || b == SP || b == HTAB

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- A non-empty `tchar` run: valid as a `Method` name or a header field-name. -/
def validToken (bs : List UInt8) : Bool := !bs.isEmpty && bs.all isTChar

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- A valid header field-value or status-line reason-phrase: every byte is a field-value
    byte. May be empty (an empty reason-phrase, or an empty header value, are both legal). -/
def validFieldValue (bs : List UInt8) : Bool := bs.all isFieldValueByte

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- A valid origin-form request-target: non-empty, first byte `'/'` (0x2F), every byte
    visible US-ASCII (so it can never itself contain the SP that delimits it on the wire). -/
def validTarget (bs : List UInt8) : Bool :=
  match bs with
  | [] => false
  | b0 :: _ => b0 == 0x2F && bs.all isVChar

/-
### Decimal digit codec for `Content-Length`

`natToDigitBytes`/`digitBytesToNat?` are this library's own from-scratch decimal codec,
proved round-trip-correct below (`digitBytesToNat?_natToDigitBytes`) by well-founded
induction on the encoder's own recursion -- deliberately not built on `Nat.repr`/`toString`,
so the proof does not depend on core's string-formatting internals.
-/

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Encodes a `Nat` as its minimal (no leading zeros, "0" for zero) run of ASCII decimal
    digit bytes. Well-founded recursion on `n` (`n / 10 < n` whenever `n ≥ 10`) -- not
    `partial def`. -/
def natToDigitBytes (n : Nat) : List UInt8 :=
  if h : n < 10 then
    [(0x30 + n).toUInt8]
  else
    natToDigitBytes (n / 10) ++ [(0x30 + n % 10).toUInt8]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Decodes one ASCII decimal digit byte, or `none` if `b` is not `'0'..'9'`. -/
def digitByteToNat? (b : UInt8) : Option Nat :=
  if b ≥ 0x30 && b ≤ 0x39 then some (b - 0x30).toNat else none

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Left-fold accumulator for `digitBytesToNat?`. Structurally recursive on `bs`. -/
def digitBytesToNatAux : List UInt8 → Nat → Option Nat
  | [], acc => some acc
  | b :: rest, acc =>
      match digitByteToNat? b with
      | some d => digitBytesToNatAux rest (acc * 10 + d)
      | none => none

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Decodes a non-empty run of ASCII decimal digit bytes into the `Nat` it denotes;
    `none` on an empty run or any non-digit byte -- an empty `Content-Length` value is a
    parse error, not a silent zero. -/
def digitBytesToNat? (bs : List UInt8) : Option Nat :=
  if bs.isEmpty then none else digitBytesToNatAux bs 0

theorem digitByteToNat?_of_digit (n : Nat) (h : n < 10) :
    digitByteToNat? ((0x30 + n).toUInt8) = some n := by
  have h10 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
    omega
  rcases h10 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Auxiliary accumulator form of the round-trip lemma: folding the digits of `n` (with an
    arbitrary starting accumulator `acc`) reproduces `acc * 10 ^ (digit count) + n`. Proved
    by strong induction on `n`, mirroring `natToDigitBytes`'s own recursion. -/
theorem digitBytesToNatAux_natToDigitBytes (n : Nat) :
    ∀ acc, digitBytesToNatAux (natToDigitBytes n) acc = some (acc * 10 ^ (natToDigitBytes n).length + n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    unfold natToDigitBytes
    split
    · rename_i h
      simp only [digitBytesToNatAux, digitByteToNat?_of_digit n h]
      simp [List.length]
    · rename_i h
      -- `split` above already rewrote *every* occurrence of `natToDigitBytes n` in the goal
      -- (both the `digitBytesToNatAux` argument and the `.length` in the target sum) to the
      -- else-branch `natToDigitBytes (n / 10) ++ [...]`, so no separate unfolding lemma for
      -- `(natToDigitBytes n).length` is needed -- `List.length_append` below acts directly on
      -- the append already sitting in the goal.
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hfold : ∀ (l : List UInt8) (x : UInt8) (a : Nat),
          digitBytesToNatAux (l ++ [x]) a =
            match digitBytesToNatAux l a with
            | some v => (match digitByteToNat? x with | some d => some (v * 10 + d) | none => none)
            | none => none := by
        intro l
        induction l with
        | nil => intro x a; simp [digitBytesToNatAux]
        | cons b t iht =>
          intro x a
          simp only [List.cons_append, digitBytesToNatAux]
          cases digitByteToNat? b with
          | none => simp
          | some d => exact iht x (a * 10 + d)
      rw [hfold, ih (n / 10) hlt acc]
      have hdig : digitByteToNat? ((0x30 + n % 10).toUInt8) = some (n % 10) :=
        digitByteToNat?_of_digit (n % 10) (Nat.mod_lt n (by omega))
      rw [hdig]
      simp only [List.length_append, List.length_cons, List.length_nil]
      -- Reduce to a purely linear fact by naming the nonlinear product `acc * 10 ^ L0` once,
      -- via `Nat.pow_succ`/`Nat.mul_assoc` (core lemmas, no `ring`/Mathlib), so `omega` can
      -- finish using its built-in support for `n / 10` and `n % 10`.
      have step : (acc * 10 ^ (natToDigitBytes (n / 10)).length + n / 10) * 10 + n % 10
          = acc * 10 ^ ((natToDigitBytes (n / 10)).length + 0 + 1) + n := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        generalize acc * 10 ^ (natToDigitBytes (n / 10)).length = k
        omega
      simpa using step

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- The round-trip theorem for the `Content-Length` digit codec: every `Nat` survives
    `natToDigitBytes` then `digitBytesToNat?`. This is the base fact `request_roundtrip` /
    `response_roundtrip` reduce their `Content-Length` obligation to. -/
theorem digitBytesToNat?_natToDigitBytes (n : Nat) :
    digitBytesToNat? (natToDigitBytes n) = some n := by
  have hne : ¬ (natToDigitBytes n).isEmpty := by
    unfold natToDigitBytes
    split <;> simp
  simp only [digitBytesToNat?, hne]
  have := digitBytesToNatAux_natToDigitBytes n 0
  simpa using this

/-
### Line splitting

`takeLine` finds the first `CR LF` pair in a byte list and splits there (structural
recursion, one step per byte). `peelLines` repeatedly calls `takeLine`, collecting lines
until an empty one (the header-section terminator) or a `takeLine` failure (an
unterminated line -- `Error.headersNotTerminated`). `peelLines` is well-founded, not
structural: each call it makes to itself is on `takeLine`'s remainder, not a syntactic
sub-term of its own argument, so its termination measure (`List.length`, strictly
decreasing per `takeLine_length_lt`) is stated explicitly.
-/

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- Splits `bs` at the first `CR LF` pair: `some (before, after)` with `before` excluding
    the pair and `after` the bytes following it, or `none` if no `CR LF` pair occurs
    anywhere in `bs`. Structurally recursive: each recursive call is on a literal `List`
    sub-term of `bs`. -/
def takeLine : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
      match rest with
      | [] => none
      | b1 :: rest1 =>
          if b == CR && b1 == LF then
            some ([], rest1)
          else
            match takeLine (b1 :: rest1) with
            | some (line, remainder) => some (b :: line, remainder)
            | none => none

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `takeLine`'s success case strictly shortens the input by at least 2 bytes -- the
    termination measure `peelLines` needs. Proved by the same structural induction as
    `takeLine` itself. -/
theorem takeLine_length_lt (bs : List UInt8) (line remainder : List UInt8)
    (h : takeLine bs = some (line, remainder)) : remainder.length < bs.length := by
  induction bs generalizing line remainder with
  | nil => simp [takeLine] at h
  | cons b rest ih =>
      cases rest with
      | nil => simp [takeLine] at h
      | cons b1 rest1 =>
          simp only [takeLine] at h
          split at h
          · rename_i heq
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            simp [h.2]
            omega
          · rename_i heq
            cases hstep : takeLine (b1 :: rest1) with
            | none => simp [hstep] at h
            | some p =>
                obtain ⟨line', remainder'⟩ := p
                simp only [hstep, Option.some.injEq, Prod.mk.injEq] at h
                have hrec := ih line' remainder' hstep
                simp only [List.length_cons] at hrec
                simp only [← h.2, List.length_cons]
                omega

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- Reads lines off `bs` (via `takeLine`) until an empty line (the header-section
    terminator) is found, returning the non-terminator lines read and the bytes following
    the terminator. `none` if `takeLine` ever fails first (an unterminated line: a
    truncated header section, `Error.headersNotTerminated`). Well-founded on
    `List.length`. -/
def peelLines (bs : List UInt8) : Option (List (List UInt8) × List UInt8) :=
  match h : takeLine bs with
  | none => none
  | some (line, remainder) =>
      if line = [] then
        some ([], remainder)
      else
        have : remainder.length < bs.length := takeLine_length_lt bs line remainder h
        match peelLines remainder with
        | none => none
        | some (lines, body) => some (line :: lines, body)
termination_by bs.length

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Splits `bs` at the first SP byte: `some (before, after)`, or `none` if `bs` contains
    no SP at all. Structurally recursive, the same shape as `takeLine` but for a
    single-byte separator (request-line/status-line field splitting never needs more than
    one lookahead byte). -/
def splitFirstSpace : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
      if b == SP then
        some ([], rest)
      else
        match splitFirstSpace rest with
        | some (before, after) => some (b :: before, after)
        | none => none

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- Splits a header line at its first `":" SP` occurrence: `some (name, value)`, or `none`
    if no colon is present, or the byte immediately following the first colon is not SP
    (this library requires the canonical single-space form on the wire; see
    `docs/STDLIB_HTTP11.md#23-header-fields`). Structurally recursive. -/
def splitHeaderLine : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
      if b == COLON then
        match rest with
        | b1 :: rest1 => if b1 == SP then some ([], rest1) else none
        | [] => none
      else
        match splitHeaderLine rest with
        | some (name, value) => some (b :: name, value)
        | none => none

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `takeLine` recovers exactly a byte string freshly terminated with `CR LF`, provided the
    string itself contains neither byte -- the structural fact the writer/parser round-trip
    proof reduces every line-level recovery obligation to. -/
theorem takeLine_append_crlf (rest : List UInt8) :
    ∀ content : List UInt8, (∀ b ∈ content, b ≠ CR ∧ b ≠ LF) →
      takeLine (content ++ CR :: LF :: rest) = some (content, rest) := by
  intro content
  induction content with
  | nil => intro _; rfl
  | cons b t ih =>
    intro hall
    have ht : ∀ x ∈ t, x ≠ CR ∧ x ≠ LF := fun x hx => hall x (List.mem_cons_of_mem b hx)
    rcases t with _ | ⟨b1, t1⟩
    · have hb : b ≠ CR ∧ b ≠ LF := hall b (List.mem_cons_self)
      show takeLine (b :: CR :: LF :: rest) = some ([b], rest)
      simp only [takeLine]
      have hcond : (b == CR && CR == LF) = false := by
        simp [beq_iff_eq, hb.1]
      simp only [hcond, Bool.false_eq_true, if_false]
      rfl
    · have hb1 : b1 ≠ LF := (ht b1 (List.mem_cons_self)).2
      show takeLine (b :: b1 :: (t1 ++ CR :: LF :: rest)) = some (b :: b1 :: t1, rest)
      simp only [takeLine]
      have hcond : (b == CR && b1 == LF) = false := by
        simp [beq_iff_eq, hb1]
      simp only [hcond, Bool.false_eq_true, if_false]
      have hrec := ih ht
      simp only [List.cons_append] at hrec
      rw [hrec]



/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- One controlled unfolding step of `peelLines`, restated without the internal dependent
    `match h : takeLine bs with ...` binder so ordinary `rw`/`simp` can use it -- `peelLines`
    is well-founded recursive, so including it directly in a `simp` set loops (`simp` cannot
    tell when to stop re-unfolding the recursive call in its own else-branch). -/
theorem peelLines_eq_of_takeLine {bs line remainder : List UInt8}
    (h : takeLine bs = some (line, remainder)) :
    peelLines bs = if line = [] then some ([], remainder) else
      match peelLines remainder with
      | none => none
      | some (lines, body) => some (line :: lines, body) := by
  rw [peelLines.eq_1]
  split
  · rename_i heq
    rw [h] at heq
    exact absurd heq (by simp)
  · rename_i line' remainder' heq
    rw [h] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `peelLines` recovers exactly a written list of non-empty lines, each individually
    `CR LF`-terminated, immediately followed by the blank-line terminator and a body --
    the structural fact `writeRequest`/`writeResponse`'s parse-back proof reduces its
    "recover every header line" obligation to. -/
theorem peelLines_append (body : List UInt8) :
    ∀ lines : List (List UInt8),
      (∀ l ∈ lines, l ≠ []) → (∀ l ∈ lines, ∀ b ∈ l, b ≠ CR ∧ b ≠ LF) →
      peelLines ((lines.map (· ++ [CR, LF])).flatten ++ CR :: LF :: body)
        = some (lines, body) := by
  intro lines
  induction lines with
  | nil =>
    intro _ _
    show peelLines (CR :: LF :: body) = some ([], body)
    have hstep : takeLine (CR :: LF :: body) = some ([], body) := by
      have := takeLine_append_crlf body [] (by simp)
      simpa using this
    rw [peelLines_eq_of_takeLine hstep]
    simp
  | cons l ls ih =>
    intro hne hcc
    have hlne : l ≠ [] := hne l List.mem_cons_self
    have hl : ∀ b ∈ l, b ≠ CR ∧ b ≠ LF := hcc l List.mem_cons_self
    have hlsne : ∀ l' ∈ ls, l' ≠ [] := fun l' hl' => hne l' (List.mem_cons_of_mem l hl')
    have hlscc : ∀ l' ∈ ls, ∀ b ∈ l', b ≠ CR ∧ b ≠ LF :=
      fun l' hl' b hb => hcc l' (List.mem_cons_of_mem l hl') b hb
    show peelLines ((l ++ [CR, LF]) ++ (ls.map (· ++ [CR, LF])).flatten ++ CR :: LF :: body)
        = some (l :: ls, body)
    have hassoc : (l ++ [CR, LF]) ++ (ls.map (· ++ [CR, LF])).flatten ++ CR :: LF :: body
        = l ++ CR :: LF :: ((ls.map (· ++ [CR, LF])).flatten ++ CR :: LF :: body) := by
      simp [List.append_assoc]
    rw [hassoc]
    have hstep := takeLine_append_crlf
      ((ls.map (· ++ [CR, LF])).flatten ++ CR :: LF :: body) l hl
    have hrec := ih hlsne hlscc
    rw [peelLines_eq_of_takeLine hstep]
    simp only [hlne, if_false, hrec]


/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- `splitFirstSpace` recovers exactly the byte string preceding a freshly-inserted SP,
    provided that string contains no SP itself -- the structural fact request-line/status-line
    field recovery reduces to. -/
theorem splitFirstSpace_append (rest : List UInt8) :
    ∀ before : List UInt8, (∀ b ∈ before, b ≠ SP) →
      splitFirstSpace (before ++ SP :: rest) = some (before, rest) := by
  intro before
  induction before with
  | nil => intro _; rfl
  | cons b t ih =>
    intro hall
    have hb : b ≠ SP := hall b List.mem_cons_self
    have ht : ∀ x ∈ t, x ≠ SP := fun x hx => hall x (List.mem_cons_of_mem b hx)
    show splitFirstSpace (b :: (t ++ SP :: rest)) = some (b :: t, rest)
    simp only [splitFirstSpace]
    have hcond : (b == SP) = false := by simp [hb]
    simp only [hcond, Bool.false_eq_true, if_false]
    rw [ih ht]

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `splitHeaderLine` recovers exactly the field-name preceding a freshly-inserted `": "`,
    provided that name contains no colon itself (guaranteed by the `tchar` token grammar) --
    the structural fact header-line field recovery reduces to. -/
theorem splitHeaderLine_append (value : List UInt8) :
    ∀ name : List UInt8, (∀ b ∈ name, b ≠ COLON) →
      splitHeaderLine (name ++ COLON :: SP :: value) = some (name, value) := by
  intro name
  induction name with
  | nil => intro _; rfl
  | cons b t ih =>
    intro hall
    have hb : b ≠ COLON := hall b List.mem_cons_self
    have ht : ∀ x ∈ t, x ≠ COLON := fun x hx => hall x (List.mem_cons_of_mem b hx)
    show splitHeaderLine (b :: (t ++ COLON :: SP :: value)) = some (b :: t, value)
    simp only [splitHeaderLine]
    have hcond : (b == COLON) = false := by simp [hb]
    simp only [hcond, Bool.false_eq_true, if_false]
    rw [ih ht]

end Stdlib.Http11

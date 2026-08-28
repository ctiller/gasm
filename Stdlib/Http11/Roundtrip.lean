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

import Stdlib.Http11.Parser
import Stdlib.Http11.Writer

/-
## Stdlib.Http11.Roundtrip

The two round-trip theorems, per `docs/STDLIB_HTTP11.md#5-formal-theorems`:

1. `request_roundtrip` / `response_roundtrip` (§5.1): `∀ r, parseRequest (writeRequest r) =
   .ok r` -- universally quantified over *every* structured value, forbidding an
   always-failing parser.
2. `request_parse_reencode_stable` / `response_parse_reencode_stable` (§5.2): `∀ b r₁ r₂,
   parseRequest b = .ok r₁ → parseRequest (writeRequest r₁) = .ok r₂ → r₁ = r₂` -- ranging over
   *every* byte string (including adversarial ones), forbidding a lossy parser. This is a
   direct corollary of (1) plus `parseRequest`/`parseResponse`'s own determinism (both are
   plain functions of their input): instantiating (1) at `r₁` gives `parseRequest (writeRequest
   r₁) = .ok r₁` unconditionally, which the second hypothesis then forces to equal `.ok r₂` by
   injectivity of `Except.ok`. (1) is this theorem's non-vacuity floor: on its own, (2) would be
   satisfiable by a parser that always returns `.error` (its first hypothesis would simply never
   fire), but (1) independently forbids that.

`write (parse b) = b` is deliberately **not** claimed and is false in general for HTTP (header
case, optional whitespace, and header order all admit multiple byte strings for one structured
value) -- see `docs/STDLIB_HTTP11.md#51-write-then-parse-roundtrip-theorems`.

The bulk of this file (everything before `request_roundtrip` itself) proves that each piece
`writeRequest`/`writeResponse` writes is exactly what `parseRequest`/`parseResponse` reads back:
line boundaries (`peelLines_append` from `Basic.lean`), the request/status line's three
space-separated fields, each header's `name ": " value`, and the synthesized `Content-Length`
header/body-length pair. Every one of these facts reduces, ultimately, to a character-class
argument: a written field never itself contains the delimiter byte(s) used to split it back out,
because `Request`/`Response`'s own proof fields (`targetOk`, `headersOk`, ...) already restrict
every field to a byte class disjoint from `CR`/`LF`/`SP`/`COLON` as appropriate.
-/

namespace Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
theorem writeRequestLine_ne_nil (m : Method) (target : List UInt8) :
    writeRequestLine m target ≠ [] := by
  unfold writeRequestLine
  cases m <;> simp

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
theorem writeHeaderLine_ne_nil (h : List UInt8 × List UInt8) : writeHeaderLine h ≠ [] := by
  unfold writeHeaderLine
  simp

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
theorem writeContentLengthLine_ne_nil (n : Nat) : writeContentLengthLine n ≠ [] := by
  unfold writeContentLengthLine
  simp [contentLengthBytes]

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- A request line's wire bytes contain no `CR`/`LF`: the method is `tchar` (excludes control
    bytes), the target is `vchar` (`targetOk`, excludes control bytes), `SP` and
    `httpVersionBytes`' literal bytes are neither `CR` nor `LF`. -/
theorem writeRequestLine_no_crlf (m : Method) (target : List UInt8)
    (ht : validTarget target = true) :
    ∀ b ∈ writeRequestLine m target, b ≠ CR ∧ b ≠ LF := by
  intro b hb
  simp only [writeRequestLine, List.mem_append, List.mem_cons] at hb
  have htv : target.all isVChar = true := by
    unfold validTarget at ht
    cases target with
    | nil => simp at ht
    | cons b0 t => simp only [Bool.and_eq_true] at ht; exact ht.2
  rcases hb with (hb | rfl | hb) | rfl | hb
  · exact isTChar_not_crlf (List.all_eq_true.mp
      (by have := Method.toBytes_validToken m; unfold validToken at this
          simp only [Bool.and_eq_true] at this; exact this.2) b hb)
  · simp [SP, CR, LF]
  · exact isVChar_not_crlf (List.all_eq_true.mp htv b hb)
  · simp [SP, CR, LF]
  · simp only [httpVersionBytes, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/-- A status line's wire bytes contain no `CR`/`LF`: `httpVersionBytes` and `SP`'s literal
    bytes, the status code's digits (`natToDigitBytes_not_crlf`), and the reason phrase
    (`reasonOk`'s field-value byte class) are all `CR`/`LF`-free. -/
theorem writeStatusLine_no_crlf (statusCode : Nat) (reason : List UInt8)
    (hr : validFieldValue reason = true) :
    ∀ b ∈ writeStatusLine statusCode reason, b ≠ CR ∧ b ≠ LF := by
  intro b hb
  simp only [writeStatusLine, List.mem_append, List.mem_cons] at hb
  rcases hb with (hb | rfl | hb) | rfl | hb
  · simp only [httpVersionBytes, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · simp [SP, CR, LF]
  · exact natToDigitBytes_not_crlf statusCode b hb
  · simp [SP, CR, LF]
  · exact isFieldValueByte_not_crlf (List.all_eq_true.mp hr b hb)

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- A header line's wire bytes contain no `CR`/`LF`: the name is `tchar`, `":" SP` are literal
    non-`CR`/`LF` bytes, and the value is a field-value byte (`headerFieldOk`). -/
theorem writeHeaderLine_no_crlf (h : List UInt8 × List UInt8) (hok : headerFieldOk h = true) :
    ∀ b ∈ writeHeaderLine h, b ≠ CR ∧ b ≠ LF := by
  intro b hb
  simp only [writeHeaderLine, List.mem_append, List.mem_cons] at hb
  unfold headerFieldOk at hok
  simp only [Bool.and_eq_true] at hok
  have hname := hok.1.1.1
  have hval := hok.1.1.2
  unfold validToken at hname
  simp only [Bool.and_eq_true] at hname
  rcases hb with hb | rfl | rfl | hb
  · exact isTChar_not_crlf (List.all_eq_true.mp hname.2 b hb)
  · simp [COLON, CR, LF]
  · simp [SP, CR, LF]
  · exact isFieldValueByte_not_crlf (List.all_eq_true.mp hval b hb)

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
theorem writeContentLengthLine_no_crlf (n : Nat) :
    ∀ b ∈ writeContentLengthLine n, b ≠ CR ∧ b ≠ LF := by
  intro b hb
  simp only [writeContentLengthLine, List.mem_append, List.mem_cons] at hb
  rcases hb with hb | rfl | rfl | hb
  · simp only [contentLengthBytes, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · simp [COLON, CR, LF]
  · simp [SP, CR, LF]
  · exact natToDigitBytes_not_crlf n b hb

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
theorem requestLines_ne_nil (r : Request) : ∀ l ∈ requestLines r, l ≠ [] := by
  intro l hl
  unfold requestLines at hl
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | ⟨h, _, rfl⟩) | rfl
  · exact writeRequestLine_ne_nil r.method r.target
  · exact writeHeaderLine_ne_nil h
  · exact writeContentLengthLine_ne_nil r.body.length

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
theorem requestLines_no_crlf (r : Request) :
    ∀ l ∈ requestLines r, ∀ b ∈ l, b ≠ CR ∧ b ≠ LF := by
  intro l hl
  unfold requestLines at hl
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | ⟨h, hh, rfl⟩) | rfl
  · exact writeRequestLine_no_crlf r.method r.target r.targetOk
  · exact writeHeaderLine_no_crlf h (List.all_eq_true.mp r.headersOk h hh)
  · exact writeContentLengthLine_no_crlf r.body.length

/- REF: docs/STDLIB_HTTP11.md#3-parser-behavior -/
/-- `peelLines` recovers exactly `writeRequest r`'s own line decomposition -- direct application
    of `Basic.peelLines_append` to `requestLines_ne_nil`/`requestLines_no_crlf`. -/
theorem peelLines_writeRequest (r : Request) :
    peelLines (writeRequest r) = some (requestLines r, r.body) := by
  unfold writeRequest
  exact peelLines_append r.body (requestLines r) (requestLines_ne_nil r) (requestLines_no_crlf r)

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- `parseRequestLine` recovers exactly the method/target `writeRequestLine` wrote. -/
theorem parseRequestLine_writeRequestLine (m : Method) (target : List UInt8)
    (ht : validTarget target = true) :
    parseRequestLine (writeRequestLine m target) = .ok (m, target) := by
  have hshape : writeRequestLine m target
      = m.toBytes ++ SP :: (target ++ SP :: httpVersionBytes) := by
    unfold writeRequestLine
    simp only [List.append_assoc, List.cons_append]
  have htv : target.all isVChar = true := by
    unfold validTarget at ht
    cases target with
    | nil => simp at ht
    | cons b0 t => simp only [Bool.and_eq_true] at ht; exact ht.2
  have hmtok := Method.toBytes_validToken m
  unfold validToken at hmtok
  simp only [Bool.and_eq_true] at hmtok
  have hs1 : splitFirstSpace (writeRequestLine m target)
      = some (m.toBytes, target ++ SP :: httpVersionBytes) := by
    rw [hshape]
    exact splitFirstSpace_append _ m.toBytes
      (fun b hb => isTChar_ne_sp (List.all_eq_true.mp hmtok.2 b hb))
  have hs2 :
      splitFirstSpace (target ++ SP :: httpVersionBytes) = some (target, httpVersionBytes) :=
    splitFirstSpace_append _ target (fun b hb => isVChar_ne_sp (List.all_eq_true.mp htv b hb))
  have hs3 : splitFirstSpace httpVersionBytes = none := by decide
  unfold parseRequestLine splitThreeFields
  simp only [hs1, hs2, hs3, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [Method.ofBytes?_toBytes]
  simp only [ht, if_true]

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `parseHeaderLine` recovers exactly the name/value `writeHeaderLine` wrote. -/
theorem parseHeaderLine_writeHeaderLine (h : List UInt8 × List UInt8)
    (hok : headerFieldOk h = true) :
    parseHeaderLine (writeHeaderLine h) = .ok h := by
  unfold headerFieldOk at hok
  simp only [Bool.and_eq_true] at hok
  have hname : validToken h.1 = true := hok.1.1.1
  have hval : validFieldValue h.2 = true := hok.1.1.2
  have hows : noOwsEdges h.2 = true := hok.1.2
  have hnameTok := hname
  unfold validToken at hnameTok
  simp only [Bool.and_eq_true] at hnameTok
  have hsplit : splitHeaderLine (writeHeaderLine h) = some (h.1, h.2) := by
    unfold writeHeaderLine
    exact splitHeaderLine_append h.2 h.1
      (fun b hb => isTChar_ne_colon (List.all_eq_true.mp hnameTok.2 b hb))
  unfold parseHeaderLine
  simp only [hsplit, hname, if_true, hval, hows, Bool.and_self]

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- `parseHeaderLine` recovers exactly the `(Content-Length, digits)` pair
    `writeContentLengthLine` wrote (it is, definitionally, `writeHeaderLine` applied to that
    pair -- see `Writer.lean`). -/
theorem parseHeaderLine_writeContentLengthLine (n : Nat) :
    parseHeaderLine (writeContentLengthLine n) = .ok (contentLengthBytes, natToDigitBytes n) := by
  have hshape : writeContentLengthLine n
      = contentLengthBytes ++ COLON :: SP :: natToDigitBytes n := rfl
  have hnc : ∀ b ∈ contentLengthBytes, b ≠ COLON := by decide
  have hsplit : splitHeaderLine (writeContentLengthLine n)
      = some (contentLengthBytes, natToDigitBytes n) := by
    rw [hshape]
    exact splitHeaderLine_append _ contentLengthBytes hnc
  have htok : validToken contentLengthBytes = true := by decide
  have hval := natToDigitBytes_validFieldValue n
  have hows := natToDigitBytes_noOwsEdges n
  unfold parseHeaderLine
  simp only [hsplit, htok, if_true, hval, hows, Bool.and_self]

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `parseHeaderLines` recovers exactly a written header list plus one extra trailing line
    (the synthesized `Content-Length` line, in `request_roundtrip`'s use), each parsed
    independently in order. -/
theorem parseHeaderLines_map_append (headers : List (List UInt8 × List UInt8))
    (extra : List UInt8 × List UInt8) (hh : ∀ h ∈ headers, headerFieldOk h = true)
    (he : parseHeaderLine (writeHeaderLine extra) = .ok extra) :
    parseHeaderLines (headers.map writeHeaderLine ++ [writeHeaderLine extra])
      = .ok (headers ++ [extra]) := by
  induction headers with
  | nil =>
    show parseHeaderLines [writeHeaderLine extra] = .ok [extra]
    unfold parseHeaderLines
    rw [he]
    rfl
  | cons h t ih =>
    have hht : ∀ h' ∈ t, headerFieldOk h' = true :=
      fun h' hh' => hh h' (List.mem_cons_of_mem h hh')
    have hh0 : headerFieldOk h = true := hh h List.mem_cons_self
    show parseHeaderLines (writeHeaderLine h :: (t.map writeHeaderLine ++ [writeHeaderLine extra]))
        = .ok (h :: t ++ [extra])
    unfold parseHeaderLines
    rw [parseHeaderLine_writeHeaderLine h hh0, ih hht]
    rfl

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
theorem isContentLengthName_self : isContentLengthName contentLengthBytes = true := by decide

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- `extractContentLength` recovers exactly `n` and the original headers, given every header in
    `headers` is (case-insensitively) not named `Content-Length` -- exactly `headersOk`'s own
    invariant. -/
theorem extractContentLength_append (headers : List (List UInt8 × List UInt8)) (n : Nat)
    (hh : ∀ h ∈ headers, isContentLengthName h.1 = false) :
    extractContentLength (headers ++ [(contentLengthBytes, natToDigitBytes n)])
      = .ok (n, headers) := by
  have hfilterT : (headers ++ [(contentLengthBytes, natToDigitBytes n)]).filter
      (fun h => isContentLengthName h.1) = [(contentLengthBytes, natToDigitBytes n)] := by
    rw [List.filter_append]
    have h1 : headers.filter (fun h => isContentLengthName h.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h hmem
      simp [hh h hmem]
    rw [h1]
    simp [isContentLengthName_self]
  have hfilterF : (headers ++ [(contentLengthBytes, natToDigitBytes n)]).filter
      (fun h => !isContentLengthName h.1) = headers := by
    rw [List.filter_append]
    have h1 : headers.filter (fun h => !isContentLengthName h.1) = headers := by
      apply List.filter_eq_self.mpr
      intro h hmem
      simp [hh h hmem]
    rw [h1]
    simp [isContentLengthName_self]
  unfold extractContentLength
  simp only [hfilterT]
  rw [digitBytesToNat?_natToDigitBytes]
  simp [hfilterF]

/- REF: docs/STDLIB_HTTP11.md#51-write-then-parse-roundtrip-theorems -/
/-- **Write-then-parse round trip, requests.** Universally quantified over every structured
    `Request` value -- not a `native_decide` check over sample literals. Forbids an
    always-failing parser: `writeRequest r` must parse back to exactly `r`, for every `r`. -/
theorem request_roundtrip (r : Request) : parseRequest (writeRequest r) = .ok r := by
  have hpeel := peelLines_writeRequest r
  have hheadersOkEach : ∀ h ∈ r.headers, headerFieldOk h = true :=
    fun h hh => List.all_eq_true.mp r.headersOk h hh
  have hCLbytes : writeContentLengthLine r.body.length
      = writeHeaderLine (contentLengthBytes, natToDigitBytes r.body.length) := rfl
  have hparseHdrs : parseHeaderLines (r.headers.map writeHeaderLine ++
      [writeContentLengthLine r.body.length])
      = .ok (r.headers ++ [(contentLengthBytes, natToDigitBytes r.body.length)]) := by
    rw [hCLbytes]
    exact parseHeaderLines_map_append r.headers _ hheadersOkEach
      (parseHeaderLine_writeContentLengthLine r.body.length)
  have hCLexclude : ∀ h ∈ r.headers, isContentLengthName h.1 = false := by
    intro h hh
    have hok := hheadersOkEach h hh
    unfold headerFieldOk at hok
    simp only [Bool.and_eq_true] at hok
    simpa using hok.2
  have hextract := extractContentLength_append r.headers r.body.length hCLexclude
  unfold parseRequest
  rw [hpeel]
  unfold requestLines
  rw [show ([writeRequestLine r.method r.target] ++ r.headers.map writeHeaderLine ++
      [writeContentLengthLine r.body.length] : List (List UInt8)) =
      writeRequestLine r.method r.target :: (r.headers.map writeHeaderLine ++
      [writeContentLengthLine r.body.length]) from rfl]
  simp only [parseRequestLine_writeRequestLine r.method r.target r.targetOk, hparseHdrs, hextract]
  simp only [ne_eq, not_true_eq_false, if_false, r.targetOk, r.headersOk]
  simp

/- REF: docs/STDLIB_HTTP11.md#52-parse-reencode-stability-theorems -/
/-- **Parse-reencode stability, requests.** Ranges over *every* byte string `b` (including
    malformed/adversarial ones), not just ones `writeRequest` produces. A direct corollary of
    `request_roundtrip` plus `parseRequest`'s determinism: instantiating `request_roundtrip` at
    `r1` gives `parseRequest (writeRequest r1) = .ok r1` unconditionally, which `h2` then forces
    to equal `.ok r2` by injectivity of `Except.ok`. `request_roundtrip` is this theorem's
    non-vacuity floor -- on its own this would be satisfiable by a parser that always fails
    (`h1` would simply never fire), but `request_roundtrip` independently forbids that. -/
theorem request_parse_reencode_stable (b : List UInt8) (r1 r2 : Request)
    (_h1 : parseRequest b = .ok r1) (h2 : parseRequest (writeRequest r1) = .ok r2) : r1 = r2 := by
  rw [request_roundtrip r1] at h2
  exact Except.ok.inj h2

/-
### Response

Mirrors the `Request` development above (status line in place of request line; headers and
`Content-Length` are handled by the same generic lemmas). `natToDigitBytes_length3` is the one
genuinely new fact `Request` never needed: a request-target's byte length is unconstrained, but
a status-code is grammatically fixed at exactly three decimal digits, so recovering it from the
writer's output needs `natToDigitBytes`'s own length to be provably `3` on `100..599` (in fact
on all of `100..999`).
-/

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/-- Every `natToDigitBytes` encoding of a 3-digit-range `Nat` is exactly 3 bytes long -- proved
    by unfolding the encoder's own recursion twice (`n ≥ 100` forces two `n / 10` steps before
    the base case) rather than by strong induction, since the bound needed at each step differs. -/
theorem natToDigitBytes_length3 (n : Nat) (h1 : 100 ≤ n) (h2 : n ≤ 999) :
    (natToDigitBytes n).length = 3 := by
  unfold natToDigitBytes
  rw [dif_neg (show ¬ n < 10 from by omega)]
  simp only [List.length_append, List.length_cons, List.length_nil]
  unfold natToDigitBytes
  rw [dif_neg (show ¬ n / 10 < 10 from by omega)]
  simp only [List.length_append, List.length_cons, List.length_nil]
  unfold natToDigitBytes
  rw [dif_pos (show n / 10 / 10 < 10 from by omega)]
  simp

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
theorem natToDigitBytes_ne_sp (n : Nat) : ∀ b ∈ natToDigitBytes n, b ≠ SP := by
  intro b hb
  obtain ⟨hlo, hhi⟩ := natToDigitBytes_range n b hb
  exact (digit_ne_sp_htab hlo hhi).1

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
theorem writeStatusLine_ne_nil (code : Nat) (reason : List UInt8) :
    writeStatusLine code reason ≠ [] := by
  unfold writeStatusLine
  simp [httpVersionBytes]

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/-- `parseStatusLine` recovers exactly the status-code/reason-phrase `writeStatusLine` wrote --
    the reason-phrase is recovered by splitting only the *first two* spaces (see
    `Parser.lean`'s `parseStatusLine` docstring for why: unlike the request line, the third
    field here is deliberately allowed to contain further spaces). -/
theorem parseStatusLine_writeStatusLine (code : Nat) (reason : List UInt8)
    (hcr : 100 ≤ code ∧ code ≤ 599) (hrv : validFieldValue reason = true)
    (hro : noOwsEdges reason = true) :
    parseStatusLine (writeStatusLine code reason) = .ok (code, reason) := by
  have hshape : writeStatusLine code reason
      = httpVersionBytes ++ SP :: (natToDigitBytes code ++ SP :: reason) := by
    unfold writeStatusLine
    simp only [List.append_assoc, List.cons_append]
  have hs1 : splitFirstSpace (writeStatusLine code reason)
      = some (httpVersionBytes, natToDigitBytes code ++ SP :: reason) := by
    rw [hshape]
    exact splitFirstSpace_append _ httpVersionBytes (by decide)
  have hs2 : splitFirstSpace (natToDigitBytes code ++ SP :: reason)
      = some (natToDigitBytes code, reason) :=
    splitFirstSpace_append _ (natToDigitBytes code) (natToDigitBytes_ne_sp code)
  have hlen3 : (natToDigitBytes code).length = 3 :=
    natToDigitBytes_length3 code hcr.1 (by omega)
  unfold parseStatusLine
  simp only [hs1, hs2]
  simp only [hlen3, digitBytesToNat?_natToDigitBytes, hcr, hrv, hro, if_true, Bool.and_self]
  simp

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
theorem responseLines_ne_nil (resp : Response) : ∀ l ∈ responseLines resp, l ≠ [] := by
  intro l hl
  unfold responseLines at hl
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | ⟨h, _, rfl⟩) | rfl
  · exact writeStatusLine_ne_nil resp.statusCode resp.reason
  · exact writeHeaderLine_ne_nil h
  · exact writeContentLengthLine_ne_nil resp.body.length

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
theorem responseLines_no_crlf (resp : Response) :
    ∀ l ∈ responseLines resp, ∀ b ∈ l, b ≠ CR ∧ b ≠ LF := by
  intro l hl
  unfold responseLines at hl
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | ⟨h, hh, rfl⟩) | rfl
  · exact writeStatusLine_no_crlf resp.statusCode resp.reason resp.reasonOk.1
  · exact writeHeaderLine_no_crlf h (List.all_eq_true.mp resp.headersOk h hh)
  · exact writeContentLengthLine_no_crlf resp.body.length

/- REF: docs/STDLIB_HTTP11.md#3-parser-behavior -/
theorem peelLines_writeResponse (resp : Response) :
    peelLines (writeResponse resp) = some (responseLines resp, resp.body) := by
  unfold writeResponse
  exact peelLines_append resp.body (responseLines resp)
    (responseLines_ne_nil resp) (responseLines_no_crlf resp)

/- REF: docs/STDLIB_HTTP11.md#51-write-then-parse-roundtrip-theorems -/
/-- **Write-then-parse round trip, responses.** See `request_roundtrip`; identical shape and
    argument, with the status line in place of the request line. -/
theorem response_roundtrip (resp : Response) :
    parseResponse (writeResponse resp) = .ok resp := by
  have hpeel := peelLines_writeResponse resp
  have hheadersOkEach : ∀ h ∈ resp.headers, headerFieldOk h = true :=
    fun h hh => List.all_eq_true.mp resp.headersOk h hh
  have hCLbytes : writeContentLengthLine resp.body.length
      = writeHeaderLine (contentLengthBytes, natToDigitBytes resp.body.length) := rfl
  have hparseHdrs : parseHeaderLines (resp.headers.map writeHeaderLine ++
      [writeContentLengthLine resp.body.length])
      = .ok (resp.headers ++ [(contentLengthBytes, natToDigitBytes resp.body.length)]) := by
    rw [hCLbytes]
    exact parseHeaderLines_map_append resp.headers _ hheadersOkEach
      (parseHeaderLine_writeContentLengthLine resp.body.length)
  have hCLexclude : ∀ h ∈ resp.headers, isContentLengthName h.1 = false := by
    intro h hh
    have hok := hheadersOkEach h hh
    unfold headerFieldOk at hok
    simp only [Bool.and_eq_true] at hok
    simpa using hok.2
  have hextract := extractContentLength_append resp.headers resp.body.length hCLexclude
  have hstatus := parseStatusLine_writeStatusLine resp.statusCode resp.reason
    resp.statusRange resp.reasonOk.1 resp.reasonOk.2
  unfold parseResponse
  rw [hpeel]
  unfold responseLines
  rw [show ([writeStatusLine resp.statusCode resp.reason] ++ resp.headers.map writeHeaderLine ++
      [writeContentLengthLine resp.body.length] : List (List UInt8)) =
      writeStatusLine resp.statusCode resp.reason :: (resp.headers.map writeHeaderLine ++
      [writeContentLengthLine resp.body.length]) from rfl]
  simp only [hstatus, hparseHdrs, hextract]
  simp only [ne_eq, not_true_eq_false, if_false, resp.statusRange, resp.reasonOk, resp.headersOk]
  simp

/- REF: docs/STDLIB_HTTP11.md#52-parse-reencode-stability-theorems -/
/-- **Parse-reencode stability, responses.** See `request_parse_reencode_stable`; identical
    shape and argument. -/
theorem response_parse_reencode_stable (b : List UInt8) (r1 r2 : Response)
    (_h1 : parseResponse b = .ok r1) (h2 : parseResponse (writeResponse r1) = .ok r2) :
    r1 = r2 := by
  rw [response_roundtrip r1] at h2
  exact Except.ok.inj h2

end Stdlib.Http11

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

import Stdlib.Http11.Basic

/-
## Stdlib.Http11.Types

The structured, proof-carrying `Request`/`Response` types this library's parser produces and
its writer consumes, plus the shared, decidable well-formedness predicates both the parser and
the round-trip proof (`Stdlib/Http11/Roundtrip.lean`) reduce to. `Request`/`Response` bundle a
single `wf`-style proof field per proof-carrying invariant (target validity, header
well-formedness, status-code range, reason-phrase validity) rather than using subtypes for
each byte-list field individually: this keeps field access plain (`r.target : List UInt8`, not
`r.target.val`) and, since Lean's proof terms are subject to definitional proof irrelevance,
makes two `Request`/`Response` values with the same non-proof fields *definitionally* equal --
exactly what `Roundtrip.lean`'s "reconstructed value equals the original" step needs.

See `docs/STDLIB_HTTP11.md#11-what-this-library-models` for why these particular invariants
(and no others -- no `Transfer-Encoding`, no absolute-form targets, etc.) are the ones this
library enforces.
-/

namespace Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- The nine registered HTTP methods this library's request grammar supports -- closed so the
    round-trip theorem needs no open-ended token grammar for it. -/
inductive Method
  | GET | HEAD | POST | PUT | DELETE | CONNECT | OPTIONS | TRACE | PATCH
  deriving DecidableEq, Repr, BEq

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- The exact wire bytes for each method token. -/
def Method.toBytes : Method → List UInt8
  | .GET => [0x47, 0x45, 0x54]
  | .HEAD => [0x48, 0x45, 0x41, 0x44]
  | .POST => [0x50, 0x4F, 0x53, 0x54]
  | .PUT => [0x50, 0x55, 0x54]
  | .DELETE => [0x44, 0x45, 0x4C, 0x45, 0x54, 0x45]
  | .CONNECT => [0x43, 0x4F, 0x4E, 0x4E, 0x45, 0x43, 0x54]
  | .OPTIONS => [0x4F, 0x50, 0x54, 0x49, 0x4F, 0x4E, 0x53]
  | .TRACE => [0x54, 0x52, 0x41, 0x43, 0x45]
  | .PATCH => [0x50, 0x41, 0x54, 0x43, 0x48]

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- Decodes a method token by exact literal match against the nine known method byte strings;
    `none` for anything else (a registration-extensible method is out of this library's closed
    `Method` grammar, `docs/STDLIB_HTTP11.md#12-deliberate-omissions`). -/
def Method.ofBytes? (bs : List UInt8) : Option Method :=
  if bs = Method.GET.toBytes then some .GET
  else if bs = Method.HEAD.toBytes then some .HEAD
  else if bs = Method.POST.toBytes then some .POST
  else if bs = Method.PUT.toBytes then some .PUT
  else if bs = Method.DELETE.toBytes then some .DELETE
  else if bs = Method.CONNECT.toBytes then some .CONNECT
  else if bs = Method.OPTIONS.toBytes then some .OPTIONS
  else if bs = Method.TRACE.toBytes then some .TRACE
  else if bs = Method.PATCH.toBytes then some .PATCH
  else none

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- Round-trip for the (finite, 9-element) method grammar: decoding what `toBytes` wrote
    always recovers the same method. Proved by exhaustive case split -- `Method` is closed. -/
theorem Method.ofBytes?_toBytes (m : Method) : Method.ofBytes? m.toBytes = some m := by
  cases m <;> decide

/- REF: docs/STDLIB_HTTP11.md#24-token-and-field-value-character-classes -/
/-- Every method token is a valid `tchar` token -- needed so a method's wire bytes never
    themselves contain the SP that delimits the request line's fields. -/
theorem Method.toBytes_validToken (m : Method) : validToken m.toBytes = true := by
  cases m <;> decide

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- The literal wire bytes for the one HTTP version this library supports. -/
def httpVersionBytes : List UInt8 :=
  [0x48, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31]

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- The literal, already-lowercase wire bytes for the `Content-Length` header name, used only
    for the case-insensitive comparison `isContentLengthName` performs. -/
def contentLengthBytes : List UInt8 :=
  [0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68]

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Maps an ASCII upper-case letter to its lower-case form; every other byte is unchanged. -/
def toLowerByte (b : UInt8) : UInt8 :=
  if b ≥ 0x41 && b ≤ 0x5A then b + 0x20 else b

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
def toLowerBytes (bs : List UInt8) : List UInt8 :=
  bs.map toLowerByte

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Case-insensitive test for whether `name` is the header name `Content-Length` -- the one
    header this library always synthesizes itself and never accepts as caller-supplied, so
    there is exactly one source of truth for the body length. -/
def isContentLengthName (name : List UInt8) : Bool :=
  toLowerBytes name == contentLengthBytes

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- A single header field is well-formed: a valid `tchar` name, a value with no leading/
    trailing OWS whose every byte is a field-value byte, and a name that is not (case-
    insensitively) `Content-Length` -- that header is always writer-synthesized, never
    caller-supplied, `docs/STDLIB_HTTP11.md#25-message-body-and-content-length`. -/
def headerFieldOk (h : List UInt8 × List UInt8) : Bool :=
  validToken h.1 && validFieldValue h.2 && noOwsEdges h.2 && !isContentLengthName h.1

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
def headersWellFormed (headers : List (List UInt8 × List UInt8)) : Bool :=
  headers.all headerFieldOk

/- REF: docs/STDLIB_HTTP11.md#1-overview--scope -/
/-- A structured, proof-carrying HTTP/1.1 request: an origin-form `target` (`targetOk`), and a
    header list excluding `Content-Length` and satisfying the token/field-value grammar
    (`headersOk`). `body`'s length is always the writer-synthesized `Content-Length` value --
    see `Writer.lean`. -/
structure Request where
  method    : Method
  target    : List UInt8
  headers   : List (List UInt8 × List UInt8)
  body      : List UInt8
  targetOk  : validTarget target = true
  headersOk : headersWellFormed headers = true

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/-- A structured, proof-carrying HTTP/1.1 response: a three-digit `statusCode` in `100..599`
    (`statusRange`), a `reason` phrase with no leading/trailing OWS whose every byte is a
    field-value byte (`reasonOk`), and a header list excluding `Content-Length` and satisfying
    the token/field-value grammar (`headersOk`). -/
structure Response where
  statusCode  : Nat
  statusRange : 100 ≤ statusCode ∧ statusCode ≤ 599
  reason      : List UInt8
  reasonOk    : validFieldValue reason = true ∧ noOwsEdges reason = true
  headers     : List (List UInt8 × List UInt8)
  headersOk   : headersWellFormed headers = true
  body        : List UInt8

end Stdlib.Http11

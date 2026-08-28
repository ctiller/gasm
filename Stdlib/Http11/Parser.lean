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

import Stdlib.Http11.Types

/-
## Stdlib.Http11.Parser

`parseRequest`/`parseResponse : List UInt8 → Except Error _` -- total (no `partial def`
anywhere in this file: every function is either plain structural recursion or, where it calls
into `Basic.lean`'s `peelLines`, well-founded recursion with an explicit termination measure)
and rejects everything RFC 9112 forbids that this library's scope covers
(`docs/STDLIB_HTTP11.md#31-error-taxonomy`, `docs/STDLIB_HTTP11.md#32-rejected-input`) rather
than hanging or silently accepting malformed input. Every place this parser constructs a
`Request`/`Response` value does so via a dependent `if h : P then ... else ...` on exactly the
`Bool` predicate the target structure's proof field demands, so the constructed value's
`targetOk`/`headersOk`/etc. fields are literally the `h` the branch condition just produced --
no separate re-derivation of those facts is needed once the parser is written this way.
-/

namespace Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Splits a request-line/status-line into exactly three space-separated fields, or `none` if
    there are fewer (a missing field) or more (a fourth field left inside what would become
    the third) than three. -/
def splitThreeFields (bs : List UInt8) : Option (List UInt8 × List UInt8 × List UInt8) :=
  match splitFirstSpace bs with
  | none => none
  | some (first, rest1) =>
      match splitFirstSpace rest1 with
      | none => none
      | some (second, third) =>
          if (splitFirstSpace third).isSome then none else some (first, second, third)

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Parses one request line: `method SP target SP "HTTP/1.1"`. -/
def parseRequestLine (line : List UInt8) : Except Error (Method × List UInt8) :=
  match splitThreeFields line with
  | none => .error .malformedRequestLine
  | some (methodBytes, target, version) =>
      match Method.ofBytes? methodBytes with
      | none => .error .unknownMethod
      | some m =>
          if validTarget target then
            if version = httpVersionBytes then .ok (m, target)
            else .error .unsupportedVersion
          else .error .invalidTarget

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/-- Parses one status line: `"HTTP/1.1" SP status-code SP reason-phrase`. `status-code` must
    be exactly three decimal digits decoding (via `digitBytesToNat?`) to a value in
    `100..599`. -/
def parseStatusLine (line : List UInt8) : Except Error (Nat × List UInt8) :=
  match splitThreeFields line with
  | none => .error .malformedStatusLine
  | some (version, codeBytes, reason) =>
      if version = httpVersionBytes then
        if codeBytes.length = 3 then
          match digitBytesToNat? codeBytes with
          | none => .error .invalidStatusCode
          | some n =>
              if 100 ≤ n ∧ n ≤ 599 then
                if validFieldValue reason && noOwsEdges reason then .ok (n, reason)
                else .error .invalidReasonPhrase
              else .error .invalidStatusCode
        else .error .invalidStatusCode
      else .error .unsupportedVersion

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- Parses one header line: `field-name ":" SP field-value`, `field-value` free of leading/
    trailing OWS. -/
def parseHeaderLine (line : List UInt8) : Except Error (List UInt8 × List UInt8) :=
  match splitHeaderLine line with
  | none => .error .malformedHeaderLine
  | some (name, value) =>
      if validToken name then
        if validFieldValue value && noOwsEdges value then .ok (name, value)
        else .error .invalidHeaderValue
      else .error .invalidHeaderName

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- Parses every header line independently, in order (no list folding, no combining of
    repeated field names, `docs/STDLIB_HTTP11.md#23-header-fields`). Structurally recursive on
    the (already `peelLines`-split) list of lines. -/
def parseHeaderLines : List (List UInt8) → Except Error (List (List UInt8 × List UInt8))
  | [] => .ok []
  | l :: ls =>
      match parseHeaderLine l with
      | .error e => .error e
      | .ok h =>
          match parseHeaderLines ls with
          | .error e => .error e
          | .ok rest => .ok (h :: rest)

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- Extracts the required, exactly-one `Content-Length` header (case-insensitive name match)
    from an already-parsed header list, returning its decoded value and every other header in
    their original relative order. -/
def extractContentLength (headers : List (List UInt8 × List UInt8)) :
    Except Error (Nat × List (List UInt8 × List UInt8)) :=
  match headers.filter (fun h => isContentLengthName h.1) with
  | [] => .error .missingContentLength
  | [clHeader] =>
      match digitBytesToNat? clHeader.2 with
      | none => .error .malformedContentLength
      | some n => .ok (n, headers.filter (fun h => !isContentLengthName h.1))
  | _ :: _ :: _ => .error .duplicateContentLength

/- REF: docs/STDLIB_HTTP11.md#3-parser-behavior -/
/-- Parses a complete HTTP/1.1 request: `peelLines` splits the request line and header lines
    from the body at the header-section terminator (`none` here means no `CR LF CR LF` blank
    line was found anywhere -- `Error.headersNotTerminated`, including a request truncated
    mid-headers); the request line, each header line, and the `Content-Length`-declared body
    length are then each validated independently. Total: every branch is a plain `match`/`if`,
    no recursion beyond what `peelLines`/`parseHeaderLines` already do, so this terminates on
    every input, well-formed or adversarial. -/
def parseRequest (bs : List UInt8) : Except Error Request :=
  match peelLines bs with
  | none => .error .headersNotTerminated
  | some ([], _) => .error .malformedRequestLine
  | some (reqLine :: hdrLines, body) =>
      match parseRequestLine reqLine with
      | .error e => .error e
      | .ok (m, target) =>
          match parseHeaderLines hdrLines with
          | .error e => .error e
          | .ok headers =>
              match extractContentLength headers with
              | .error e => .error e
              | .ok (n, otherHeaders) =>
                  if body.length ≠ n then .error .bodyLengthMismatch
                  else if ht : validTarget target then
                    if hh : headersWellFormed otherHeaders then
                      .ok { method := m, target := target, headers := otherHeaders,
                            body := body, targetOk := ht, headersOk := hh }
                    else .error .invalidHeaderName
                  else .error .invalidTarget

/- REF: docs/STDLIB_HTTP11.md#3-parser-behavior -/
/-- Parses a complete HTTP/1.1 response; see `parseRequest` for the shared header-section/
    `Content-Length` handling this mirrors. -/
def parseResponse (bs : List UInt8) : Except Error Response :=
  match peelLines bs with
  | none => .error .headersNotTerminated
  | some ([], _) => .error .malformedStatusLine
  | some (statusLine :: hdrLines, body) =>
      match parseStatusLine statusLine with
      | .error e => .error e
      | .ok (code, reason) =>
          match parseHeaderLines hdrLines with
          | .error e => .error e
          | .ok headers =>
              match extractContentLength headers with
              | .error e => .error e
              | .ok (n, otherHeaders) =>
                  if body.length ≠ n then .error .bodyLengthMismatch
                  else if hr : 100 ≤ code ∧ code ≤ 599 then
                    if hro : validFieldValue reason = true ∧ noOwsEdges reason = true then
                      if hh : headersWellFormed otherHeaders then
                        .ok { statusCode := code, statusRange := hr, reason := reason,
                              reasonOk := hro, headers := otherHeaders, body := body,
                              headersOk := hh }
                      else .error .invalidHeaderName
                    else .error .invalidReasonPhrase
                  else .error .invalidStatusCode

end Stdlib.Http11

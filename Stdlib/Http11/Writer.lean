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
## Stdlib.Http11.Writer

The canonical byte writer: `writeRequest`/`writeResponse` produce exactly one deterministic
byte string per structured value (`docs/STDLIB_HTTP11.md#4-writer--canonical-serialization`).
`requestLines`/`responseLines` expose the writer's own line decomposition (request/status line,
each header line in list order, the synthesized `Content-Length` line) *before* CRLF-joining --
`Roundtrip.lean`'s proof that `parseRequest (writeRequest r) = .ok r` applies
`Basic.peelLines_append` directly to this list, rather than re-deriving the decomposition from
the joined byte string.
-/

namespace Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- `method SP target SP "HTTP/1.1"`, unterminated (the request line's content, not yet
    `CR LF`-joined -- see `requestLines`). -/
def writeRequestLine (m : Method) (target : List UInt8) : List UInt8 :=
  m.toBytes ++ SP :: target ++ SP :: httpVersionBytes

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/-- `"HTTP/1.1" SP status-code SP reason-phrase`, unterminated. -/
def writeStatusLine (statusCode : Nat) (reason : List UInt8) : List UInt8 :=
  httpVersionBytes ++ SP :: natToDigitBytes statusCode ++ SP :: reason

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
/-- `name ":" SP value`, unterminated. -/
def writeHeaderLine (h : List UInt8 × List UInt8) : List UInt8 :=
  h.1 ++ COLON :: SP :: h.2

/- REF: docs/STDLIB_HTTP11.md#25-message-body-and-content-length -/
/-- `"Content-Length:" SP <decimal digits of n>`, unterminated -- the one header this library
    always synthesizes itself from `body.length`, never accepting it as a caller-supplied
    ordinary header (`docs/STDLIB_HTTP11.md#25-message-body-and-content-length`). -/
def writeContentLengthLine (n : Nat) : List UInt8 :=
  contentLengthBytes ++ COLON :: SP :: natToDigitBytes n

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
/-- The request's lines in wire order, each still unterminated: the request line, each header
    in list order, then the synthesized `Content-Length` line. -/
def requestLines (r : Request) : List (List UInt8) :=
  [writeRequestLine r.method r.target] ++ r.headers.map writeHeaderLine ++
    [writeContentLengthLine r.body.length]

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
/-- The response's lines in wire order, each still unterminated: the status line, each header
    in list order, then the synthesized `Content-Length` line. -/
def responseLines (resp : Response) : List (List UInt8) :=
  [writeStatusLine resp.statusCode resp.reason] ++ resp.headers.map writeHeaderLine ++
    [writeContentLengthLine resp.body.length]

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
/-- The canonical wire bytes for `r`: `requestLines r`, each `CR LF`-terminated, followed by
    the header-section terminator (a blank `CR LF` line) and the body bytes verbatim. -/
def writeRequest (r : Request) : List UInt8 :=
  ((requestLines r).map (· ++ [CR, LF])).flatten ++ CR :: LF :: r.body

/- REF: docs/STDLIB_HTTP11.md#4-writer--canonical-serialization -/
/-- The canonical wire bytes for `resp`: `responseLines resp`, each `CR LF`-terminated,
    followed by the header-section terminator and the body bytes verbatim. -/
def writeResponse (resp : Response) : List UInt8 :=
  ((responseLines resp).map (· ++ [CR, LF])).flatten ++ CR :: LF :: resp.body

end Stdlib.Http11

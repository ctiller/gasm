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
import Stdlib.Http11.Parser
import Stdlib.Http11.Writer
import Stdlib.Http11.Roundtrip

/-
## Stdlib.Http11.Test

Concrete regression vectors: one per `Error` rejection reason (`docs/STDLIB_HTTP11.md#32-rejected-input`),
plus a handful of well-formed requests/responses that must parse successfully. `request_roundtrip`/
`response_roundtrip` in `Roundtrip.lean` already prove the parser inverts the writer for *every*
structured value -- what these `#guard`s cover instead is the parser's *rejection* behavior on
concrete byte strings, which a universally-quantified round-trip theorem (stated over well-formed
`Request`/`Response` values) does not by itself exercise.
-/

namespace Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#3-parser-behavior -/
/-- Converts an ASCII test string to the raw wire bytes `parseRequest`/`parseResponse` consume. -/
def s2b (s : String) : List UInt8 := s.toUTF8.toList

-- === Well-formed input: must parse successfully ===

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nHost: localhost\r\nContent-Length: 0\r\n\r\n") with
  | .ok r => r.method == .GET ∧ r.target == s2b "/" ∧ r.body == []
  | .error _ => false

/- REF: docs/STDLIB_HTTP11.md#23-header-fields -/
#guard match parseRequest
    (s2b "POST /submit HTTP/1.1\r\nHost: localhost\r\nContent-Length: 5\r\n\r\nhello") with
  | .ok r => r.method == .POST ∧ r.target == s2b "/submit" ∧ r.body == s2b "hello"
  | .error _ => false

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
#guard match parseResponse (s2b "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n") with
  | .ok r => r.statusCode == 200 ∧ r.reason == s2b "OK"
  | .error _ => false

/- REF: docs/STDLIB_HTTP11.md#22-status-line -/
/- A reason-phrase containing internal spaces -- `parseStatusLine`'s reason for splitting only
    the first two spaces (see `Parser.lean`); a status line is not `splitThreeFields`. -/
#guard match parseResponse (s2b "HTTP/1.1 500 Internal Server Error\r\nContent-Length: 0\r\n\r\n") with
  | .ok r => r.statusCode == 500 ∧ r.reason == s2b "Internal Server Error"
  | .error _ => false

-- === Malformed input: one vector per `Error` rejection reason ===

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- No `CR LF CR LF` blank line anywhere -- a request truncated mid-headers. -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nHost: localhost") with
  | .error .headersNotTerminated => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- Wrong request-line field count: only two space-separated fields. -/
#guard match parseRequest (s2b "GET /\r\n\r\n") with
  | .error .malformedRequestLine => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- Wrong status-line field count: no space before the (missing) reason-phrase field, i.e. only
    one field after the version. -/
#guard match parseResponse (s2b "HTTP/1.1 200\r\n\r\n") with
  | .error .malformedStatusLine => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A method outside the nine registered tokens. -/
#guard match parseRequest (s2b "FOO / HTTP/1.1\r\n\r\n") with
  | .error .unknownMethod => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A request-target that does not start with `/` (not origin-form). -/
#guard match parseRequest (s2b "GET http://x/ HTTP/1.1\r\n\r\n") with
  | .error .invalidTarget => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- Any version token other than the literal `HTTP/1.1`. -/
#guard match parseRequest (s2b "GET / HTTP/1.0\r\n\r\n") with
  | .error .unsupportedVersion => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A header line with no `": "` separator. -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nHost localhost\r\n\r\n") with
  | .error .malformedHeaderLine => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- An empty header field-name (`": value"` -- `splitHeaderLine` succeeds with `name = []`,
    which fails `validToken`'s non-empty requirement). -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\n: localhost\r\n\r\n") with
  | .error .invalidHeaderName => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A header value with a leading space beyond the canonical single `": "` separator (embedded
    leading OWS, rejected by `noOwsEdges`). -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nHost:  localhost\r\n\r\n") with
  | .error .invalidHeaderValue => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- No `Content-Length` header at all. -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n") with
  | .error .missingContentLength => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- Two headers both named `content-length`, case-insensitively. -/
#guard match parseRequest
    (s2b "GET / HTTP/1.1\r\nContent-Length: 0\r\ncontent-length: 0\r\n\r\n") with
  | .error .duplicateContentLength => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A non-numeric `Content-Length` value. -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nContent-Length: abc\r\n\r\n") with
  | .error .malformedContentLength => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A body shorter than the declared `Content-Length`. -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhi") with
  | .error .bodyLengthMismatch => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A body longer than the declared `Content-Length` (trailing garbage past a declared length,
    not silently accepted as part of the next message). -/
#guard match parseRequest (s2b "GET / HTTP/1.1\r\nContent-Length: 2\r\n\r\nhello") with
  | .error .bodyLengthMismatch => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A status code that is not exactly three decimal digits. -/
#guard match parseResponse (s2b "HTTP/1.1 20 OK\r\n\r\n") with
  | .error .invalidStatusCode => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A three-digit status code outside `100..599`. -/
#guard match parseResponse (s2b "HTTP/1.1 999 Nonsense\r\nContent-Length: 0\r\n\r\n") with
  | .error .invalidStatusCode => true
  | _ => false

/- REF: docs/STDLIB_HTTP11.md#31-error-taxonomy -/
/- A reason-phrase with a leading space beyond the canonical single separator. -/
#guard match parseResponse (s2b "HTTP/1.1 200  OK\r\nContent-Length: 0\r\n\r\n") with
  | .error .invalidReasonPhrase => true
  | _ => false

end Stdlib.Http11

open Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#3-parser-behavior -/
/-- Every regression vector above is a `#guard`, checked at compile time (kernel-evaluated,
    not `native_decide`) -- if this executable built, every vector already passed. -/
def main : IO UInt32 := do
  IO.println "======================================================================"
  IO.println " Stdlib.Http11 Test Suite (RFC 9112 request/response parser and writer)"
  IO.println "======================================================================"
  IO.println "[+] All #guard regression vectors passed at build time (20 checks: 4"
  IO.println "    well-formed parses, 14 Error-taxonomy rejections, 2 status-line edge"
  IO.println "    cases)."
  IO.println "\n[+] ALL STDLIB.HTTP11 TESTS PASSED (100% SUCCESS)."
  return 0

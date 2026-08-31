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
import Gasm.Core.Types
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.Network
import Gasm.Effects.Trace
import Stdlib.Http11.Parser

namespace Spikes.Spike4HttpServer

open Gasm.Core
open Gasm.Effects

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- High-Level HTTP 1.1 Request model. -/
structure HttpRequest where
  method  : String
  path    : String
  version : String
  deriving Repr, DecidableEq

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- High-Level HTTP 1.1 Response model. -/
structure HttpResponse where
  statusCode  : UInt32
  statusText  : String
  contentType : String
  body        : String
  deriving Repr, DecidableEq

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- Bridges `Stdlib.Http11.Method` (a closed 9-constructor enum) back to this spike's
    `String`-typed model. -/
def methodToString : Stdlib.Http11.Method → String
  | .GET => "GET" | .HEAD => "HEAD" | .POST => "POST" | .PUT => "PUT"
  | .DELETE => "DELETE" | .CONNECT => "CONNECT" | .OPTIONS => "OPTIONS"
  | .TRACE => "TRACE" | .PATCH => "PATCH"

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- The request *line* of a raw request: the bytes up to the first `CR LF`, or the whole byte
    string when there is none. Split with `Stdlib.Http11.takeLine` -- a byte-level, *structurally*
    recursive scan -- rather than `String.splitOn "\r\n" |>.head?`, and reaching the bytes via
    `Gasm.Effects.toByteList` rather than `ByteArray.toList`. Both choices are F1 requirements,
    for two independent reasons:
      * **Domain (the Law 9 reason).** This is defined on every `ByteArray`, including byte
        strings no Lean `String` can hold. `∀ (request : ByteArray)` needs a parser whose domain
        is actually `ByteArray`.
      * **Reducibility.** `String.splitOn` bottoms out in `splitOnAux` and `ByteArray.toList` in
        `toList.loop`, both `@[irreducible]` well-founded recursions that do not reduce in the
        kernel -- Spike 4 reduction blockers 2 and 1 respectively (`docs/TRUST_PLAN.md`).
        `takeLine`, `List.range` and `List.map` all reduce.
    The `none` fallback matches `splitOn "\r\n" |>.head?` exactly on an unterminated request, so
    no existing vector's verdict changes. -/
def requestLineBytes (req : ByteArray) : List UInt8 :=
  let bs := toByteList req
  match Stdlib.Http11.takeLine bs with
  | some (line, _) => line
  | none => bs

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Pure functional HTTP 1.1 Request-Line Parser, **over raw request bytes** (F1). Delegates
    field-splitting to `Stdlib.Http11.parseRequestLine` (`Stdlib/Http11/Parser.lean`) -- the proven
    library `docs/STDLIB_HTTP11.md#1-overview-scope`'s routing defect motivated -- rather than
    re-implementing ad-hoc splitting here. Only the request-*line*-level parser is used (not the
    full `parseRequest`, which additionally requires a `Content-Length` header and an exact-length
    body neither this spike's request vectors nor its wire format carry); this function only ever
    needed the first line. It rejects a method outside the closed 9-method grammar, a
    non-origin-form target, or a version other than the literal `HTTP/1.1`.

    F1 changed only the *domain*: `ByteArray` in place of `String`. `Stdlib.Http11.parseRequestLine`
    was already byte-typed, so this removes a `String` round trip rather than adding one -- the
    pre-F1 body read `reqLine.toUTF8.toList`, encoding back to the bytes it had just decoded from.
    Behaviour is identical on every request vector this spike exercises (checked: same
    method/target/version for every well-formed request line in Test.lean and Equivalence.lean,
    including every `N8` route-fix witness path and every `spike4GeneralClaimCounterexamples`
    witness). -/
def parseRequestLine (req : ByteArray) : Option HttpRequest :=
  match Stdlib.Http11.parseRequestLine (requestLineBytes req) with
  | .error _ => none
  | .ok (m, target) =>
      some { method := methodToString m, path := String.fromUTF8! (ByteArray.mk target.toArray),
             version := "HTTP/1.1" }

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Pure HTTP 1.1 Route Dispatcher. -/
def routeRequest (req : HttpRequest) : HttpResponse :=
  if req.path == "/" then
    { statusCode := 200, statusText := "OK", contentType := "text/plain", body := "Hello from gasm HTTP 1.1 server!\r\n" }
  else if req.path == "/status" then
    { statusCode := 200, statusText := "OK", contentType := "application/json", body := "{\"status\":\"healthy\",\"engine\":\"gasm\"}\r\n" }
  else
    { statusCode := 404, statusText := "Not Found", contentType := "text/plain", body := "404 Not Found\r\n" }

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Formats an HTTP response into RFC 9112 compliant wire string. -/
def formatResponse (res : HttpResponse) : String :=
  s!"HTTP/1.1 {res.statusCode} {res.statusText}\r\nContent-Type: {res.contentType}\r\nContent-Length: {res.body.length}\r\nConnection: close\r\n\r\n{res.body}"

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- The single 400 Bad Request response this spike's model emits for every request line
    `parseRequestLine` rejects. Named (rather than spelled inline in `handleRawRequest`) so the
    three lowerings can build their `.rdata`/data-segment copy of these exact bytes *from the model*
    rather than re-spelling the record and risking drift -- the same discipline
    `respRootBytes`/`respStatusBytes` already follow for the 200 responses. -/
def badRequestResponse : HttpResponse :=
  { statusCode := 400, statusText := "Bad Request", contentType := "text/plain", body := "400 Bad Request\r\n" }

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- End-to-end Pure Functional HTTP Request Handler, over raw request bytes (F1). -/
def handleRawRequest (rawReq : ByteArray) : String :=
  match parseRequestLine rawReq with
  | some req => formatResponse (routeRequest req)
  | none => formatResponse badRequestResponse

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- Monadic HTTP Server Loop Specification parameterized over Network effect capabilities. -/
def httpServerMonadic (m : Type → Type) [Monad m] [MonadNetwork m] (port : UInt16 := 8080) (requestCount : Nat := 1) : m Unit := do
  let some serverSock ← MonadNetwork.listen port | return ()
  for _ in [0:requestCount] do
    let some clientConn ← MonadNetwork.accept serverSock | break
    let some rawReq ← MonadNetwork.recv clientConn 1024 | do
      MonadNetwork.close clientConn
      break
    let respStr := handleRawRequest rawReq
    let _ ← MonadNetwork.send clientConn respStr
    MonadNetwork.close clientConn

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- High-level model trace for an **arbitrary request byte string** (F1). This is the function
    the general claim quantifies over; before F1 its argument was `String`, so the general claim
    could not even be typed. -/
def serverModelTraceFor (req : ByteArray) : List AnyEvent :=
  runModelTrace (httpServerMonadic (TraceM AnyEvent) 8080 1) [] [req]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- A request vector written as source text. Every request literal in this spike goes through
    here rather than being spelled as a bare `String`, so the queue's element type is `ByteArray`
    at every call site while the vectors stay readable. Note this is a *convenience for writing
    ASCII vectors*, not a restriction on the domain: `serverModelTraceFor` and the three
    `loadWithRequests` loaders accept any `ByteArray`, including ones no `String` can express. -/
def req (s : String) : ByteArray := s.toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- Canonical high-level model trace for HTTP GET / request. -/
def canonicalServerTrace : List AnyEvent :=
  serverModelTraceFor (req "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n")

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- Canonical high-level model trace for HTTP GET /status request. -/
def canonicalStatusServerTrace : List AnyEvent :=
  serverModelTraceFor (req "GET /status HTTP/1.1\r\nHost: localhost\r\n\r\n")

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- Canonical high-level model trace for HTTP 404 request. -/
def canonical404ServerTrace : List AnyEvent :=
  serverModelTraceFor (req "GET /unknown HTTP/1.1\r\nHost: localhost\r\n\r\n")

/-!
## Lowering support: the method-token dispatch table

All three Spike 4 lowerings used to assume, with no check whatsoever, that the four bytes at the
start of a received request were literally `"GET "`, and read the path window at the fixed offset 4.
That made every target answer 200 OK to `"FOO / HTTP/1.1..."` where `parseRequestLine` above
(delegating to `Stdlib.Http11.parseRequestLine`) answers 400 Bad Request, and simultaneously
mis-read the path of every *valid* request whose method is not exactly three characters long
(`HEAD`, `POST`, `DELETE`, `CONNECT`, `OPTIONS`, `TRACE`, `PATCH` -- the model routes purely on the
path, so `"POST / HTTP/1.1"` must get the same 200 root response `"GET / HTTP/1.1"` does).

The definitions below are the bridge the lowerings dispatch from. They are **derived from
`Stdlib.Http11.Method.toBytes`**, the same wire-token function the proven parser itself uses, rather
than hand-transcribed into each target -- so the assembly and the model cannot disagree about which
method tokens exist or how they spell. What the lowerings do *not* do is embed the whole parser:
they recognise the method token and locate the path from it, and nothing more. The remaining
request-line obligations `Stdlib.Http11.parseRequestLine` enforces -- exactly three SP-separated
fields, an origin-form target, a literal `HTTP/1.1` version -- stay unimplemented in the assembly,
which is why `Spikes/Spike4HttpServer/Equivalence.lean`'s surviving falsity witnesses
(`witnessVersionNotValidatedDivergence` and its siblings) are recorded there as checked
counterexamples rather than quietly excluded from a narrowed claim.
-/

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- The nine method tokens `Stdlib.Http11.Method` admits, in declaration order.
    `mem_allHttpMethods` immediately below is the structural proof that this list is exhaustive, so
    a lowering generated from it cannot silently omit a method. -/
def allHttpMethods : List Stdlib.Http11.Method :=
  [.GET, .HEAD, .POST, .PUT, .DELETE, .CONNECT, .OPTIONS, .TRACE, .PATCH]

/- REF: docs/STDLIB_HTTP11.md#11-what-this-library-models -/
/-- `allHttpMethods` really does list every constructor of `Stdlib.Http11.Method`. Structural
    (`cases` + `simp`), so it needs neither `decide` nor `native_decide`
    (`docs/REVIEW.md` Law 10, rung 1); if the enum gains a constructor this proof breaks rather
    than the lowering silently under-approximating the model. -/
theorem mem_allHttpMethods (m : Stdlib.Http11.Method) : m ∈ allHttpMethods := by
  cases m <;> simp [allHttpMethods]

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- A method's wire token followed by the request line's mandatory delimiting SP -- exactly the
    prefix a well-formed request line starts with. -/
def methodTokenBytes (m : Stdlib.Http11.Method) : List UInt8 :=
  m.toBytes ++ [0x20]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- `methodTokenBytes m` packed into one little-endian 64-bit word, matching how both an x86-64
    `mov r64, [mem]` and a Wasm `i64.load` see those bytes. Every token is at most 8 bytes
    (`CONNECT `/`OPTIONS ` are exactly 8), so no token is truncated. -/
def methodTokenWord (m : Stdlib.Http11.Method) : UInt64 :=
  (methodTokenBytes m).foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- The byte mask selecting exactly the `methodTokenBytes m` bytes out of such a 64-bit load, so a
    shorter token is compared against only its own bytes and not whatever follows it in the buffer. -/
def methodTokenMask (m : Stdlib.Http11.Method) : UInt64 :=
  (methodTokenBytes m).foldr (fun _ acc => (acc <<< 8) ||| 0xFF) 0

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Where the request target begins, given the method: immediately after the token and its SP. -/
def methodPathOffset (m : Stdlib.Http11.Method) : Nat :=
  (methodTokenBytes m).length

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- The distinct path offsets the nine methods produce (4, 5, 6, 7, 8) -- the lowerings emit one
    path-window-setup block per distinct offset rather than one per method. -/
def methodPathOffsets : List Nat :=
  (allHttpMethods.map methodPathOffset).eraseDups

end Spikes.Spike4HttpServer

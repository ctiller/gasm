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
/-- Pure functional HTTP 1.1 Request-Line Parser. Delegates field-splitting to
    `Stdlib.Http11.parseRequestLine` (`Stdlib/Http11/Parser.lean`) -- the proven library
    `docs/STDLIB_HTTP11.md#1-overview--scope`'s routing defect motivated -- rather than
    re-implementing ad-hoc string splitting here. Only the request-*line*-level parser is used
    (not the full `parseRequest`, which additionally requires a `Content-Length` header and an
    exact-length body neither this spike's request vectors nor its wire format carry); this
    function only ever needed the first line. Behavior is identical to the prior hand-rolled
    version on every existing request vector (verified: same method/target/version for every
    well-formed 3-field `GET` request line this spike's Test.lean/Equivalence.lean exercise,
    including every `N8` route-fix witness path), while now also rejecting a method outside the
    closed 9-method grammar, a non-origin-form target, or a version other than the literal
    `HTTP/1.1` -- validation the prior hand-rolled version silently skipped. -/
def parseRequestLine (req : String) : Option HttpRequest :=
  let lines := req.splitOn "\r\n"
  match lines.head? with
  | none => none
  | some reqLine =>
    match Stdlib.Http11.parseRequestLine reqLine.toUTF8.toList with
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

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine -/
/-- End-to-end Pure Functional HTTP Request Handler. -/
def handleRawRequest (rawReq : String) : String :=
  match parseRequestLine rawReq with
  | some req => formatResponse (routeRequest req)
  | none => formatResponse { statusCode := 400, statusText := "Bad Request", contentType := "text/plain", body := "400 Bad Request\r\n" }

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
/-- High-level model trace for an arbitrary HTTP request string. -/
def serverModelTraceFor (req : String) : List AnyEvent :=
  runModelTrace (httpServerMonadic (TraceM AnyEvent) 8080 1) [] [req]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- Canonical high-level model trace for HTTP GET / request. -/
def canonicalServerTrace : List AnyEvent :=
  serverModelTraceFor "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n"

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- Canonical high-level model trace for HTTP GET /status request. -/
def canonicalStatusServerTrace : List AnyEvent :=
  serverModelTraceFor "GET /status HTTP/1.1\r\nHost: localhost\r\n\r\n"

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#4-semantic-trace-equivalence-verifiedprogram-contract -/
/-- Canonical high-level model trace for HTTP 404 request. -/
def canonical404ServerTrace : List AnyEvent :=
  serverModelTraceFor "GET /unknown HTTP/1.1\r\nHost: localhost\r\n\r\n"


end Spikes.Spike4HttpServer

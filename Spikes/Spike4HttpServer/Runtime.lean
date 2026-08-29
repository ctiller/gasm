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

import Gasm.Core.Platform
import Gasm.Effects.Network
import Spikes.Spike4HttpServer.Spec
import Spikes.Spike4HttpServer.StreamingRequestLine

namespace Spikes.Spike4HttpServer

open Gasm.Core.Platform
open Gasm.Effects

/-!
Logical semantics of the verified Gasm HTTP request-line runtime component.  Native and Wasm
artifacts call this component through target-specific ABI realizations; this file deliberately
contains no target instruction or object-format definitions.
-/

/-- Maximum bytes retained by the request-scope parser. -/
def requestLineBudget : Nat := 1024

/-- Maximum bytes transferred by one socket read.  This bounds the concrete scratch allocation
without bounding the finite request domain. -/
def requestReadChunk : Nat := 256

/-- Target ABI spellings are centralized beside the logical component contract. -/
def gasmHttpParserSymbol : String := "gasm_http_parse_request_line"
def gasmHttpRuntimeDll : String := "GASMRT.dll"
def gasmHttpWasmModule : String := "gasm:verified/http-parser"
def gasmHttpLinuxSyscall : UInt64 := 0x4741534D

inductive RuntimeRoute where
  | root
  | status
  | notFound
  | badRequest
  | resourceExhausted
  deriving DecidableEq, BEq, Repr, Inhabited

def requestResourceExhaustedResponse : HttpResponse :=
  { statusCode := 414, statusText := "URI Too Long", contentType := "text/plain",
    body := "414 URI Too Long\r\n" }

def responseForRoute : RuntimeRoute → String
  | .root => formatResponse (routeRequest
      { method := "GET", path := "/", version := "HTTP/1.1" })
  | .status => formatResponse (routeRequest
      { method := "GET", path := "/status", version := "HTTP/1.1" })
  | .notFound => formatResponse (routeRequest
      { method := "GET", path := "/not-found", version := "HTTP/1.1" })
  | .badRequest => formatResponse badRequestResponse
  | .resourceExhausted => formatResponse requestResourceExhaustedResponse

def routeParsed : Except Stdlib.Http11.Error (Stdlib.Http11.Method × List UInt8) → RuntimeRoute
  | .error _ => .badRequest
  | .ok (_, target) =>
      if target == "/".toUTF8.toList then .root
      else if target == "/status".toUTF8.toList then .status
      else .notFound

structure RequestDrive where
  parser : StreamingRequestLineState := default
  currentRev : List UInt8 := []
  chunksRev : List ByteArray := []
  result : Option RuntimeRoute := none
  deriving Inhabited

def flushCurrent (drive : RequestDrive) : RequestDrive :=
  if drive.currentRev.isEmpty then drive
  else
    { drive with
      currentRev := []
      chunksRev := ByteArray.mk drive.currentRev.reverse.toArray :: drive.chunksRev }

/-- One byte of the runtime implementation.  Bytes after completion or exhaustion are ignored;
closing the request scope releases the unread connection data before the next accept. -/
def driveByte (drive : RequestDrive) (byte : UInt8) : RequestDrive :=
  match drive.result with
  | some _ => drive
  | none =>
      let withByte := { drive with currentRev := byte :: drive.currentRev }
      let withChunk :=
        if withByte.currentRev.length = requestReadChunk then flushCurrent withByte else withByte
      match streamRequestLineByte requestLineBudget drive.parser byte with
      | .needMore parser => { withChunk with parser := parser }
      | .complete parsed => flushCurrent { withChunk with result := some (routeParsed parsed) }
      | .resourceExhausted parser =>
          flushCurrent { withChunk with parser := parser, result := some .resourceExhausted }

/-- Execute the streaming parser for an arbitrary finite request.  The fold is structurally
finite, each retained parser state is bounded by `requestLineBudget`, and every transfer recorded
in `chunks` is bounded by `requestReadChunk`. -/
def driveRequest (request : ByteArray) : RuntimeRoute × List ByteArray :=
  let driven := (Gasm.Effects.toByteList request).foldl driveByte default
  let finished := flushCurrent driven
  let route := match finished.result with
    | some route => route
    | none => routeParsed (finishStreamingRequestLine finished.parser)
  (route, finished.chunksRev.reverse)

def observedRequest (request : ByteArray) : ByteArray :=
  (driveRequest request).2.foldl (init := ByteArray.empty) (fun bytes chunk => bytes ++ chunk)

def requestTrace (request : ByteArray) : List AnyEvent :=
  let driven := driveRequest request
  [ AnyEvent.of (NetEvent.accept "127.0.0.1"),
    AnyEvent.of (NetEvent.recv (bytesToPayload (observedRequest request))),
    AnyEvent.of (NetEvent.send (responseForRoute driven.1)),
    AnyEvent.of (NetEvent.close 101) ]

/-- Whole-server runtime semantics for every finite request queue.  Resource exhaustion is local
to one request: `requestTrace` closes that connection and `flatMap` continues with the rest. -/
def runtimeTrace (requests : List ByteArray) : List AnyEvent :=
  AnyEvent.of (NetEvent.listen 8080) :: requests.flatMap requestTrace

/-- Environment-level specification.  Non-network oracle fields cannot silently narrow the
claim; they are quantified by `VerifiedProgram` and intentionally observationally irrelevant. -/
def serverEnvironmentSpec (environment : Environment) : List AnyEvent :=
  runtimeTrace (environment.incomingRequests.take 1)

/-- Recoverability is a property of the request scope rather than an unbounded process resource:
after an exhausted request is closed, executing the next request is exactly its standalone trace. -/
theorem resource_failure_does_not_poison_next (request next : ByteArray)
    (h : (driveRequest request).1 = .resourceExhausted) :
    (runtimeTrace [request, next]).drop (1 + (requestTrace request).length) = requestTrace next := by
  simp [runtimeTrace, requestTrace]

end Spikes.Spike4HttpServer

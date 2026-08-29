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

namespace Spikes.Spike4HttpServer

open Stdlib.Http11

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Request-line bytes retained across short reads.  A pending CR is held outside `line` until the
    following byte determines whether it is the CRLF terminator, so a terminator split across two
    reads is handled without a special caller path. -/
structure StreamingRequestLineState where
  line : List UInt8 := []
  pendingCR : Bool := false
  complete : Bool := false
  deriving Repr, DecidableEq, BEq

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
inductive StreamingRequestLineResult where
  | needMore (state : StreamingRequestLineState)
  | complete (parsed : Except Error (Method × List UInt8))
  | resourceExhausted (state : StreamingRequestLineState)
  deriving Repr

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Consumes one byte under a finite request-scope line budget.  Exhaustion is returned to the
    caller as data; it is not a process exit and the retained state remains available for request
    cleanup/recovery. -/
def streamRequestLineByte (budget : Nat) (state : StreamingRequestLineState) (byte : UInt8) :
    StreamingRequestLineResult :=
  if state.complete then .complete (parseRequestLine state.line)
  else if state.pendingCR then
    if byte == 10 then .complete (parseRequestLine state.line)
    else if state.line.length + 2 > budget then .resourceExhausted state
    else .needMore { line := state.line ++ [13, byte], pendingCR := byte == 13 }
  else if byte == 13 then .needMore { state with pendingCR := true }
  else if state.line.length + 1 > budget then .resourceExhausted state
  else .needMore { state with line := state.line ++ [byte] }

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Feeds one short-read chunk.  Once a request line completes, remaining bytes belong to headers
    and are intentionally not interpreted by this request-line state machine. -/
def streamRequestLineChunk (budget : Nat) : StreamingRequestLineState → List UInt8 → StreamingRequestLineResult
  | state, [] => .needMore state
  | state, byte :: rest =>
    match streamRequestLineByte budget state byte with
    | .needMore state' => streamRequestLineChunk budget state' rest
    | result => result

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Ends a stream at EOF.  The parser sees the exact retained line, including a lone trailing CR,
    which it rejects through the standard request-line grammar rather than silently accepting a
    truncated terminator. -/
def finishStreamingRequestLine (state : StreamingRequestLineState) : Except Error (Method × List UInt8) :=
  parseRequestLine (if state.pendingCR then state.line ++ [13] else state.line)

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Once CRLF has been recognized, the shared streaming machine delegates validation to exactly
    the repository's canonical request-line parser. -/
theorem completed_streaming_request_line_agrees (line : List UInt8) :
    finishStreamingRequestLine { line := line, pendingCR := false, complete := true } =
      Stdlib.Http11.parseRequestLine line := rfl

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- A byte that would exceed a request's finite line budget is reported without mutating the
    retained parser state.  The caller can therefore close the request scope and continue serving
    the next connection. -/
theorem stream_request_line_budget_exhausted (budget : Nat) (state : StreamingRequestLineState)
    (byte : UInt8) (hComplete : state.complete = false) (hPending : state.pendingCR = false)
    (hByte : byte ≠ 13) (hBudget : budget < state.line.length + 1) :
    streamRequestLineByte budget state byte = .resourceExhausted state := by
  simp [streamRequestLineByte, hComplete, hPending, hByte, hBudget]

end Spikes.Spike4HttpServer

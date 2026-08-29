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
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Linker
import Gasm.Targets.WASI.ABI
import Spikes.Spike4HttpServer.Spec

namespace Spikes.Spike4HttpServer.Wasm

open Gasm.Core
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike4HttpServer

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
def respRootBytes : ByteArray :=
  (formatResponse (routeRequest { method := "GET", path := "/", version := "HTTP/1.1" })).toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
def respStatusBytes : ByteArray :=
  (formatResponse (routeRequest { method := "GET", path := "/status", version := "HTTP/1.1" })).toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
def resp404Bytes : ByteArray :=
  (formatResponse { statusCode := 404, statusText := "Not Found", contentType := "text/plain", body := "404 Not Found\r\n" }).toUTF8

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Response bytes for 400 Bad Request, taken from the model's own `badRequestResponse` so the
    lowering cannot drift from what `Spec.handleRawRequest` emits on a rejected request line. -/
def resp400Bytes : ByteArray :=
  (formatResponse badRequestResponse).toUTF8

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def sockListenType : FuncType := { params := [.i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def sockAcceptType : FuncType := { params := [.i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def sockRecvType   : FuncType := { params := [.i32, .i32, .i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def sockSendType   : FuncType := { params := [.i32, .i32, .i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def sockCloseType  : FuncType := { params := [.i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def procExitWasmType : FuncType := { params := [.i32], results := [] }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def startType      : FuncType := { params := [], results := [] }

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
def spike4WasmImports : List String := [
  "sock_listen",
  "sock_accept",
  "sock_recv",
  "sock_send",
  "sock_close",
  "proc_exit"
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
def spike4TypeSignatures : List FuncType := [
  sockListenType,
  sockAcceptType,
  sockRecvType,
  sockSendType,
  sockCloseType,
  procExitWasmType,
  startType
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
def spike4DataSegments : List WasmDataSegment := [
  { offset := 0x00,  data := respRootBytes },
  { offset := 0x100, data := respStatusBytes },
  { offset := 0x200, data := resp404Bytes },
  { offset := 0x300, data := resp400Bytes }
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Method-token validation for the WASI lowering, the direct analogue of the x86-64
    `methodValidationInstrs` (`Spikes/Spike4HttpServer/MethodDispatch.lean`) and generated from the
    same `allHttpMethods` table, so the two targets cannot disagree about the method grammar.

    Leaves local 5 holding a pointer to the request target (`bufPtr + methodPathOffset m` for the
    method token that matched) or `0` if no token matched -- `0` is not a possible target pointer
    here because `bufPtr` is nonzero, so the caller tests `i32_eqz` on local 5 to take its 400 Bad
    Request branch. Written as a flat chain of independent `if` tests rather than a nine-deep
    `if_else` nest purely for readability; the tests are mutually exclusive because no method
    token plus its delimiting SP is a masked prefix of another. -/
def wasmMethodValidationInstrs (bufPtr : UInt32) : List WasmInstr :=
  .i32_const 0 :: .local_set 5 ::
    allHttpMethods.flatMap (fun m =>
      [ .i32_const bufPtr,
        .i64_load 0 0,
        .i64_const (methodTokenMask m),
        .i64_and,
        .i64_const (methodTokenWord m),
        .i64_eq,
        .if_else .empty
          [ .i32_const (bufPtr + (methodPathOffset m).toUInt32), .local_set 5 ]
          [] ])

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Emit byte comparisons for a literal beginning at the pointer held in `baseLocal`.
    The caller establishes the literal's bounds before executing this sequence, so every
    `i32.load8_u` is a read of a byte `sock_recv` reported receiving. -/
def wasmLiteralAt (baseLocal : Nat) (bytes : List UInt8) (success : List WasmInstr) : List WasmInstr :=
  (bytes.zipIdx).foldr (fun (b, offset) rest =>
    [ .local_get baseLocal,
      .i32_const offset.toUInt32,
      .i32_add,
      .i32_load8_u 0 0,
      .i32_const b.toUInt32,
      .i32_eq,
      .if_else .empty rest [] ]) success

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Bounded HTTP/1.1 request-line scanner for the WASI lowering.

    `sock_recv` stores its exact byte count in local 2.  This scanner reads only offsets strictly
    below that count, locates the first CRLF, and sets local 10 exactly when that first line has a
    nonempty origin-form target, exactly two SP separators (three fields), and a literal
    `HTTP/1.1` version.  Locals 6--11 are scratch: cursor, SP count, target pointer, version
    pointer, validity flag, and current byte respectively.  The method grammar is checked by
    `wasmMethodValidationInstrs` afterwards, once this scanner has established that its fixed
    eight-byte method window is inside the received request. -/
def wasmRequestLineValidationInstrs (bufPtr : UInt32) : List WasmInstr :=
  let markValid := wasmLiteralAt 9 "HTTP/1.1".toUTF8.toList
    [ .i32_const 1, .local_set 10 ]
  let versionIsLiteral :=
    [ .i32_const bufPtr, .local_get 6, .i32_add,
      .local_get 9, .i32_const 8, .i32_add, .i32_eq,
      .if_else .empty markValid [] ]
  let targetIsOriginForm :=
    [ .local_get 8, .i32_eqz,
      .if_else .empty []
        [ .local_get 8, .i32_load8_u 0 0, .i32_const 47, .i32_eq,
          .if_else .empty versionIsLiteral [] ] ]
  let hasThreeFields :=
    [ .local_get 7, .i32_const 2, .i32_eq,
      .if_else .empty targetIsOriginForm [] ]
  let hasCRLF :=
    [ .i32_const bufPtr, .local_get 6, .i32_add, .i32_const 1, .i32_add,
      .i32_load8_u 0 0, .i32_const 10, .i32_eq,
      .if_else .empty hasThreeFields [] ]
  let onCR :=
    [ .local_get 6, .i32_const 1, .i32_add, .local_get 2, .i32_lt_u,
      .if_else .empty hasCRLF [],
      -- The first CR always ends scanning; only the success path above sets validity.
      .br 2 ]
  let recordSpace :=
    [ .local_get 7, .i32_eqz,
      .if_else .empty
        [ .i32_const bufPtr, .local_get 6, .i32_add, .i32_const 1, .i32_add,
          .local_set 8 ]
        [ .local_get 7, .i32_const 1, .i32_eq,
          .if_else .empty
            [ .i32_const bufPtr, .local_get 6, .i32_add, .i32_const 1, .i32_add,
              .local_set 9 ]
            [] ],
      .local_get 7, .i32_const 1, .i32_add, .local_set 7 ]
  let onSpace :=
    [ .local_get 7, .i32_const 2, .i32_ge_u,
      .if_else .empty
        [ .i32_const 3, .local_set 7 ]
        recordSpace ]
  let onNonCR :=
    [ .local_get 11, .i32_const 32, .i32_eq,
      .if_else .empty onSpace [],
      .local_get 6, .i32_const 1, .i32_add, .local_set 6,
      .br 1 ]
  [ .i32_const 0, .local_set 6,
    .i32_const 0, .local_set 7,
    .i32_const 0, .local_set 8,
    .i32_const 0, .local_set 9,
    .i32_const 0, .local_set 10,
    .block .empty [
      .loop .empty [
        -- Reaching bytes_recv without a CRLF leaves validity false.
        .local_get 6, .local_get 2, .i32_ge_u, .br_if 1,
        .i32_const bufPtr, .local_get 6, .i32_add, .i32_load8_u 0 0, .local_set 11,
        .local_get 11, .i32_const 13, .i32_eq,
        .if_else .empty onCR onNonCR
      ]
    ] ]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#11-supported-http-11-specification-subset -/
/-- Choose a response after the bounded request-line scanner has accepted the line. -/
def wasmValidLineResponseInstrs : List WasmInstr :=
  wasmMethodValidationInstrs 0x400 ++
  [ .local_get 5,
    .i32_eqz,
    .if_else .empty
      [ -- The line is structurally valid but the method is outside the model's closed grammar.
        .i32_const 0x300,
        .local_set 3,
        .i32_const resp400Bytes.size.toUInt32,
        .local_set 4 ]
      [ -- Route using the target pointer selected by the recognised method.
        .local_get 5,
        .i64_load 0 0,
        .i64_const 0x207375746174732F, -- "/status "
        .i64_eq,
        .if_else .empty
          [ .i32_const 0x100,
            .local_set 3,
            .i32_const respStatusBytes.size.toUInt32,
            .local_set 4 ]
          [ .local_get 5,
            .i32_load 0 0,
            .i32_const 0x0000FFFF,
            .i32_and,
            .i32_const 0x202F, -- "/ "
            .i32_eq,
            .if_else .empty
              [ .i32_const 0x00,
                .local_set 3,
                .i32_const respRootBytes.size.toUInt32,
                .local_set 4 ]
              [ .i32_const 0x200,
                .local_set 3,
                .i32_const resp404Bytes.size.toUInt32,
                .local_set 4 ] ] ] ]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
/-- WASM instruction sequence for Spike 4 HTTP 1.1 Server:
    Local 0: server_fd (i32)
    Local 1: client_fd (i32)
    Local 2: bytes_recv (i32)
    Local 3: resp_ptr (i32)
    Local 4: resp_len (i32)
    Local 5: path_ptr (i32) -- request-target pointer chosen by the method-token check, 0 if the
             method was not recognised
    Locals 6--11: bounded request-line scanner scratch state (see `wasmRequestLineValidationInstrs`)
-/
def spike4WasmInstructions : List WasmInstr := [
  -- 1. sock_listen(8080) -> server_fd
  .i32_const 8080,
  .call 0,
  .local_set 0,

  -- Accept loop (runs indefinitely)
  .loop .empty [
    -- 2. sock_accept(server_fd) -> client_fd
    .local_get 0,
    .call 1,
    .local_set 1,

    -- 3. sock_recv(client_fd, buf = 0x400, max_len = 1024) -> bytes_recv
    .local_get 1,
    .i32_const 0x400,
    .i32_const 1024,
    .call 2,
    .local_set 2,

    -- 3b. Validate bytes_recv (REF: docs/tasks/N8-spike4-stack-buffer-overflow.md, defect 2 analog
    -- for this target). sock_recv only ever returns a non-negative count in this model (0 on
    -- EOF/no data), so a plain i32_eqz suffices -- unlike the native targets there is no negative
    -- errno return to additionally guard against here. On EOF, skip routing entirely rather than
    -- inspecting a request buffer sock_recv never wrote into.
    .local_get 2,
    .i32_eqz,
    .if_else .empty [
      -- EOF/no-data teardown: close the connection without touching the request buffer or sending
      -- a response.
      .local_get 1,
      .call 4,
      .drop
    ] (wasmRequestLineValidationInstrs 0x400 ++ [
      .local_get 10,
      .i32_eqz,
      .if_else .empty [
        -- Malformed line: 400 Bad Request, matching the model's rejection.
        .i32_const 0x300,
        .local_set 3,
        .i32_const resp400Bytes.size.toUInt32,
        .local_set 4
      ] wasmValidLineResponseInstrs,
      -- 5. sock_send(client_fd, resp_ptr, resp_len)
      .local_get 1,
      .local_get 3,
      .local_get 4,
      .call 3,
      .drop,

      -- 6. sock_close(client_fd)
      .local_get 1,
      .call 4,
      .drop
    ]),

    -- 7. Loop back to accept next connection
    .br 0
  ]
]

/- REF: docs/STDLIB_HTTP11.md#21-request-line -/
/-- Regression oracle for the bounded WASI parser.  These are execution checks over the same
    arbitrary request strings the model parses; they pin the byte-count boundary and each grammar
    clause without introducing a narrower verified-program domain. -/
def wasmMatchesRawRequestModel (request : ByteArray) : Bool :=
  runWasiTrace spike4WasmInstructions spike4DataSegments ByteArray.empty spike4WasmImports [request]
    == serverModelTraceFor request

#guard wasmMatchesRawRequestModel (req "GET / HTTP/1.1\r\nHost: localhost\r\n\r\n")
#guard wasmMatchesRawRequestModel (req "GET /status HTTP/1.1\r\nHost: localhost\r\n\r\n")
#guard wasmMatchesRawRequestModel (req "GET / HTTP/1.0\r\n")
#guard wasmMatchesRawRequestModel (req "GET http://example.com/ HTTP/1.1\r\n")
#guard wasmMatchesRawRequestModel (req "GET  / HTTP/1.1\r\n")
#guard wasmMatchesRawRequestModel (req "GET / HTTP/1.1 extra\r\n")

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
def spike4WasmFunction : WasmFunction := {
  name := "_start",
  locals := [.i32, .i32, .i32, .i32, .i32, .i32,
             .i32, .i32, .i32, .i32, .i32, .i32],
  body := spike4WasmInstructions
}

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
def spike4WasmModule : WasmModule := {
  imports := [
    { module := "wasi_snapshot_preview1", name := "sock_listen", desc := .func 0 },
    { module := "wasi_snapshot_preview1", name := "sock_accept", desc := .func 1 },
    { module := "wasi_snapshot_preview1", name := "sock_recv",   desc := .func 2 },
    { module := "wasi_snapshot_preview1", name := "sock_send",   desc := .func 3 },
    { module := "wasi_snapshot_preview1", name := "sock_close",  desc := .func 4 },
    { module := "wasi_snapshot_preview1", name := "proc_exit",   desc := .func 5 }
  ],
  functions := [spike4WasmFunction],
  exports := [
    { name := "_start", desc := .func 6 }
  ],
  dataSegments := spike4DataSegments
}

end Spikes.Spike4HttpServer.Wasm

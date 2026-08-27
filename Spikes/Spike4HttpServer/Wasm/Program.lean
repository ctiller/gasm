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
  { offset := 0x200, data := resp404Bytes }
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
/-- WASM instruction sequence for Spike 4 HTTP 1.1 Server:
    Local 0: server_fd (i32)
    Local 1: client_fd (i32)
    Local 2: bytes_recv (i32)
    Local 3: resp_ptr (i32)
    Local 4: resp_len (i32)
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

    -- 4. Route request based on path at offset 0x404
    -- Check if path starts with "/status" (0x73, 0x74, 0x61, 0x74 at 0x405..0x408)
    -- Read byte at 0x405:
    .i32_const 0x405,
    .i32_load8_u 0 0,
    .i32_const 0x73, -- 's'
    .i32_eq,
    .if_else .empty [
      -- Match /status:
      .i32_const 0x100,
      .local_set 3,
      .i32_const respStatusBytes.size.toUInt32,
      .local_set 4
    ] [
      -- Else check if path starts with "/ " (' ' = 0x20)
      .i32_const 0x405,
      .i32_load8_u 0 0,
      .i32_const 0x20, -- ' '
      .i32_eq,
      .if_else .empty [
        -- Match /:
        .i32_const 0x00,
        .local_set 3,
        .i32_const respRootBytes.size.toUInt32,
        .local_set 4
      ] [
        -- Else 404:
        .i32_const 0x200,
        .local_set 3,
        .i32_const resp404Bytes.size.toUInt32,
        .local_set 4
      ]
    ],

    -- 5. sock_send(client_fd, resp_ptr, resp_len)
    .local_get 1,
    .local_get 3,
    .local_get 4,
    .call 3,
    .drop,

    -- 6. sock_close(client_fd)
    .local_get 1,
    .call 4,
    .drop,

    -- 7. Loop back to accept next connection
    .br 0
  ]
]

/- REF: docs/SPIKES/SPIKE4_HTTP_SERVER.md#32-webassembly-wasm -/
def spike4WasmFunction : WasmFunction := {
  name := "_start",
  locals := [.i32, .i32, .i32, .i32, .i32],
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

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
import Gasm.Targets.Wasm.Binary
import Gasm.Targets.Wasm.Text
import Gasm.Targets.Wasm.Linker
import Stdlib.Zlib.Spec

namespace Stdlib.Zlib.Wasm

open Gasm.Core
open Gasm.Targets.Wasm

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Standard 10-byte RFC 1952 GZIP header for WASM linear memory initialization. -/
def gzipHeaderBytes : ByteArray :=
  ByteArray.mk #[0x1F, 0x8B, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03]

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- WebAssembly function calculating CRC-32 over linear memory (params: ptr=i32, len=i32 -> result: i32). -/
def crc32WasmFunction : WasmFunction := {
  name := "zlib_crc32"
  params := [.i32, .i32]
  results := [.i32]
  locals := [.i32, .i32, .i32] -- local 2: crc, local 3: i, local 4: bit
  body := [
    -- crc = 0xFFFFFFFF
    .i32_const 0xFFFFFFFF,
    .local_set 2,
    -- i = 0
    .i32_const 0,
    .local_set 3,

    .block .empty [
      .loop .empty [
        -- break if i >= len
        .local_get 3,
        .local_get 1,
        .i32_ge_u,
        .br_if 1,

        -- crc ^= load_u8(ptr + i)
        .local_get 2,
        .local_get 0,
        .local_get 3,
        .i32_add,
        .i32_load8_u 0 0,
        .i32_xor,
        .local_set 2,

        -- bit = 0
        .i32_const 0,
        .local_set 4,
        .block .empty [
          .loop .empty [
            .local_get 4,
            .i32_const 8,
            .i32_ge_u,
            .br_if 1,

            -- if (crc & 1) crc = (crc >>> 1) ^ 0xEDB88320 else crc = (crc >>> 1)
            .local_get 2,
            .i32_const 1,
            .i32_and,
            .if_else .empty [
              .local_get 2,
              .i32_const 1,
              .i32_shr_u,
              .i32_const 0xEDB88320,
              .i32_xor,
              .local_set 2
            ] [
              .local_get 2,
              .i32_const 1,
              .i32_shr_u,
              .local_set 2
            ],

            .local_get 4,
            .i32_const 1,
            .i32_add,
            .local_set 4,
            .br 0
          ]
        ],

        -- i += 1
        .local_get 3,
        .i32_const 1,
        .i32_add,
        .local_set 3,
        .br 0
      ]
    ],

    -- return crc ^ 0xFFFFFFFF
    .local_get 2,
    .i32_const 0xFFFFFFFF,
    .i32_xor
  ]
  exportName := some "zlib_crc32"
}

end Stdlib.Zlib.Wasm

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
import Gasm.Targets.WASI.ABI
import Stdlib.SmolAlloc.Spec
import Stdlib.SmolAlloc.Wasm
import Spikes.Spike3SortLines.Spec

namespace Spikes.Spike3SortLines.Wasm

open Gasm.Core
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Stdlib.SmolAlloc

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Type signatures for WASI Preview 1 imports:
    0: fd_read (i32, i32, i32, i32) -> i32
    1: fd_write (i32, i32, i32, i32) -> i32
    2: proc_exit (i32) -> void
    3: _start () -> void -/
def spike3TypeSignatures : List FuncType := [
  fdReadType,
  fdWriteType,
  procExitType,
  { params := [], results := [] }
]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Static data segments in linear memory for Spike 3 Wasm:
    - Offset 0x00: stdin ciovec (bufPtr=0x100, bufLen=512) (8 bytes)
    - Offset 0x08: nread / nwritten scratch (8 bytes)
    - Offset 0x10: stdout line ciovec (bufPtr=0, bufLen=0) (8 bytes)
    - Offset 0x18: crlf ciovec (bufPtr=0x80, bufLen=2) (8 bytes)
    - Offset 0x80: CRLF string "\r\n" (2 bytes) -/
def spike3DataSegments : List WasmDataSegment := [
  -- stdin ciovec at offset 0: bufPtr = 0x100 (256), bufLen = 512
  { offset := 0x00, data := encodeCiovec 0x100 512 },
  -- crlf ciovec at offset 0x18: bufPtr = 0x80 (128), bufLen = 2
  { offset := 0x18, data := encodeCiovec 0x80 2 },
  -- crlf string at offset 0x80: "\r\n"
  { offset := 0x80, data := "\r\n".toUTF8 }
]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Full WebAssembly instruction sequence for Spike 3 (Stdin Lexicographical Line Sorter with SmolAlloc).
    
    Local Variables Map:
    - Local 0: nread (i32)
    - Local 1: inBufIdx (i32)
    - Local 2: curByte (i32)
    - Local 3: lineHead (i32)
    - Local 4: lineTail (i32)
    - Local 5: lineCount (i32)
    - Local 6: lineBufPtr (i32)
    - Local 7: lineLen (i32)
    - Local 8: lineCap (i32)
    - Local 9: sortTable (i32)
    - Local 10: i (i32)
    - Local 11: j (i32)
    - Local 12: ptr1 (i32)
    - Local 13: len1 (i32)
    - Local 14: ptr2 (i32)
    - Local 15: len2 (i32)
    - Local 16: cmpRes (i32)
    - Local 17: k (i32)
    - Local 18: minLen (i32)
    - Local 19: b1 (i32)
    - Local 20: b2 (i32)
    - Local 21: curNode (i32)
    - Local 22: nextNode (i32)
    -- SmolAlloc Scratch Locals (23..27):
    - Local 23: allocSize (i32)
    - Local 24: allocAligned (i32)
    - Local 25: allocHeader (i32)
    - Local 26: allocCur (i32)
    - Local 27: allocPrev (i32) -/
def spike3WasmInstructions : List WasmInstr := Id.run do
  let mut code : List WasmInstr := []

  -- 1. Initialize SmolAlloc heap at 0x2000
  code := code ++ initWasmSmolAlloc 0x2000

  -- 2. Initialize Line Builder (lineCap = 64, allocate initial lineBufPtr)
  code := code ++ [
    .i32_const 64,
    .local_set 8, -- lineCap = 64
    .i32_const 0,
    .local_set 7, -- lineLen = 0
    .i32_const 0,
    .local_set 3, -- lineHead = 0
    .i32_const 0,
    .local_set 4, -- lineTail = 0
    .i32_const 0,
    .local_set 5  -- lineCount = 0
  ]
  -- Allocate initial line buffer: lineBufPtr = smol_malloc(64)
  code := code ++ [ .i32_const 64 ]
  code := code ++ emitSmolMallocWasm 23 24 25 26 27
  code := code ++ [ .local_set 6 ]

  -- 3. Ingestion Loop: read stdin chunks via fd_read(0, 0x00, 1, 0x08)
  code := code ++ [
    .block .empty [
      .loop .empty [
        -- Call fd_read(0, 0x00, 1, 0x08)
        .i32_const 0,    -- fd = 0 (stdin)
        .i32_const 0x00, -- iovs_ptr
        .i32_const 1,    -- iovs_len
        .i32_const 0x08, -- nread_ptr
        .call 0,
        .drop,           -- drop errno

        -- Read nread = [0x08]
        .i32_const 0x08,
        .i32_load 2 0,
        .local_set 0,

        -- If nread == 0, break ingestion loop
        .local_get 0,
        .i32_const 0,
        .i32_eq,
        .br_if 1,

        -- Walk through chunk bytes [0 .. nread - 1]
        .i32_const 0,
        .local_set 1, -- inBufIdx = 0

        .block .empty [
          .loop .empty [
            -- Loop condition: inBufIdx >= nread -> break
            .local_get 1,
            .local_get 0,
            .i32_ge_u,
            .br_if 1,

            -- curByte = read byte at (0x100 + inBufIdx)
            .i32_const 0x100,
            .local_get 1,
            .i32_add,
            .i32_load8_u 0 0,
            .local_set 2,

            -- Advance inBufIdx
            .local_get 1,
            .i32_const 1,
            .i32_add,
            .local_set 1,

            -- Check if curByte == '\n' (10)
            .local_get 2,
            .i32_const 10,
            .i32_eq,
            .if_else .empty (
              [
                -- Newline encountered! Trim trailing '\r' (13) if present
                .local_get 7,
                .i32_const 0,
                .i32_gt_u,
                .if_else .empty [
                  .local_get 6,
                  .local_get 7,
                  .i32_const 1,
                  .i32_sub,
                  .i32_add,
                  .i32_load8_u 0 0,
                  .i32_const 13,
                  .i32_eq,
                  .if_else .empty [
                    .local_get 7,
                    .i32_const 1,
                    .i32_sub,
                    .local_set 7
                  ] []
                ] [],

                -- Finalize line string payload: allocate exact buffer via smol_malloc(lineLen + 1)
                .local_get 7,
                .i32_const 1,
                .i32_add
              ] ++ emitSmolMallocWasm 23 24 25 26 27 ++ [
                .local_set 12, -- ptr1 = exact string buffer

                -- Copy lineLen bytes from lineBufPtr to ptr1
                .i32_const 0,
                .local_set 17, -- k = 0
                .block .empty [
                  .loop .empty [
                    .local_get 17,
                    .local_get 7,
                    .i32_ge_u,
                    .br_if 1,
                    -- [ptr1 + k] = [lineBufPtr + k]
                    .local_get 12,
                    .local_get 17,
                    .i32_add,
                    .local_get 6,
                    .local_get 17,
                    .i32_add,
                    .i32_load8_u 0 0,
                    .i32_store8 0 0,
                    .local_get 17,
                    .i32_const 1,
                    .i32_add,
                    .local_set 17,
                    .br 0
                  ]
                ],
                -- Null terminate: [ptr1 + lineLen] = 0
                .local_get 12,
                .local_get 7,
                .i32_add,
                .i32_const 0,
                .i32_store8 0 0,

                -- Allocate LineNode (16 bytes) via smol_malloc(16)
                .i32_const 16
              ] ++ emitSmolMallocWasm 23 24 25 26 27 ++ [
                .local_set 21, -- curNode = allocated node
                -- [curNode + 0] = ptr1
                .local_get 21,
                .local_get 12,
                .i32_store 2 0,
                -- [curNode + 4] = lineLen
                .local_get 21,
                .local_get 7,
                .i32_store 2 4,
                -- [curNode + 8] = 0 (next = null)
                .local_get 21,
                .i32_const 0,
                .i32_store 2 8,

                -- Link into linked list
                .local_get 3,
                .i32_const 0,
                .i32_eq,
                .if_else .empty [
                  -- list was empty: lineHead = curNode, lineTail = curNode
                  .local_get 21,
                  .local_set 3,
                  .local_get 21,
                  .local_set 4
                ] [
                  -- [lineTail + 8] = curNode, lineTail = curNode
                  .local_get 4,
                  .local_get 21,
                  .i32_store 2 8,
                  .local_get 21,
                  .local_set 4
                ],
                -- lineCount++
                .local_get 5,
                .i32_const 1,
                .i32_add,
                .local_set 5,

                -- Reset lineLen = 0 for next line
                .i32_const 0,
                .local_set 7
              ]
            ) (
              [
                -- Regular byte (not '\n'): append curByte to lineBufPtr
                -- If lineLen >= lineCap: resize lineBufPtr via smol_malloc(lineCap * 2)
                .local_get 7,
                .local_get 8,
                .i32_ge_u,
                .if_else .empty (
                  [
                    .local_get 8,
                    .i32_const 2,
                    .i32_mul,
                    .local_set 8,
                    .local_get 8
                  ] ++ emitSmolMallocWasm 23 24 25 26 27 ++ [
                    .local_set 12, -- ptr1 = newBuf
                    -- Copy lineLen bytes from lineBufPtr to ptr1
                    .i32_const 0,
                    .local_set 17,
                    .block .empty [
                      .loop .empty [
                        .local_get 17,
                        .local_get 7,
                        .i32_ge_u,
                        .br_if 1,
                        .local_get 12,
                        .local_get 17,
                        .i32_add,
                        .local_get 6,
                        .local_get 17,
                        .i32_add,
                        .i32_load8_u 0 0,
                        .i32_store8 0 0,
                        .local_get 17,
                        .i32_const 1,
                        .i32_add,
                        .local_set 17,
                        .br 0
                      ]
                    ],
                    -- Free old lineBufPtr
                    .local_get 6
                  ] ++ emitSmolFreeWasm 26 25 ++ [
                    .local_get 12,
                    .local_set 6
                  ]
                ) [],

                -- Store curByte at [lineBufPtr + lineLen]
                .local_get 6,
                .local_get 7,
                .i32_add,
                .local_get 2,
                .i32_store8 0 0,
                -- lineLen++
                .local_get 7,
                .i32_const 1,
                .i32_add,
                .local_set 7
              ]
            ),
            .br 0 -- next byte in chunk
          ]
        ],
        .br 0 -- next chunk
      ]
    ]
  ]

  -- Free staging lineBufPtr
  code := code ++ [ .local_get 6 ]
  code := code ++ emitSmolFreeWasm 26 25

  -- 4. Build Sort Table: allocate sortTable = smol_malloc(lineCount * 8)
  code := code ++ [
    .local_get 5,
    .i32_const 0,
    .i32_gt_u,
    .if_else .empty (
      [
        .local_get 5,
        .i32_const 8,
        .i32_mul
      ] ++ emitSmolMallocWasm 23 24 25 26 27 ++ [
        .local_set 9, -- sortTable

        -- Populate sort table from linked list
        .local_get 3,
        .local_set 21, -- curNode = lineHead
        .i32_const 0,
        .local_set 10, -- i = 0

        .block .empty [
          .loop .empty [
            .local_get 21,
            .i32_const 0,
            .i32_eq,
            .br_if 1,

            -- [sortTable + i*8 + 0] = curNode.strPtr
            .local_get 9,
            .local_get 10,
            .i32_const 8,
            .i32_mul,
            .i32_add,
            .local_get 21,
            .i32_load 2 0,
            .i32_store 2 0,

            -- [sortTable + i*8 + 4] = curNode.strLen
            .local_get 9,
            .local_get 10,
            .i32_const 8,
            .i32_mul,
            .i32_add,
            .local_get 21,
            .i32_load 2 4,
            .i32_store 2 4,

            -- Advance: i++, curNode = curNode.next
            .local_get 10,
            .i32_const 1,
            .i32_add,
            .local_set 10,
            .local_get 21,
            .i32_load 2 8,
            .local_set 21,
            .br 0
          ]
        ],

        -- 5. Lexicographical Bubble Sort over sortTable
        -- Outer loop: for i = 0 to lineCount - 1
        .i32_const 0,
        .local_set 10, -- i = 0
        .block .empty [
          .loop .empty [
            .local_get 10,
            .local_get 5,
            .i32_ge_u,
            .br_if 1,

            -- Inner loop: for j = 0 to lineCount - 2 - i
            .i32_const 0,
            .local_set 11, -- j = 0
            .block .empty [
              .loop .empty [
                .local_get 11,
                .local_get 5,
                .i32_const 1,
                .i32_sub,
                .local_get 10,
                .i32_sub,
                .i32_ge_u,
                .br_if 1,

                -- Load (ptr1, len1) at table[j]
                .local_get 9,
                .local_get 11,
                .i32_const 8,
                .i32_mul,
                .i32_add,
                .i32_load 2 0,
                .local_set 12,
                .local_get 9,
                .local_get 11,
                .i32_const 8,
                .i32_mul,
                .i32_add,
                .i32_load 2 4,
                .local_set 13,

                -- Load (ptr2, len2) at table[j+1]
                .local_get 9,
                .local_get 11,
                .i32_const 1,
                .i32_add,
                .i32_const 8,
                .i32_mul,
                .i32_add,
                .i32_load 2 0,
                .local_set 14,
                .local_get 9,
                .local_get 11,
                .i32_const 1,
                .i32_add,
                .i32_const 8,
                .i32_mul,
                .i32_add,
                .i32_load 2 4,
                .local_set 15,

                -- Compare string1 vs string2
                -- minLen = min(len1, len2)
                .local_get 13,
                .local_get 15,
                .i32_lt_u,
                .if_else (.val .i32) [ .local_get 13 ] [ .local_get 15 ],
                .local_set 18,

                .i32_const 0,
                .local_set 16, -- cmpRes = 0 (0 = eq, 1 = gt, -1 = lt)
                .i32_const 0,
                .local_set 17, -- k = 0

                .block .empty [
                  .loop .empty [
                    .local_get 17,
                    .local_get 18,
                    .i32_ge_u,
                    .br_if 1,

                    -- b1 = [ptr1 + k], b2 = [ptr2 + k]
                    .local_get 12,
                    .local_get 17,
                    .i32_add,
                    .i32_load8_u 0 0,
                    .local_set 19,
                    .local_get 14,
                    .local_get 17,
                    .i32_add,
                    .i32_load8_u 0 0,
                    .local_set 20,

                    .local_get 19,
                    .local_get 20,
                    .i32_ne,
                    .if_else .empty [
                      .local_get 19,
                      .local_get 20,
                      .i32_gt_u,
                      .if_else .empty [
                        .i32_const 1,
                        .local_set 16
                      ] [
                        .i32_const 0xFFFFFFFF,
                        .local_set 16
                      ],
                      .br 2 -- break out of compare loop
                    ] [],

                    .local_get 17,
                    .i32_const 1,
                    .i32_add,
                    .local_set 17,
                    .br 0
                  ]
                ],

                -- If prefix matched (cmpRes == 0), compare lengths
                .local_get 16,
                .i32_const 0,
                .i32_eq,
                .if_else .empty [
                  .local_get 13,
                  .local_get 15,
                  .i32_gt_u,
                  .if_else .empty [
                    .i32_const 1,
                    .local_set 16
                  ] [
                    .local_get 13,
                    .local_get 15,
                    .i32_lt_u,
                    .if_else .empty [
                      .i32_const 0xFFFFFFFF,
                      .local_set 16
                    ] []
                  ]
                ] [],

                -- If str1 > str2 (cmpRes == 1): swap table[j] and table[j+1]
                .local_get 16,
                .i32_const 1,
                .i32_eq,
                .if_else .empty [
                  -- table[j] = (ptr2, len2)
                  .local_get 9,
                  .local_get 11,
                  .i32_const 8,
                  .i32_mul,
                  .i32_add,
                  .local_get 14,
                  .i32_store 2 0,
                  .local_get 9,
                  .local_get 11,
                  .i32_const 8,
                  .i32_mul,
                  .i32_add,
                  .local_get 15,
                  .i32_store 2 4,

                  -- table[j+1] = (ptr1, len1)
                  .local_get 9,
                  .local_get 11,
                  .i32_const 1,
                  .i32_add,
                  .i32_const 8,
                  .i32_mul,
                  .i32_add,
                  .local_get 12,
                  .i32_store 2 0,
                  .local_get 9,
                  .local_get 11,
                  .i32_const 1,
                  .i32_add,
                  .i32_const 8,
                  .i32_mul,
                  .i32_add,
                  .local_get 13,
                  .i32_store 2 4
                ] [],

                -- j++
                .local_get 11,
                .i32_const 1,
                .i32_add,
                .local_set 11,
                .br 0
              ]
            ],

            -- i++
            .local_get 10,
            .i32_const 1,
            .i32_add,
            .local_set 10,
            .br 0
          ]
        ],

        -- 6. Stream Sorted Lines to stdout via fd_write(1, 0x10, 2, 0x20)
        .i32_const 0,
        .local_set 10, -- i = 0
        .block .empty [
          .loop .empty [
            .local_get 10,
            .local_get 5,
            .i32_ge_u,
            .br_if 1,

            -- Read (ptr, len) from table[i]
            .local_get 9,
            .local_get 10,
            .i32_const 8,
            .i32_mul,
            .i32_add,
            .i32_load 2 0,
            .local_set 12,
            .local_get 9,
            .local_get 10,
            .i32_const 8,
            .i32_mul,
            .i32_add,
            .i32_load 2 4,
            .local_set 13,

            -- Setup stdout_ciovec at 0x10: [0x10] = ptr (12), [0x14] = len (13)
            .i32_const 0x10,
            .local_get 12,
            .i32_store 2 0,
            .i32_const 0x14,
            .local_get 13,
            .i32_store 2 0,

            -- Call fd_write(1, 0x10, 2, 0x20)
            .i32_const 1,    -- fd = 1 (stdout)
            .i32_const 0x10, -- iovs_ptr = 0x10 (string ciovec followed by crlf ciovec at 0x18)
            .i32_const 2,    -- iovs_len = 2
            .i32_const 0x20, -- nwritten_ptr = 0x20
            .call 1,
            .drop,

            .local_get 10,
            .i32_const 1,
            .i32_add,
            .local_set 10,
            .br 0
          ]
        ],

        -- 7. Discharge all SmolAlloc memory obligations
        -- Free sortTable
        .local_get 9
      ] ++ emitSmolFreeWasm 26 25 ++ [
        -- Free all line strings and line nodes
        .local_get 3,
        .local_set 21, -- curNode = lineHead
        .block .empty [
          .loop .empty (
            [
              .local_get 21,
              .i32_const 0,
              .i32_eq,
              .br_if 1,

              -- nextNode = [curNode + 8]
              .local_get 21,
              .i32_load 2 8,
              .local_set 22,

              -- Free string payload: smol_free([curNode + 0])
              .local_get 21,
              .i32_load 2 0
            ] ++ emitSmolFreeWasm 26 25 ++ [
              -- Free node: smol_free(curNode)
              .local_get 21
            ] ++ emitSmolFreeWasm 26 25 ++ [
              .local_get 22,
              .local_set 21,
              .br 0
            ]
          )
        ]
      ]
    ) []
  ]

  -- 8. Clean Exit: proc_exit(0)
  code := code ++ [
    .i32_const 0,
    .call 2
  ]

  return code

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Complete WasmModule descriptor for Spike 3 (Stdin Line Sorter). -/
def spike3WasmModule : WasmModule := {
  imports := [
    { module := wasiModuleName, name := "fd_read", desc := .func 0 },
    { module := wasiModuleName, name := "fd_write", desc := .func 1 },
    { module := wasiModuleName, name := "proc_exit", desc := .func 2 }
  ],
  functions := [
    {
      name := "_start",
      params := [],
      results := [],
      locals := List.replicate 28 .i32,
      body := spike3WasmInstructions,
      exportName := some "_start"
    }
  ],
  memoryPages := some 1,
  dataSegments := spike3DataSegments,
  exports := [
    { name := "memory", desc := .mem 0 }
  ]
}

end Spikes.Spike3SortLines.Wasm

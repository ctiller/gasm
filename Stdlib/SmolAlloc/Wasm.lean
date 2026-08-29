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
import Stdlib.SmolAlloc.Spec

namespace Stdlib.SmolAlloc

open Gasm.Core
open Gasm.Targets.Wasm

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Standard linear memory address storing the 32-bit arena bump pointer. -/
def wasmArenaBumpPtrAddr : UInt32 := 0x1000

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Standard linear memory address storing the 32-bit free list head pointer. -/
def wasmFreeListHeadAddr : UInt32 := 0x1004

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Initial linear memory heap base address for dynamic allocations (e.g. 0x2000 = 8192). -/
def wasmInitialHeapBase : UInt32 := 0x2000

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Initializes the SmolAlloc allocator state in WebAssembly linear memory:
    - Sets arena bump pointer at `wasmArenaBumpPtrAddr` to `heapBase`.
    - Sets free list head at `wasmFreeListHeadAddr` to 0 (null). -/
def initWasmSmolAlloc (heapBase : UInt32 := wasmInitialHeapBase) : List WasmInstr := [
  .i32_const wasmArenaBumpPtrAddr,
  .i32_const heapBase,
  .i32_store 2 0,
  .i32_const wasmFreeListHeadAddr,
  .i32_const 0,
  .i32_store 2 0
]

/- REF: docs/STDLIB_SMOLALLOC.md#32-first-fit-freelist-search -/
/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- WebAssembly inline instructions to allocate `size` bytes using SmolAlloc:
    Expects requested size `size : i32` on top of the operand stack.
    Leaves allocated payload pointer `payloadPtr : i32` on top of the stack.
    
    Uses locals:
    - localSize : local index containing/receiving size
    - localAligned : local index for aligned size ((size + 7) & ~7)
    - localHeader : local index for allocated block header
    - localCur : local index for free list candidate search
    - localPrev : local index for free list previous candidate -/
def emitSmolMallocWasm (localSize : Nat) (localAligned : Nat) (localHeader : Nat) (localCur : Nat) (localPrev : Nat) : List WasmInstr := [
  -- 1. Store size and calculate aligned size = (size + 7) & ~7
  .local_set localSize,
  .local_get localSize,
  .i32_const 7,
  .i32_add,
  .i32_const 0xFFFFFFF8,
  .i32_and,
  .local_set localAligned,

  -- 2. Inspect FreeList for First-Fit match
  .i32_const wasmFreeListHeadAddr,
  .i32_load 2 0,
  .local_set localCur,
  .i32_const 0,
  .local_set localPrev,
  .i32_const 0,
  .local_set localHeader,

  -- Search loop across freelist
  .block .empty [
    .loop .empty [
      .local_get localCur,
      .i32_const 0,
      .i32_eq,
      .br_if 1, -- end of freelist reached without match

      -- Read candidate blockSize from [localCur + 0]
      .local_get localCur,
      .i32_load 2 0,
      .local_get localAligned,
      .i32_ge_u,
      .if_else .empty [
        -- Found fitting block at localCur!
        .local_get localCur,
        .local_set localHeader,

        -- Unlink localCur from freelist
        .local_get localPrev,
        .i32_const 0,
        .i32_eq,
        .if_else .empty [
          -- localCur was head: wasmFreeListHead = localCur.nextFree [localCur + 24]
          .i32_const wasmFreeListHeadAddr,
          .local_get localCur,
          .i32_load 2 24,
          .i32_store 2 0
        ] [
          -- localCur was interior: localPrev.nextFree = localCur.nextFree [localCur + 24]
          .local_get localPrev,
          .local_get localCur,
          .i32_load 2 24,
          .i32_store 2 24
        ],
        -- Mark isFree = 0 at [localCur + 8]
        .local_get localCur,
        .i32_const 0,
        .i32_store 2 8,
        .br 2 -- break out of block
      ] [
        -- Advance to next candidate: localPrev = localCur, localCur = [localCur + 24]
        .local_get localCur,
        .local_set localPrev,
        .local_get localCur,
        .i32_load 2 24,
        .local_set localCur,
        .br 0 -- continue loop
      ]
    ]
  ],

  -- 3. If localHeader is still 0, perform fresh bump allocation
  .local_get localHeader,
  .i32_const 0,
  .i32_eq,
  .if_else .empty [
    -- localHeader = [wasmArenaBumpPtrAddr]
    .i32_const wasmArenaBumpPtrAddr,
    .i32_load 2 0,
    .local_set localHeader,

    -- A fresh allocation must first reserve enough finite linear-memory pages for its
    -- exclusive end.  `memory.grow` returns Wasm's -1 failure sentinel rather than trapping;
    -- preserve that fallibility at the allocator boundary by returning a null payload pointer
    -- and leaving the bump pointer/header memory untouched.
    .local_get localHeader,
    .local_get localAligned,
    .i32_add,
    .i32_const 32,
    .i32_add,
    .local_set localCur,
    .memory_size,
    .local_set localPrev,
    .local_get localCur,
    .i32_const 65535,
    .i32_add,
    .i32_const 65536,
    .i32_div_u,
    .local_set localSize,
    .local_get localSize,
    .local_get localPrev,
    .i32_gt_u,
    .if_else .empty [
      .local_get localSize,
      .local_get localPrev,
      .i32_sub,
      .memory_grow,
      .i32_const 0xFFFFFFFF,
      .i32_eq,
      .if_else .empty [
        .i32_const 0,
        .local_set localHeader
      ] []
    ] [],

    -- Only publish a fresh allocation after page reservation succeeded.
    .local_get localHeader,
    .i32_const 0,
    .i32_eq,
    .if_else .empty [] [
      -- Advance bump pointer: [wasmArenaBumpPtrAddr] = localHeader + localAligned + 32
      .i32_const wasmArenaBumpPtrAddr,
      .local_get localHeader,
      .local_get localAligned,
      .i32_add,
      .i32_const 32,
      .i32_add,
      .i32_store 2 0,

      -- Initialize the 32-byte header.
      .local_get localHeader,
      .local_get localAligned,
      .i32_store 2 0,
      .local_get localHeader,
      .i32_const 0,
      .i32_store 2 8,
      .local_get localHeader,
      .i32_const 8,
      .i32_store 2 16,
      .local_get localHeader,
      .i32_const 0,
      .i32_store 2 24
    ]
  ] [],

  -- 4. Return payload pointer = localHeader + 32, or 0 on finite-capability refusal.
  .local_get localHeader,
  .i32_const 0,
  .i32_eq,
  .if_else .empty [ .i32_const 0 ] [
    .local_get localHeader,
    .i32_const 32,
    .i32_add
  ]
]

/- REF: docs/STDLIB_SMOLALLOC.md#33-deallocation-free -/
/-- WebAssembly inline instructions to free an allocated payload pointer using SmolAlloc:
    Expects `payloadPtr : i32` on top of the stack.
    Discharges memory obligation and links block back into the free list.
    
    Uses locals:
    - localPtr : local index containing/receiving payload pointer
    - localHeader : local index for computed block header (payloadPtr - 32) -/
def emitSmolFreeWasm (localPtr : Nat) (localHeader : Nat) : List WasmInstr := [
  .local_set localPtr,
  -- localHeader = localPtr - 32
  .local_get localPtr,
  .i32_const 32,
  .i32_sub,
  .local_set localHeader,

  -- Mark isFree = 1 at [localHeader + 8]
  .local_get localHeader,
  .i32_const 1,
  .i32_store 2 8,

  -- Prepend localHeader to FreeList:
  -- [localHeader + 24] = [wasmFreeListHeadAddr]
  .local_get localHeader,
  .i32_const wasmFreeListHeadAddr,
  .i32_load 2 0,
  .i32_store 2 24,

  -- [wasmFreeListHeadAddr] = localHeader
  .i32_const wasmFreeListHeadAddr,
  .local_get localHeader,
  .i32_store 2 0
]

end Stdlib.SmolAlloc

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

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- The fresh-allocation end is safe only when both `UInt32` additions retained their
    mathematical value.  Testing merely `candidate < header` is insufficient: a wrapped
    candidate can remain above its header (for example `0x100 + 0xfffffff8 + 32 = 0x118`).
    The emitted fallible allocator performs these same two tests before it publishes a bump
    pointer or header. -/
def wasmFreshAllocationNoWrap (header aligned : UInt32) : Bool :=
  let candidate := header + aligned + 32
  !(candidate < header) && !(candidate - header < aligned)

/-- The previously admitted wrapped candidate is rejected by the strengthened guard. -/
theorem wasmFreshAllocationNoWrap_rejects_wrapped_counterexample :
    wasmFreshAllocationNoWrap 0x100 0xFFFFFFF8 = false := by
  decide

/-- The largest aligned end below `UInt32` overflow is accepted. -/
theorem wasmFreshAllocationNoWrap_accepts_max_aligned_boundary :
    wasmFreshAllocationNoWrap 0xFFFFFFD0 8 = true := by
  decide

/-- Advancing that same request by eight bytes wraps the candidate and is rejected. -/
theorem wasmFreshAllocationNoWrap_rejects_first_aligned_wrap :
    wasmFreshAllocationNoWrap 0xFFFFFFD8 8 = false := by
  decide

/-- Rounding a requested payload up to eight bytes must itself stay in the `UInt32` range.
    This is tested before the fallible allocator even reads the free-list head, so an overflowing
    request cannot reuse or unlink an existing block. -/
def wasmAlignmentNoWrap (size : UInt32) : Bool :=
  let aligned := (size + 7) &&& 0xFFFFFFF8
  !(aligned < size)

/-- The largest request whose eight-byte alignment remains representable is accepted. -/
theorem wasmAlignmentNoWrap_accepts_maximum :
    wasmAlignmentNoWrap 0xFFFFFFF8 = true := by
  decide

/-- The first overflowing request rounds to zero and is rejected before any free-list action. -/
theorem wasmAlignmentNoWrap_rejects_first_overflow :
    wasmAlignmentNoWrap 0xFFFFFFF9 = false := by
  decide

/-- The exact instruction guard emitted before a fallible allocation's free-list search.  Its
    rejecting arm is empty, so it cannot read or mutate allocator memory. -/
def emitWasmAlignmentNoWrapGuard (localSize localAligned : Nat)
    (onAccepted : List WasmInstr) : List WasmInstr := [
  .local_get localAligned,
  .local_get localSize,
  .i32_lt_u,
  .if_else .empty [] onAccepted
]

/- Fallible WebAssembly bump allocation.

    This is the resource-bounded counterpart of `emitSmolMallocWasm`.  It never performs a
    header or bump-pointer store unless the complete allocation range fits the currently
    instantiated linear memory.  On exhaustion (including `i32` address wraparound) it leaves
    `localHeader` equal to zero and therefore returns the null pointer.  A caller must test that
    result and select its specified failure behaviour; it must not dereference null and let the
    interpreter turn an ordinary finite-resource condition into an unclassified Wasm trap.

    `localCur` is scratch after the free-list search and is reused for the candidate end address.
    The page-index comparison avoids computing `memory_size * 65536` in `i32`, which would itself
    wrap at the Wasm32 four-GiB limit. -/
/-- The emitted initialization that runs before any fallible allocation guard.  In particular it
    clears stale `localHeader` scratch before the alignment guard may reject. -/
def emitSmolMallocWasmFallibleInitialization (localSize localAligned localHeader : Nat) :
    List WasmInstr := [
  .local_set localSize,
  .local_get localSize,
  .i32_const 7,
  .i32_add,
  .i32_const 0xFFFFFFF8,
  .i32_and,
  .local_set localAligned,
  -- The shared epilogue returns `localHeader + 32` on success, so clear a caller's scratch
  -- value before the alignment guard can reject.  This is still before every free-list access.
  .i32_const 0,
  .local_set localHeader,
]

/-- The preparation prefix shared by every fallible allocator invocation.  It records the raw
    request and aligned request, clears stale header scratch, and only then decides whether the
    real free-list/fresh-bump continuation may execute. -/
def emitSmolMallocWasmFalliblePrefix (localSize localAligned localHeader : Nat)
    (onAccepted : List WasmInstr) : List WasmInstr :=
  emitSmolMallocWasmFallibleInitialization localSize localAligned localHeader ++
    emitWasmAlignmentNoWrapGuard localSize localAligned onAccepted

/-- The shared result selection used by the fallible allocator after either its free-list or
    fresh-bump path.  The prefix initializes `localHeader`, so a rejected request reaches the
    ordinary null result even when its caller supplied stale scratch locals. -/
def emitSmolMallocWasmFallibleEpilogue (localHeader : Nat) : List WasmInstr := [
  .local_get localHeader,
  .i32_const 0,
  .i32_eq,
  .if_else .empty [
    .i32_const 0
  ] [
    .local_get localHeader,
    .i32_const 32,
    .i32_add
  ]
]

/- The free-list and fresh-bump continuation of the fallible allocator.  Keeping this emitted
   continuation named makes the rejecting preparation branch syntactically explicit: it is only
   passed to the alignment guard and is not evaluated when that guard rejects. -/
def emitSmolMallocWasmFallibleBody (localAligned : Nat) (localHeader : Nat)
    (localCur : Nat) (localPrev : Nat) : List WasmInstr := [
  -- This continuation begins only after the prefix's alignment guard has accepted.
  .i32_const wasmFreeListHeadAddr,
  .i32_load 2 0,
  .local_set localCur,
  .i32_const 0,
  .local_set localPrev,
  .i32_const 0,
  .local_set localHeader,

  .block .empty [
    .loop .empty [
      .local_get localCur,
      .i32_const 0,
      .i32_eq,
      .br_if 1,
      .local_get localCur,
      .i32_load 2 0,
      .local_get localAligned,
      .i32_ge_u,
      .if_else .empty [
        .local_get localCur,
        .local_set localHeader,
        .local_get localPrev,
        .i32_const 0,
        .i32_eq,
        .if_else .empty [
          .i32_const wasmFreeListHeadAddr,
          .local_get localCur,
          .i32_load 2 24,
          .i32_store 2 0
        ] [
          .local_get localPrev,
          .local_get localCur,
          .i32_load 2 24,
          .i32_store 2 24
        ],
        .local_get localCur,
        .i32_const 0,
        .i32_store 2 8,
        .br 2
      ] [
        .local_get localCur,
        .local_set localPrev,
        .local_get localCur,
        .i32_load 2 24,
        .local_set localCur,
        .br 0
      ]
    ]
  ],

  .local_get localHeader,
  .i32_const 0,
  .i32_eq,
  .if_else .empty [
    .i32_const wasmArenaBumpPtrAddr,
    .i32_load 2 0,
    .local_set localHeader,
    .local_get localHeader,
    .local_get localAligned,
    .i32_add,
    .i32_const 32,
    .i32_add,
    .local_set localCur,

    -- Reject a wrapped candidate before it can publish any allocator metadata.  The first
    -- comparison catches ordinary wrap below the header; the second catches a candidate that
    -- wrapped but remained numerically above it.
    .local_get localCur,
    .local_get localHeader,
    .i32_lt_u,
    .if_else .empty [
      .i32_const 0,
      .local_set localHeader
    ] [
      .local_get localCur,
      .local_get localHeader,
      .i32_sub,
      .local_get localAligned,
      .i32_lt_u,
      .if_else .empty [
        .i32_const 0,
        .local_set localHeader
      ] [
      -- The non-wrapping candidate's last byte must be in a current memory page.
      .local_get localCur,
      .i32_const 1,
      .i32_sub,
      .i32_const 16,
      .i32_shr_u,
      .memory_size,
      .i32_lt_u,
      .if_else .empty [
        .i32_const wasmArenaBumpPtrAddr,
        .local_get localCur,
        .i32_store 2 0,
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
      ] [
        .i32_const 0,
        .local_set localHeader
      ]
      ]
    ]
] [],
]

def emitSmolMallocWasmFallible (localSize : Nat) (localAligned : Nat) (localHeader : Nat)
    (localCur : Nat) (localPrev : Nat) : List WasmInstr :=
  emitSmolMallocWasmFalliblePrefix localSize localAligned localHeader
    (emitSmolMallocWasmFallibleBody localAligned localHeader localCur localPrev) ++
  emitSmolMallocWasmFallibleEpilogue localHeader

/-- The complete fallible allocator is exactly its initialization, branch guard, accepted
    free-list/fresh-bump continuation, and shared result epilogue. -/
theorem emitSmolMallocWasmFallible_decomposes (localSize localAligned localHeader localCur localPrev : Nat) :
    emitSmolMallocWasmFallible localSize localAligned localHeader localCur localPrev =
      (emitSmolMallocWasmFallibleInitialization localSize localAligned localHeader ++
        emitWasmAlignmentNoWrapGuard localSize localAligned
          (emitSmolMallocWasmFallibleBody localAligned localHeader localCur localPrev)) ++
        emitSmolMallocWasmFallibleEpilogue localHeader := by
  rfl

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

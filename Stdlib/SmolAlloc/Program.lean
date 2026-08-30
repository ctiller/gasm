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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Assembler
import Stdlib.SmolAlloc.Spec

namespace Stdlib.SmolAlloc

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler

/- REF: docs/STDLIB_SMOLALLOC.md#2-the-abstract-page-source-typeclass-pagesource -/
/-- A finite native arena explicitly granted to the allocator by its embedding platform.

    `endExclusive` is deliberately an address rather than an inferred or default capacity: every
    native caller must choose the bound it is prepared to recover from. -/
structure NativeArenaCapability where
  base         : UInt64
  endExclusive : UInt64
  deriving Repr, DecidableEq

/-- Construct a finite native arena only when its exclusive end is representable.  This is the
    same unsigned addition guarded by the lowered entry sequence before it installs `r15`. -/
def NativeArenaCapability.ofReservation (base bytes : UInt64) : Option NativeArenaCapability :=
  if bytes != 0 && base ≤ 0xFFFFFFFFFFFFFFFF - bytes then
    some { base, endExclusive := base + bytes }
  else
    none

theorem NativeArenaCapability.ofReservation_success (base bytes : UInt64)
    (h : bytes != 0 && base ≤ 0xFFFFFFFFFFFFFFFF - bytes) :
    NativeArenaCapability.ofReservation base bytes =
      some { base, endExclusive := base + bytes } := by
  simp [NativeArenaCapability.ofReservation, h]

theorem NativeArenaCapability.ofReservation_overflow (base bytes : UInt64)
    (h : ¬ (bytes != 0 && base ≤ 0xFFFFFFFFFFFFFFFF - bytes)) :
    NativeArenaCapability.ofReservation base bytes = none := by
  simp [NativeArenaCapability.ofReservation, h]

/-- The fresh-allocation decision implemented by `smol_malloc` after it has rounded a request and
    added its header.  `some header` is a successful fresh allocation; `none` is exhaustion or an
    invalid bump/end ordering. -/
def NativeArenaCapability.allocateFresh (cap : NativeArenaCapability) (nextHeader bytes : UInt64) :
    Option UInt64 :=
  if nextHeader ≤ cap.endExclusive && bytes ≤ cap.endExclusive - nextHeader then
    some nextHeader
  else
    none

theorem NativeArenaCapability.allocateFresh_exhausted (cap : NativeArenaCapability)
    (nextHeader bytes : UInt64)
    (h : ¬ (nextHeader ≤ cap.endExclusive && bytes ≤ cap.endExclusive - nextHeader)) :
    cap.allocateFresh nextHeader bytes = none := by
  simp [NativeArenaCapability.allocateFresh, h]

theorem NativeArenaCapability.allocateFresh_success (cap : NativeArenaCapability)
    (nextHeader bytes : UInt64)
    (h : nextHeader ≤ cap.endExclusive && bytes ≤ cap.endExclusive - nextHeader) :
    cap.allocateFresh nextHeader bytes = some nextHeader := by
  simp [NativeArenaCapability.allocateFresh, h]

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Symbolic x86-64 assembly routine for `smol_malloc(size : rcx) -> rax`.

    Register convention: `r11` is the next fresh block header, `r15` is the exclusive end of a
    capability-provided finite arena, and `r10` is the free-list head.  A fitting recycled block
    succeeds independently of remaining fresh capacity.  A fresh request that would cross `r15`
    returns the null pointer in `rax` and leaves `r11`, `r10`, and memory unchanged.  There is no
    implicit infinite-arena fallback. -/
def smolMallocSymbolicProgram : List SymbolicInstr := [
  -- 1. Align requested size up to multiple of 8: r8 = (rcx + 7) & ~7
  instr (mov_r64 .r8 .rcx),
  instr (add_r64_imm8 .r8 7),
  jb_near_label "fresh_exhausted", -- reject `size + 7` overflow before any write
  instr (and_r64_imm8 .r8 0xF8),

  -- 2. Calculate total block size needed: r9 = r8 + 32
  instr (mov_r64 .r9 .r8),
  instr (add_r64_imm8 .r9 32),
  jb_near_label "fresh_exhausted", -- reject header addition overflow before any write

  -- 3. Check freelist head in r10: if non-null, inspect candidate block
  instr (cmp_r64_imm8 .r10 0),
  jne_label "check_freelist",

  -- Fresh allocation path:
  label "fresh_alloc",
  -- Reject an invalid bump/end ordering before subtracting, then require enough remaining bytes
  -- for the header plus aligned payload.  The two unsigned comparisons avoid wraparound making a
  -- crossed finite boundary look like available capacity.
  instr (cmp_r64 .r11 .r15),
  ja_label "fresh_exhausted",
  instr (mov_r64 .rax .r15),
  instr (sub_r64 .rax .r11),
  instr (cmp_r64 .rax .r9),
  jb_label "fresh_exhausted",
  instr (mov_r64 .rax .r11),        -- rax = current bump pointer
  instr (add_r64 .r11 .r9),         -- advance arena bump pointer: r11 += r9
  -- Initialize 32-byte header in memory at [rax]:
  instr (mov_mem64_disp .rax 0x00 .r8),   -- [rax + 0x00] = blockSize (r8)
  instr (mov_mem64_disp_imm .rax 0x08 0), -- [rax + 0x08] = isFree (0)
  instr (mov_mem64_disp_imm .rax 0x10 8), -- [rax + 0x10] = alignment (8)
  instr (mov_mem64_disp_imm .rax 0x18 0), -- [rax + 0x18] = nextFree = 0
  instr (add_r64_imm8 .rax 32),           -- Return payload pointer: rax = rax + 32
  instr ret_op,

  -- Free list inspection & reuse path:
  label "check_freelist",
  instr (mov_r64 .rax .r10),                   -- rax = candidate block header
  instr (mov_reg64_mem64_disp .rdx .rax 0x00), -- rdx = candidate block's blockSize
  instr (cmp_r64 .rdx .r8),                    -- compare candidate blockSize against requested aligned size (r8)
  jb_label "fresh_alloc",                      -- if candidate is too small (rdx < r8), fall back to fresh allocation
  instr (mov_reg64_mem64_disp .r10 .rax 0x18), -- r10 = [rax + 0x18] (pop freelist head)
  instr (mov_mem64_disp_imm .rax 0x08 0),      -- [rax + 0x08] = isFree (0) (retain original blockSize at [rax])
  instr (mov_mem64_disp_imm .rax 0x18 0),      -- [rax + 0x18] = nextFree = 0
  instr (add_r64_imm8 .rax 32),                -- Return payload pointer: rax = rax + 32
  instr ret_op,

  -- Fresh capacity failure: the null result is the sole failure convention.  No allocator state
  -- or memory header has been touched on this path, so callers may clean up and retry under a
  -- larger explicitly selected capability.
  label "fresh_exhausted",
  instr (xor_r32 .eax .eax),
  instr ret_op
]

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Concrete instruction sequence for smol_malloc. -/
def smolMallocInstructions : List X86_64Instr :=
  assembleProgram 0x1000 smolMallocSymbolicProgram

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Symbolic x86-64 assembly routine for smol_free(ptr : rcx) -> rax.
    Recovers header, sets isFree=1, writes old freelist head to nextFree, and updates r10. -/
def smolFreeSymbolicProgram : List SymbolicInstr := [
  -- 1. Check if ptr == null
  instr (cmp_r64_imm8 .rcx 0),
  je_label "free_null",

  -- 2. Recover header address: rax = ptr - 32
  instr (mov_r64 .rax .rcx),
  instr (sub_r64_imm8 .rax 32),

  -- 3. Mark block as free in memory: [rax + 0x08] = 1
  instr (mov_mem64_disp_imm .rax 0x08 1),

  -- 4. Link block to previous free list head: [rax + 0x18] = r10
  instr (mov_mem64_disp .rax 0x18 .r10),

  -- 5. Update free list head: r10 = rax
  instr (mov_r64 .r10 .rax),

  -- 6. Return true (1) in RAX
  instr (mov_r64_imm64 .rax 1),
  instr ret_op,

  label "free_null",
  instr (xor_r32 .eax .eax),
  instr ret_op
]

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Concrete instruction sequence for smol_free. -/
def smolFreeInstructions : List X86_64Instr :=
  assembleProgram 0x1000 smolFreeSymbolicProgram

end Stdlib.SmolAlloc

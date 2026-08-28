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
import Gasm.Targets.X86_64.CheckedAsm
import Stdlib.SmolAlloc.Spec

namespace Stdlib.SmolAlloc

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.CheckedAsm

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- MH3 pathfinder (`docs/tasks/MH3-capability-authoring-surface.md`): the frame granted at the
    entry to `smol_malloc`'s fresh-allocation header-initialization sequence -- `rax` (the fresh
    block's payload-header base, just bumped from the arena pointer) holds the base of a 32-byte
    exclusively-held region, the exact size of the header the four stores below populate. This is
    the "RSP-frame / header-field pattern" `docs/MEMORY_HOOK.md` #4.2 names as what literal-
    displacement discharge exists for. -/
def freshAllocFrame : Frame := [⟨.rax, 32, .Exclusive⟩]

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- The four header-field stores of `smol_malloc`'s fresh-allocation path, authored through the
    Layer A capability surface instead of raw `instr (mov_mem64_disp ...)`: every literal
    displacement (`0x00`, `0x08`, `0x10`, `0x18`) discharges its `AccessOK` proof automatically via
    `mem_bounds` against `freshAllocFrame`'s 32-byte region -- omit any one of the four, or push a
    displacement past `0x18`, and the term fails to elaborate (`docs/tasks/MH3-...md`'s negative
    control, demonstrated interactively and reverted, not committed as a standing broken build). -/
def freshAllocHeaderChecked : CheckedProgram freshAllocFrame (fun _ => True) :=
  [ storeReg64 .rax 0x00 .r8,
    storeImm64 .rax 0x08 0,
    storeImm64 .rax 0x10 8,
    storeImm64 .rax 0x18 0 ]

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Symbolic x86-64 assembly routine for smol_malloc(size : rcx) -> rax.
    Uses r11 as arena bump pointer and r10 as free list head. -/
def smolMallocSymbolicProgram : List SymbolicInstr := [
  -- 1. Align requested size up to multiple of 8: r8 = (rcx + 7) & ~7
  instr (mov_r64 .r8 .rcx),
  instr (add_r64_imm8 .r8 7),
  instr (and_r64_imm8 .r8 0xF8),

  -- 2. Calculate total block size needed: r9 = r8 + 32
  instr (mov_r64 .r9 .r8),
  instr (add_r64_imm8 .r9 32),

  -- 3. Check freelist head in r10: if non-null, inspect candidate block
  instr (cmp_r64_imm8 .r10 0),
  jne_label "check_freelist",

  -- Fresh allocation path:
  label "fresh_alloc",
  instr (mov_r64 .rax .r11),        -- rax = current bump pointer
  instr (add_r64 .r11 .r9),         -- advance arena bump pointer: r11 += r9
  ] ++
  -- Initialize 32-byte header in memory at [rax]: MH3 pathfinder -- authored through the Layer A
  -- capability surface (`freshAllocHeaderChecked` above) instead of raw memory-operand
  -- constructors; `CheckedAsm.erase` produces exactly the four `instr (mov_mem64_disp ...)` /
  -- `instr (mov_mem64_disp_imm ...)` terms the unmigrated version authored directly (encoding is
  -- byte-for-byte unchanged, `docs/MEMORY_HOOK.md` #4.5) -- so this is that raw list, PROVED
  -- in-bounds against `freshAllocFrame` at authoring time rather than merely asserted correct.
  CheckedAsm.erase freshAllocHeaderChecked ++
  [
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

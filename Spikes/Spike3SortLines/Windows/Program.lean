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
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Linker
import Stdlib.SmolAlloc.Spec
import Stdlib.SmolAlloc.Program
import Spikes.Spike3SortLines.Spec

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker
open Stdlib.SmolAlloc

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Standard CRLF byte sequence placed in .rdata for terminal line delimiter emission. -/
def crlfBytes : ByteArray := "\r\n".toUTF8

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Default sample test input string for standard verified execution. -/
def defaultSampleInput : ByteArray :=
  "cherry\r\napple\r\nbanana\r\n".toUTF8

/- REF: docs/STDLIB_SMOLALLOC.md#1-overview-architectural-role -/
/- REF: docs/MEMORY_PROVENANCE.md#3-provenance-lifecycle-in-spike-3-line-sorter -/
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Symbolic program definition for Spike 3 (Stdin Lexicographical Line Sorter with SmolAlloc).
    1. Sets up 120-byte stack frame preserving 16-byte stack alignment.
    2. Obtains stdin handle via GetStdHandle(STD_INPUT_HANDLE = -10).
    3. Allocates backing virtual memory via VirtualAlloc to initialize SmolAlloc arena (R11 = bump, R10 = freelist).
    4. Dynamically streams input chunks (512 bytes) from stdin into LineNode linked list elements
       and line string payload buffers using smol_malloc with dynamic line buffer reallocation.
    5. Dynamically allocates a contiguous descriptor sort table via smol_malloc.
    6. In-place lexicographical bubble sort over line descriptors.
    7. Streams sorted lines sequentially to stdout via WriteFile.
    8. Discharges all memory obligations via smol_free for every allocated string, node, and table.
    9. Retains the backing arena under the legacy exit-marker convention and terminates with
       ExitProcess(0); this program does not call VirtualFree. -/
def spike3SymbolicProgram : List SymbolicInstr := [
  -- 1. Setup 120-byte stack frame to maintain (RSP - 120) % 16 == 0 before Win32 calls
  instr (sub_rsp 120),

  -- 2. Obtain stdin handle: GetStdHandle(STD_INPUT_HANDLE = -10)
  instr (mov_r32 .ecx 0xFFFFFFF6),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax), -- r12 = stdin handle

  -- 3. Initialize SmolAlloc Arena: VirtualAlloc(NULL, 65536, MEM_COMMIT | MEM_RESERVE = 0x3000, PAGE_READWRITE = 0x04)
  instr (xor_r32 .ecx .ecx),
  instr (mov_r32 .edx 65536),
  instr (mov_r32 .r8d 0x3000),
  instr (mov_r32 .r9d 0x04),
  call_import "VirtualAlloc",
  instr (mov_r64 .r15 .rax), -- r15 = heapBase (saved for VirtualFree)
  instr (mov_r64 .r11 .rax), -- r11 = smolalloc arena bump pointer
  instr (xor_r32 .r10d .r10d), -- r10 = smolalloc freelist head = NULL
  instr (mov_mem64_disp_imm .rsp 0x30 0), -- [rsp + 0x30] = lineCount = 0
  instr (mov_mem64_disp_imm .rsp 0x38 0), -- [rsp + 0x38] = headNode = NULL
  instr (mov_mem64_disp_imm .rsp 0x60 0), -- [rsp + 0x60] = lineBufLen = 0
  instr (mov_mem64_disp_imm .rsp 0x68 256), -- [rsp + 0x68] = lineBufCap = 256

  -- 4. Allocate 512-byte stream read chunk buffer via smol_malloc(512)
  instr (mov_r32 .ecx 512),
  call_label "smol_malloc",
  instr (mov_mem64_disp .rsp 0x50 .rax), -- [rsp + 0x50] = chunkBufPtr

  -- 5. Allocate initial 256-byte line accumulator buffer via smol_malloc(256)
  instr (mov_r32 .ecx 256),
  call_label "smol_malloc",
  instr (mov_mem64_disp .rsp 0x58 .rax), -- [rsp + 0x58] = lineBufPtr

  -- 6. Unbounded Streaming Ingestion: ReadFile into 512-byte chunkBuf in a loop
  label "stream_read_loop",
  instr (mov_r64 .rcx .r12), -- hStdin
  instr (mov_reg64_mem64_disp .rdx .rsp 0x50), -- chunkBufPtr
  instr (mov_r32 .r8d 512),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  -- Save smolalloc state across Win32 call:
  instr (mov_mem64_disp .rsp 0x40 .r11),
  instr (mov_mem64_disp .rsp 0x48 .r10),
  call_import "ReadFile",
  -- Restore smolalloc state:
  instr (mov_reg64_mem64_disp .r11 .rsp 0x40),
  instr (mov_reg64_mem64_disp .r10 .rsp 0x48),

  instr (mov_r32_rsp .eax 0x28), -- eax = bytesRead
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "stream_eof",

  -- Scan chunk bytes [chunkBuf .. chunkBuf + bytesRead]
  instr (mov_reg64_mem64_disp .rsi .rsp 0x50), -- rsi = chunk scan pointer
  instr (mov_r64 .rdi .rsi),
  instr (mov_r32_rsp .eax 0x28),
  instr (add_r64 .rdi .rax),                   -- rdi = chunk end pointer

  label "chunk_scan_loop",
  instr (cmp_r64 .rsi .rdi),
  jge_near_label "stream_read_loop",

  instr (movzx_r64_mem8 .rax .rsi 0),
  instr (cmp_r64_imm8 .rax 0x0A), -- '\n'
  je_near_label "handle_newline",
  instr (cmp_r64_imm8 .rax 0x0D), -- '\r'
  je_near_label "handle_cr",

  -- Regular character: check if lineBuf needs dynamic growth
  instr (mov_reg64_mem64_disp .rcx .rsp 0x60), -- lineBufLen
  instr (mov_reg64_mem64_disp .rdx .rsp 0x68), -- lineBufCap
  instr (cmp_r64 .rcx .rdx),
  jb_near_label "append_char",

  -- Grow line buffer dynamically: newCap = lineBufCap + 256
  instr (add_r64_imm32 .rdx 256),
  instr (mov_mem64_disp .rsp 0x68 .rdx),       -- update lineBufCap
  instr (mov_r64 .rcx .rdx),
  call_label "smol_malloc",
  -- rax = newBufPtr
  instr (mov_reg64_mem64_disp .rbx .rsp 0x58), -- rbx = oldBufPtr
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60), -- rdx = lineBufLen
  -- Copy oldBuf bytes into newBuf:
  instr (xor_r32 .ecx .ecx),
  label "grow_copy_loop",
  instr (cmp_r64 .rcx .rdx),
  jge_near_label "grow_copy_done",
  instr (mov_r64 .r8 .rbx),
  instr (add_r64 .r8 .rcx),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (mov_r64 .r9 .rax),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "grow_copy_loop",

  label "grow_copy_done",
  instr (mov_mem64_disp .rsp 0x20 .rax),       -- save newBufPtr at [rsp + 0x20]
  instr (mov_r64 .rcx .rbx),
  call_label "smol_free",                      -- free oldBuf
  instr (mov_reg64_mem64_disp .rax .rsp 0x20), -- restore newBufPtr
  instr (mov_mem64_disp .rsp 0x58 .rax),       -- update lineBufPtr = newBufPtr

  label "append_char",
  instr (movzx_r64_mem8 .rax .rsi 0),          -- reload char
  instr (mov_reg64_mem64_disp .rdx .rsp 0x58), -- lineBufPtr
  instr (mov_reg64_mem64_disp .rcx .rsp 0x60), -- lineBufLen
  instr (mov_r64 .r8 .rdx),
  instr (add_r64 .r8 .rcx),                    -- dest = lineBufPtr + lineBufLen
  instr (mov_mem8 .r8 .rax),                   -- write byte
  instr (add_r64_imm8 .rcx 1),
  instr (mov_mem64_disp .rsp 0x60 .rcx),       -- lineBufLen++
  instr (add_r64_imm8 .rsi 1),
  jmp_near_label "chunk_scan_loop",

  label "handle_cr",
  instr (add_r64_imm8 .rsi 1), -- advance past '\r'
  -- Allocate string: smol_malloc(lineBufLen + 1)
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60), -- rdx = lineBufLen
  instr (mov_r64 .rcx .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (mov_mem64_disp .rsp 0x28 .rdx),       -- save len at [rsp + 0x28]
  call_label "smol_malloc",
  instr (mov_reg64_mem64_disp .rdx .rsp 0x28), -- rdx = lineLen
  instr (mov_reg64_mem64_disp .rbx .rsp 0x58), -- rbx = lineBufPtr
  -- Copy bytes:
  instr (xor_r32 .ecx .ecx),
  label "copy_cr_loop",
  instr (cmp_r64 .rcx .rdx),
  jge_near_label "copy_cr_done",
  instr (mov_r64 .r8 .rbx),
  instr (add_r64 .r8 .rcx),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (mov_r64 .r9 .rax),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "copy_cr_loop",

  label "copy_cr_done",
  -- Allocate LineNode (24 bytes):
  instr (mov_mem64_disp .rsp 0x28 .rax), -- save strPtr
  instr (mov_r32 .ecx 24),
  call_label "smol_malloc",
  instr (mov_reg64_mem64_disp .r8 .rsp 0x28),  -- r8 = strPtr
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60), -- rdx = lineLen
  instr (mov_mem64_disp .rax 0 .r8),           -- [node + 0] = strPtr
  instr (mov_mem64_disp .rax 8 .rdx),          -- [node + 8] = lineLen
  instr (mov_reg64_mem64_disp .r9 .rsp 0x38),  -- r9 = old headNode
  instr (mov_mem64_disp .rax 16 .r9),          -- [node + 16] = nextNode
  instr (mov_mem64_disp .rsp 0x38 .rax),       -- headNode = node

  -- Increment lineCount:
  instr (mov_reg64_mem64_disp .rax .rsp 0x30),
  instr (add_r64_imm8 .rax 1),
  instr (mov_mem64_disp .rsp 0x30 .rax),
  -- Reset lineBufLen:
  instr (mov_mem64_disp_imm .rsp 0x60 0),

  -- If next byte in chunk is '\n', skip it:
  instr (cmp_r64 .rsi .rdi),
  jge_near_label "chunk_scan_loop",
  instr (movzx_r64_mem8 .rax .rsi 0),
  instr (cmp_r64_imm8 .rax 0x0A),
  jne_near_label "chunk_scan_loop",
  instr (add_r64_imm8 .rsi 1),
  jmp_near_label "chunk_scan_loop",

  label "handle_newline",
  instr (add_r64_imm8 .rsi 1), -- advance past '\n'
  -- Allocate string: smol_malloc(lineBufLen + 1)
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60), -- rdx = lineBufLen
  instr (mov_r64 .rcx .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (mov_mem64_disp .rsp 0x28 .rdx),
  call_label "smol_malloc",
  instr (mov_reg64_mem64_disp .rdx .rsp 0x28),
  instr (mov_reg64_mem64_disp .rbx .rsp 0x58),
  -- Copy bytes:
  instr (xor_r32 .ecx .ecx),
  label "copy_nl_loop",
  instr (cmp_r64 .rcx .rdx),
  jge_near_label "copy_nl_done",
  instr (mov_r64 .r8 .rbx),
  instr (add_r64 .r8 .rcx),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (mov_r64 .r9 .rax),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "copy_nl_loop",

  label "copy_nl_done",
  -- Allocate LineNode (24 bytes):
  instr (mov_mem64_disp .rsp 0x28 .rax),
  instr (mov_r32 .ecx 24),
  call_label "smol_malloc",
  instr (mov_reg64_mem64_disp .r8 .rsp 0x28),
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60),
  instr (mov_mem64_disp .rax 0 .r8),
  instr (mov_mem64_disp .rax 8 .rdx),
  instr (mov_reg64_mem64_disp .r9 .rsp 0x38),
  instr (mov_mem64_disp .rax 16 .r9),
  instr (mov_mem64_disp .rsp 0x38 .rax),

  instr (mov_reg64_mem64_disp .rax .rsp 0x30),
  instr (add_r64_imm8 .rax 1),
  instr (mov_mem64_disp .rsp 0x30 .rax),
  instr (mov_mem64_disp_imm .rsp 0x60 0),
  jmp_near_label "chunk_scan_loop",

  label "stream_eof",
  -- Flush any trailing text without newline:
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "free_staging_and_check",
  instr (mov_r64 .rcx .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (mov_mem64_disp .rsp 0x28 .rdx),
  call_label "smol_malloc",
  instr (mov_reg64_mem64_disp .rdx .rsp 0x28),
  instr (mov_reg64_mem64_disp .rbx .rsp 0x58),
  instr (xor_r32 .ecx .ecx),
  label "copy_eof_loop",
  instr (cmp_r64 .rcx .rdx),
  jge_near_label "copy_eof_done",
  instr (mov_r64 .r8 .rbx),
  instr (add_r64 .r8 .rcx),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (mov_r64 .r9 .rax),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "copy_eof_loop",

  label "copy_eof_done",
  instr (mov_mem64_disp .rsp 0x28 .rax),
  instr (mov_r32 .ecx 24),
  call_label "smol_malloc",
  instr (mov_reg64_mem64_disp .r8 .rsp 0x28),
  instr (mov_reg64_mem64_disp .rdx .rsp 0x60),
  instr (mov_mem64_disp .rax 0 .r8),
  instr (mov_mem64_disp .rax 8 .rdx),
  instr (mov_reg64_mem64_disp .r9 .rsp 0x38),
  instr (mov_mem64_disp .rax 16 .r9),
  instr (mov_mem64_disp .rsp 0x38 .rax),
  instr (mov_reg64_mem64_disp .rax .rsp 0x30),
  instr (add_r64_imm8 .rax 1),
  instr (mov_mem64_disp .rsp 0x30 .rax),
  instr (mov_mem64_disp_imm .rsp 0x60 0),

  label "free_staging_and_check",
  -- Free staging buffers:
  instr (mov_reg64_mem64_disp .rcx .rsp 0x50), -- chunkBufPtr
  call_label "smol_free",
  instr (mov_reg64_mem64_disp .rcx .rsp 0x58), -- lineBufPtr
  call_label "smol_free",

  -- Check if any lines were parsed:
  instr (mov_reg64_mem64_disp .rax .rsp 0x30), -- lineCount
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "cleanup_and_exit",

  -- 7. Allocate Dynamic Sort Table: smol_malloc(lineCount * 16)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x30),
  instr (shl_r64_imm8 .rcx 4),                 -- lineCount * 16 bytes
  call_label "smol_malloc",
  instr (mov_r64 .rbx .rax),                   -- rbx = sortTablePtr
  instr (mov_mem64_disp .rsp 0x20 .rax),       -- save sortTablePtr at [rsp + 0x20]

  -- Populate Sort Table from LineNode linked list (in reverse so original order is preserved):
  instr (mov_reg64_mem64_disp .rsi .rsp 0x38), -- rsi = headNode
  instr (mov_reg64_mem64_disp .rcx .rsp 0x30), -- rcx = lineCount
  instr (sub_r64_imm8 .rcx 1),                 -- rcx = index (starts at lineCount - 1)

  label "populate_table_loop",
  instr (cmp_r64_imm8 .rsi 0),
  je_near_label "sort_table_ready",

  -- Slot rcx address: rbx + rcx * 16
  instr (mov_r64 .r8 .rcx),
  instr (shl_r64_imm8 .r8 4),
  instr (add_r64 .r8 .rbx),

  instr (mov_reg64_mem64_disp .rax .rsi 0), -- rax = strPtr
  instr (mov_reg64_mem64_disp .rdx .rsi 8), -- rdx = lineLen
  instr (mov_mem64_disp .r8 0 .rax),
  instr (mov_mem64_disp .r8 8 .rdx),

  instr (mov_reg64_mem64_disp .rsi .rsi 16), -- rsi = nextNode
  instr (sub_r64_imm8 .rcx 1),
  jmp_near_label "populate_table_loop",

  label "sort_table_ready",
  instr (mov_reg64_mem64_disp .r13 .rsp 0x30), -- r13 = lineCount
  instr (cmp_r64_imm8 .r13 1),
  jle_near_label "output_phase",

  -- 8. In-Place Lexicographical Bubble Sort over Sort Table:
  instr (xor_r32 .r8d .r8d), -- i = 0

  label "outer_sort_loop",
  instr (mov_r64 .rax .r13),
  instr (sub_r64_imm8 .rax 1),
  instr (cmp_r64 .r8 .rax),
  jge_near_label "output_phase",

  instr (xor_r32 .r9d .r9d), -- j = 0

  label "inner_sort_loop",
  instr (mov_r64 .rax .r13),
  instr (sub_r64_imm8 .rax 1),
  instr (sub_r64 .rax .r8),
  instr (cmp_r64 .r9 .rax),
  jge_near_label "next_outer_sort",

  -- Slot j address: rbx + j*16
  -- Slot j+1 address: rbx + (j+1)*16
  instr (mov_r64 .rsi .r9),
  instr (shl_r64_imm8 .rsi 4),
  instr (add_r64 .rsi .rbx),                  -- rsi = ptr to slot j
  instr (mov_r64 .rdi .rsi),
  instr (add_r64_imm8 .rdi 16),               -- rdi = ptr to slot j+1

  instr (mov_reg64_mem64_disp .r14 .rsi 0),   -- r14 = str1 ptr
  instr (mov_reg64_mem64_disp .rax .rsi 8),   -- rax = str1 len
  instr (mov_reg64_mem64_disp .rdx .rdi 0),   -- rdx = str2 ptr
  instr (mov_reg64_mem64_disp .rbp .rdi 8),   -- rbp = str2 len

  -- Lexicographical string comparison loop: k = 0 to min(len1, len2)
  instr (xor_r32 .ecx .ecx), -- k = 0

  label "strcmp_loop",
  instr (cmp_r64 .rcx .rax),
  jge_near_label "strcmp_str1_end",
  instr (cmp_r64 .rcx .rbp),
  jge_near_label "swap_slots",

  instr (mov_r64 .r11 .r14),
  instr (add_r64 .r11 .rcx),
  instr (movzx_r64_mem8 .r11 .r11 0), -- r11 = byte1

  instr (mov_r64 .rdx .rdi),
  instr (mov_reg64_mem64_disp .rdx .rdx 0),
  instr (add_r64 .rdx .rcx),
  instr (movzx_r64_mem8 .rdx .rdx 0), -- rdx = byte2

  instr (cmp_r64 .r11 .rdx),
  ja_near_label "swap_slots",
  jb_near_label "no_swap_slots",

  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "strcmp_loop",

  label "strcmp_str1_end",
  jmp_near_label "no_swap_slots",

  label "swap_slots",
  instr (mov_reg64_mem64_disp .r11 .rsi 0),
  instr (mov_reg64_mem64_disp .rdx .rsi 8),
  instr (mov_reg64_mem64_disp .rax .rdi 0),
  instr (mov_reg64_mem64_disp .rbp .rdi 8),

  instr (mov_mem64_disp .rsi 0 .rax),
  instr (mov_mem64_disp .rsi 8 .rbp),
  instr (mov_mem64_disp .rdi 0 .r11),
  instr (mov_mem64_disp .rdi 8 .rdx),

  label "no_swap_slots",
  instr (add_r64_imm8 .r9 1), -- j++
  jmp_near_label "inner_sort_loop",

  label "next_outer_sort",
  instr (add_r64_imm8 .r8 1), -- i++
  jmp_near_label "outer_sort_loop",

  -- 9. Output Phase: Stream sorted lines to stdout via Win32 WriteFile
  label "output_phase",
  instr (mov_r32 .ecx 0xFFFFFFF5),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax), -- r12 = stdout handle

  instr (mov_reg64_mem64_disp .rbx .rsp 0x20), -- rbx = sortTablePtr
  instr (xor_r32 .r14d .r14d),                 -- r14 = line index = 0

  label "output_loop",
  instr (mov_reg64_mem64_disp .rax .rsp 0x30), -- rax = lineCount
  instr (cmp_r64 .r14 .rax),
  jge_near_label "deallocate_all_phase",

  -- Write line text: WriteFile(hStdout, linePtr, lineLen, &bytesWritten, NULL)
  instr (mov_r64 .rcx .r12),
  instr (mov_reg64_mem64_disp .rdx .rbx 0),
  instr (mov_reg64_mem64_disp .r8 .rbx 8),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  -- Save smolalloc state across Win32 call:
  instr (mov_mem64_disp .rsp 0x40 .r11),
  instr (mov_mem64_disp .rsp 0x48 .r10),
  call_import "WriteFile",
  -- Restore smolalloc state:
  instr (mov_reg64_mem64_disp .r11 .rsp 0x40),
  instr (mov_reg64_mem64_disp .r10 .rsp 0x48),

  -- Write CRLF delimiter: WriteFile(hStdout, &crlfBytes, 2, &bytesWritten, NULL)
  instr (mov_r64 .rcx .r12),
  lea_data .rdx "crlfBytes",
  instr (mov_r32 .r8d 2),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  instr (mov_mem64_disp .rsp 0x40 .r11),
  instr (mov_mem64_disp .rsp 0x48 .r10),
  call_import "WriteFile",
  instr (mov_reg64_mem64_disp .r11 .rsp 0x40),
  instr (mov_reg64_mem64_disp .r10 .rsp 0x48),

  instr (add_r64_imm8 .rbx 16),
  instr (add_r64_imm8 .r14 1),
  jmp_near_label "output_loop",

  -- 10. Complete Deallocation Phase via smol_free (0 Leaks):
  label "deallocate_all_phase",
  -- Free sort table: smol_free(sortTablePtr)
  instr (mov_reg64_mem64_disp .rcx .rsp 0x20),
  call_label "smol_free",

  -- Free all LineNodes and string payload buffers:
  instr (mov_reg64_mem64_disp .rsi .rsp 0x38), -- rsi = headNode

  label "free_nodes_loop",
  instr (cmp_r64_imm8 .rsi 0),
  je_near_label "cleanup_and_exit",

  instr (mov_reg64_mem64_disp .rbx .rsi 16), -- rbx = nextNode
  instr (mov_reg64_mem64_disp .rcx .rsi 0),  -- rcx = strPtr
  call_label "smol_free",
  instr (mov_r64 .rcx .rsi),                 -- rcx = node
  call_label "smol_free",
  instr (mov_r64 .rsi .rbx),                 -- rsi = nextNode
  jmp_near_label "free_nodes_loop",

  -- 11. Root-program termination; the current ledger accepts the legacy page exit marker, but
  --     this instruction stream does not release the arena or prove typed root-lifetime teardown:
  label "cleanup_and_exit",
  instr (xor_r32 .ecx .ecx),
  call_import "ExitProcess"
] ++ [
  -- =========================================================================
  -- STANDARD LIBRARY SMOLALLOC SUBROUTINES (FROM STDLIB.SMOLALLOC.PROGRAM)
  -- =========================================================================
  label "smol_malloc"
] ++ smolMallocSymbolicProgram ++ [
  label "smol_free"
] ++ smolFreeSymbolicProgram

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Linked binary program artifact for Spike 3. -/
def spike3Linked : LinkedWindowsProgram :=
  linkWindowsProgram spike3SymbolicProgram [
    ("crlfBytes", crlfBytes)
  ]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Lowered concrete machine instruction sequence for Spike 3. -/
def spike3Instructions : List X86_64Instr :=
  spike3Linked.instructions

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Standard executable layout descriptor for Spike 3. -/
def spike3Executable : WindowsExecutable :=
  spike3Linked.executable

end Spikes.Spike3SortLines.Windows

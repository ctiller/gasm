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
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Or
import Gasm.Targets.X86_64.Instructions.Not
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Assembler
import Stdlib.Zlib.Spec

namespace Stdlib.Zlib.X86_64

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Standard 10-byte RFC 1952 GZIP header bytes for Windows binary data sections. -/
def gzipHeaderBytes : ByteArray :=
  ByteArray.mk #[0x1F, 0x8B, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03]

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Complete symbolic x86-64 assembly routine for bitwise CRC-32 checksum calculation.
    Expects input pointer in RCX and byte length in RDX. Returns 32-bit CRC in EAX. -/
def crc32SymbolicProgram : List SymbolicInstr := [
  instr (mov_r32 .eax 0xFFFFFFFF),
  instr (xor_r32 .r8d .r8d),

  label "crc32_calc_loop",
  instr (cmp_r64 .r8 .rdx),
  jae_near_label "crc32_calc_done",

  instr (mov_r64 .r9 .rcx),
  instr (add_r64 .r9 .r8),
  instr (movzx_r64_mem8 .r9 .r9 0),
  instr (xor_r32 .eax .r9d),

  instr (mov_r32 .r10d 0xEDB88320),

  -- 8x unrolled bit shift and conditional XOR with polynomial 0xEDB88320:
  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit0",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit0",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit1",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit1",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit2",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit2",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit3",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit3",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit4",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit4",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit5",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit5",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit6",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit6",

  instr (mov_r64 .r11 .rax),
  instr (and_r64_imm8 .r11 1),
  instr (shr_r64_imm8 .rax 1),
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "crc_sub_bit7",
  instr (xor_r32 .eax .r10d),
  label "crc_sub_bit7",

  instr (add_r64_imm8 .r8 1),
  jmp_near_label "crc32_calc_loop",

  label "crc32_calc_done",
  instr (mov_r32 .r11d 0xFFFFFFFF),
  instr (xor_r32 .eax .r11d),
  instr ret_op
]

/- REF: docs/STDLIB_ZLIB.md#21-adler-32-rfc-1950 -/
/-- Complete symbolic x86-64 assembly routine for Adler-32 checksum calculation.
    Expects input pointer in RCX and byte length in RDX. Returns 32-bit Adler-32 in EAX. -/
def adler32SymbolicProgram : List SymbolicInstr := [
  instr (mov_r32 .r8d 1),
  instr (xor_r32 .r9d .r9d),
  instr (xor_r32 .r10d .r10d),

  label "adler32_calc_loop",
  instr (cmp_r64 .r10 .rdx),
  jge_near_label "adler32_calc_done",

  instr (mov_r64 .r11 .rcx),
  instr (add_r64 .r11 .r10),
  instr (movzx_r64_mem8 .r11 .r11 0),
  instr (add_r64 .r8 .r11),
  instr (add_r64 .r9 .r8),

  instr (add_r64_imm8 .r10 1),
  jmp_near_label "adler32_calc_loop",

  label "adler32_calc_done",
  instr (shr_r64_imm8 .r9 16),
  instr (mov_r64 .rax .r8),
  instr ret_op
]

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Complete x86-64 GZIP compression subroutine (RFC 1952 / RFC 1951 Fixed Huffman Bitstream Encoding).
    Expects outBuf in R14, inBuf in R15, and inLen in RBX.
    Constructs 10-byte GZIP header, encodes payload into RFC 1951 Fixed Huffman blocks with
    bit-packing and EOB delimiter, calculates bitwise CRC-32 in registers,
    and appends 8-byte trailer (CRC32 + ISIZE). Returns total compressed size in R13. -/
def gzipCompressSymbolicProgram : List SymbolicInstr := [
  -- 1. Write 10-byte standard GZIP header to outBuf
  -- ID1=0x1F, ID2=0x8B, CM=8, FLG=0, MTIME=0, XFL=2 (max compression), OS=10 (Windows) / 3 (Unix)
  instr (mov_r64 .r9 .r14),
  instr (mov_r32 .r8d 0x1F),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 1),
  instr (mov_r32 .r8d 0x8B),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 2),
  instr (mov_r32 .r8d 0x08),
  instr (mov_mem8 .r9 .r8),

  -- FLG = 0, MTIME = 0 (bytes 3..7)
  instr (xor_r32 .r8d .r8d),
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 3),
  instr (mov_mem8 .r9 .r8),
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 4),
  instr (mov_mem8 .r9 .r8),
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 5),
  instr (mov_mem8 .r9 .r8),
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 6),
  instr (mov_mem8 .r9 .r8),
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 7),
  instr (mov_mem8 .r9 .r8),

  -- XFL = 2 (max compression)
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 8),
  instr (mov_r32 .r8d 0x02),
  instr (mov_mem8 .r9 .r8),

  -- OS = 3 (Unix/Generic)
  instr (mov_r64 .r9 .r14),
  instr (add_r64_imm8 .r9 9),
  instr (mov_r32 .r8d 0x03),
  instr (mov_mem8 .r9 .r8),

  -- 2. Initialize Bitstream Writer
  -- outPos = 10 (R13), bitBuf = 0 (RSI), bitCount = 0 (RDI)
  instr (mov_r32 .r13d 10),
  instr (xor_r32 .esi .esi),
  instr (xor_r32 .edi .edi),

  -- Write 3 bits DEFLATE header: BFINAL=1 (1 bit), BTYPE=01 (2 bits: Fixed Huffman) -> 0b011 = 3
  instr (mov_r32 .eax 3),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (or_r64 .rsi .rax),
  instr (add_r64_imm8 .rdi 3),

  -- 3. Encode Payload Bytes using RFC 1951 Fixed Huffman Tree with LZ77 Match Search
  instr (xor_r32 .ecx .ecx), -- input index (RCX = 0..rbx-1)
  label "huff_compress_loop",
  instr (cmp_r64 .rcx .rbx),
  jge_near_label "huff_compress_done",

  -- =========================================================================
  -- Sliding-Window LZ77 Match Search
  -- =========================================================================
  instr (cmp_r64_imm8 .rcx 0),
  je_near_label "comp_emit_literal",

  -- maxLen = min(258, rbx - rcx) in R10
  instr (mov_r64 .r10 .rbx),
  instr (sub_r64 .r10 .rcx),
  instr (cmp_r64_imm32 .r10 258),
  jle_near_label "comp_max_len_ok",
  instr (mov_r32 .r10d 258),
  label "comp_max_len_ok",
  instr (cmp_r64_imm8 .r10 3),
  jb_near_label "comp_emit_literal",

  -- maxLookback = min(rcx, 4096) in R8, push on stack
  instr (mov_r64 .r8 .rcx),
  instr (cmp_r64_imm32 .r8 4096),
  jle_near_label "comp_max_lookback_ok",
  instr (mov_r32 .r8d 4096),
  label "comp_max_lookback_ok",
  instr (push_r64 .r8),

  -- bestLen in R11 (0), bestDist in R12 (0), curDist in R9 (1)
  instr (xor_r32 .r11d .r11d),
  instr (xor_r32 .r12d .r12d),
  instr (mov_r32 .r9d 1),

  label "comp_window_search_loop",
  instr (mov_reg64_mem64_disp .rax .rsp 0), -- RAX = maxLookback
  instr (cmp_r64 .r9 .rax),
  ja_near_label "comp_window_search_done",

  -- matchPos = rcx - curDist (R9)
  -- Quick check first byte:
  instr (mov_r64 .rax .r15),
  instr (add_r64 .rax .rcx),
  instr (sub_r64 .rax .r9),
  instr (movzx_r64_mem8 .rax .rax 0), -- inBuf[matchPos]
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .rcx),
  instr (movzx_r64_mem8 .rdx .rdx 0), -- inBuf[rcx]
  instr (cmp_r64 .rax .rdx),
  jne_near_label "comp_window_next_dist",

  -- Quick check byte at bestLen (if bestLen >= 3)
  instr (cmp_r64_imm8 .r11 3),
  jb_near_label "comp_scan_match_bytes",
  instr (mov_r64 .rax .r15),
  instr (add_r64 .rax .rcx),
  instr (sub_r64 .rax .r9),
  instr (add_r64 .rax .r11),
  instr (movzx_r64_mem8 .rax .rax 0),
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .rcx),
  instr (add_r64 .rdx .r11),
  instr (movzx_r64_mem8 .rdx .rdx 0),
  instr (cmp_r64 .rax .rdx),
  jne_near_label "comp_window_next_dist",

  -- Full scan match length k in RAX (0..maxLen-1)
  label "comp_scan_match_bytes",
  instr (xor_r32 .eax .eax),
  label "comp_scan_k_loop",
  instr (cmp_r64 .rax .r10),
  jge_near_label "comp_scan_k_done",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .rcx),
  instr (sub_r64 .rdx .r9),
  instr (add_r64 .rdx .rax),
  instr (movzx_r64_mem8 .rdx .rdx 0),
  instr (mov_r64 .r8 .r15), -- temporary scratch
  instr (add_r64 .r8 .rcx),
  instr (add_r64 .r8 .rax),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (cmp_r64 .rdx .r8),
  jne_near_label "comp_scan_k_done",
  instr (add_r64_imm8 .rax 1),
  jmp_near_label "comp_scan_k_loop",

  label "comp_scan_k_done",
  instr (cmp_r64 .rax .r11),
  jle_near_label "comp_window_next_dist",
  -- Found longer match: update bestLen (R11) and bestDist (R12)
  instr (mov_r64 .r11 .rax),
  instr (mov_r64 .r12 .r9),
  instr (cmp_r64 .r11 .r10),
  jge_near_label "comp_window_search_done",

  label "comp_window_next_dist",
  instr (add_r64_imm8 .r9 1),
  jmp_near_label "comp_window_search_loop",

  label "comp_window_search_done",
  instr (pop_r64 .rax), -- remove maxLookback from stack
  instr (cmp_r64_imm8 .r11 3),
  jb_near_label "comp_emit_literal",

  -- =========================================================================
  -- Encode Match Length (R11 in 3..258) and Match Distance (R12 in 1..4096)
  -- =========================================================================
  -- Save bestDist (R12) on stack
  instr (push_r64 .r12),

  -- Determine Length Symbol (RAX), extraBits (R8), and extraVal (R9) from matchLen (R11)
  instr (cmp_r64_imm32 .r11 258),
  jne_near_label "comp_len_not_258",
  -- matchLen == 258: symbol = 285, extraBits = 0, extraVal = 0
  instr (mov_r32 .eax 285),
  instr (xor_r32 .r8d .r8d),
  instr (xor_r32 .r9d .r9d),
  jmp_near_label "comp_emit_len_symbol",

  label "comp_len_not_258",
  instr (cmp_r64_imm8 .r11 10),
  ja_near_label "comp_len_ge_11",
  -- matchLen in 3..10: symbol = 257 + matchLen - 3 = 254 + matchLen
  instr (mov_r64 .rax .r11),
  instr (add_r64_imm32 .rax 254),
  instr (xor_r32 .r8d .r8d),
  instr (xor_r32 .r9d .r9d),
  jmp_near_label "comp_emit_len_symbol",

  label "comp_len_ge_11",
  instr (cmp_r64_imm8 .r11 18),
  ja_near_label "comp_len_ge_19",
  -- matchLen in 11..18: extraBits = 1, symbol = 265 + (matchLen - 11)/2, extraVal = (matchLen - 11) & 1
  instr (mov_r64 .rax .r11),
  instr (sub_r64_imm8 .rax 11),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 1), -- extraVal in R9
  instr (shr_r64_imm8 .rax 1),
  instr (add_r64_imm32 .rax 265), -- symbol in RAX
  instr (mov_r32 .r8d 1), -- extraBits in R8
  jmp_near_label "comp_emit_len_symbol",

  label "comp_len_ge_19",
  instr (cmp_r64_imm8 .r11 34),
  ja_near_label "comp_len_ge_35",
  -- matchLen in 19..34: extraBits = 2, symbol = 269 + (matchLen - 19)/4, extraVal = (matchLen - 19) & 3
  instr (mov_r64 .rax .r11),
  instr (sub_r64_imm8 .rax 19),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 3),
  instr (shr_r64_imm8 .rax 2),
  instr (add_r64_imm32 .rax 269),
  instr (mov_r32 .r8d 2),
  jmp_near_label "comp_emit_len_symbol",

  label "comp_len_ge_35",
  instr (cmp_r64_imm8 .r11 66),
  ja_near_label "comp_len_ge_67",
  -- matchLen in 35..66: extraBits = 3, symbol = 273 + (matchLen - 35)/8, extraVal = (matchLen - 35) & 7
  instr (mov_r64 .rax .r11),
  instr (sub_r64_imm8 .rax 35),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 7),
  instr (shr_r64_imm8 .rax 3),
  instr (add_r64_imm32 .rax 273),
  instr (mov_r32 .r8d 3),
  jmp_near_label "comp_emit_len_symbol",

  label "comp_len_ge_67",
  instr (cmp_r64_imm32 .r11 130),
  ja_near_label "comp_len_ge_131",
  -- matchLen in 67..130: extraBits = 4, symbol = 277 + (matchLen - 67)/16, extraVal = (matchLen - 67) & 15
  instr (mov_r64 .rax .r11),
  instr (sub_r64_imm8 .rax 67),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 15),
  instr (shr_r64_imm8 .rax 4),
  instr (add_r64_imm32 .rax 277),
  instr (mov_r32 .r8d 4),
  jmp_near_label "comp_emit_len_symbol",

  label "comp_len_ge_131",
  -- matchLen in 131..257: extraBits = 5, symbol = 281 + (matchLen - 131)/32, extraVal = (matchLen - 131) & 31
  instr (mov_r64 .rax .r11),
  instr (sub_r64_imm32 .rax 131),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 31),
  instr (shr_r64_imm8 .rax 5),
  instr (add_r64_imm32 .rax 281),
  instr (mov_r32 .r8d 5),

  label "comp_emit_len_symbol",
  -- Symbol is in RAX (257..285).
  -- Save matchLen (R11), extraBits (R8), and extraVal (R9) on stack
  instr (push_r64 .r11),
  instr (push_r64 .r8),
  instr (push_r64 .r9),

  instr (cmp_r64_imm32 .rax 279),
  ja_near_label "comp_len_code_ge_280",

  -- Symbol in 257..279: 7 bits of rev7(symbol - 256)
  instr (sub_r64_imm32 .rax 256),
  instr (xor_r32 .r8d .r8d),
  instr (mov_r32 .r9d 7),
  label "rev7_len_loop",
  instr (cmp_r64_imm8 .r9 0),
  je_near_label "rev7_len_done",
  instr (shl_r64_imm8 .r8 1),
  instr (mov_r64 .rdx .rax),
  instr (and_r64_imm8 .rdx 1),
  instr (or_r64 .r8 .rdx),
  instr (shr_r64_imm8 .rax 1),
  instr (sub_r64_imm8 .r9 1),
  jmp_near_label "rev7_len_loop",
  label "rev7_len_done",
  -- Pack 7 bits of R8:
  instr (push_r64 .rcx),
  instr (mov_r64 .rax .r8),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (pop_r64 .rcx),
  instr (or_r64 .rsi .rax),
  instr (add_r64_imm8 .rdi 7),
  jmp_near_label "comp_emit_len_extra",

  label "comp_len_code_ge_280",
  -- Symbol in 280..285: 8 bits of rev8(symbol - 280 + 0xC0)
  instr (sub_r64_imm32 .rax 280),
  instr (add_r64_imm32 .rax 0xC0),
  instr (xor_r32 .r8d .r8d),
  instr (mov_r32 .r9d 8),
  label "rev8_len_loop",
  instr (cmp_r64_imm8 .r9 0),
  je_near_label "rev8_len_done",
  instr (shl_r64_imm8 .r8 1),
  instr (mov_r64 .rdx .rax),
  instr (and_r64_imm8 .rdx 1),
  instr (or_r64 .r8 .rdx),
  instr (shr_r64_imm8 .rax 1),
  instr (sub_r64_imm8 .r9 1),
  jmp_near_label "rev8_len_loop",
  label "rev8_len_done",
  -- Pack 8 bits of R8:
  instr (push_r64 .rcx),
  instr (mov_r64 .rax .r8),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (pop_r64 .rcx),
  instr (or_r64 .rsi .rax),
  instr (add_r64_imm8 .rdi 8),

  label "comp_emit_len_extra",
  -- Pop extraVal (R9), extraBits (R8), matchLen (R11)
  instr (pop_r64 .r9),
  instr (pop_r64 .r8),
  instr (pop_r64 .r11),

  -- If extraBits (R8) > 0, pack R8 bits of extraVal (R9) LSB-first
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "comp_emit_dist_symbol",
  instr (push_r64 .rcx),
  instr (mov_r64 .rax .r9),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (pop_r64 .rcx),
  instr (or_r64 .rsi .rax),
  instr (add_r64 .rdi .r8),

  label "comp_emit_dist_symbol",
  -- Pop bestDist from stack into RAX
  instr (pop_r64 .rax),

  -- Determine Distance Symbol (RDX 0..29), extraBits (R8), and extraVal (R9) from bestDist (RAX)
  instr (cmp_r64_imm8 .rax 4),
  ja_near_label "comp_dist_ge_5",
  -- dist in 1..4: symbol = dist - 1, extraBits = 0, extraVal = 0
  instr (mov_r64 .rdx .rax),
  instr (sub_r64_imm8 .rdx 1),
  instr (xor_r32 .r8d .r8d),
  instr (xor_r32 .r9d .r9d),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_5",
  instr (cmp_r64_imm8 .rax 8),
  ja_near_label "comp_dist_ge_9",
  -- dist in 5..8: symbol = 4 + (dist - 5)/2, extraBits = 1, extraVal = (dist - 5) & 1
  instr (sub_r64_imm8 .rax 5),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 1),
  instr (shr_r64_imm8 .rax 1),
  instr (add_r64_imm8 .rax 4),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 1),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_9",
  instr (cmp_r64_imm8 .rax 16),
  ja_near_label "comp_dist_ge_17",
  -- dist in 9..16: symbol = 6 + (dist - 9)/4, extraBits = 2, extraVal = (dist - 9) & 3
  instr (sub_r64_imm8 .rax 9),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 3),
  instr (shr_r64_imm8 .rax 2),
  instr (add_r64_imm8 .rax 6),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 2),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_17",
  instr (cmp_r64_imm8 .rax 32),
  ja_near_label "comp_dist_ge_33",
  -- dist in 17..32: symbol = 8 + (dist - 17)/8, extraBits = 3, extraVal = (dist - 17) & 7
  instr (sub_r64_imm8 .rax 17),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 7),
  instr (shr_r64_imm8 .rax 3),
  instr (add_r64_imm8 .rax 8),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 3),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_33",
  instr (cmp_r64_imm8 .rax 64),
  ja_near_label "comp_dist_ge_65",
  -- dist in 33..64: symbol = 10 + (dist - 33)/16, extraBits = 4, extraVal = (dist - 33) & 15
  instr (sub_r64_imm8 .rax 33),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 15),
  instr (shr_r64_imm8 .rax 4),
  instr (add_r64_imm8 .rax 10),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 4),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_65",
  instr (cmp_r64_imm32 .rax 128),
  ja_near_label "comp_dist_ge_129",
  -- dist in 65..128: symbol = 12 + (dist - 65)/32, extraBits = 5, extraVal = (dist - 65) & 31
  instr (sub_r64_imm8 .rax 65),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 31),
  instr (shr_r64_imm8 .rax 5),
  instr (add_r64_imm8 .rax 12),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 5),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_129",
  instr (cmp_r64_imm32 .rax 256),
  ja_near_label "comp_dist_ge_257",
  -- dist in 129..256: symbol = 14 + (dist - 129)/64, extraBits = 6, extraVal = (dist - 129) & 63
  instr (sub_r64_imm32 .rax 129),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 63),
  instr (shr_r64_imm8 .rax 6),
  instr (add_r64_imm8 .rax 14),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 6),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_257",
  instr (cmp_r64_imm32 .rax 512),
  ja_near_label "comp_dist_ge_513",
  -- dist in 257..512: symbol = 16 + (dist - 257)/128, extraBits = 7, extraVal = (dist - 257) & 127
  instr (sub_r64_imm32 .rax 257),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 127),
  instr (shr_r64_imm8 .rax 7),
  instr (add_r64_imm8 .rax 16),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 7),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_513",
  instr (cmp_r64_imm32 .rax 1024),
  ja_near_label "comp_dist_ge_1025",
  -- dist in 513..1024: symbol = 18 + (dist - 513)/256, extraBits = 8, extraVal = (dist - 513) & 255
  instr (sub_r64_imm32 .rax 513),
  instr (mov_r64 .r9 .rax),
  instr (mov_r32 .r10d 255),
  instr (and_r64 .r9 .r10),
  instr (shr_r64_imm8 .rax 8),
  instr (add_r64_imm8 .rax 18),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 8),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_1025",
  instr (cmp_r64_imm32 .rax 2048),
  ja_near_label "comp_dist_ge_2049",
  -- dist in 1025..2048: symbol = 20 + (dist - 1025)/512, extraBits = 9, extraVal = (dist - 1025) & 511
  instr (sub_r64_imm32 .rax 1025),
  instr (mov_r64 .r9 .rax),
  instr (mov_r32 .r10d 511),
  instr (and_r64 .r9 .r10),
  instr (shr_r64_imm8 .rax 9),
  instr (add_r64_imm8 .rax 20),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 9),
  jmp_near_label "comp_pack_dist_code",

  label "comp_dist_ge_2049",
  -- dist in 2049..4096: symbol = 22 + (dist - 2049)/1024, extraBits = 10, extraVal = (dist - 2049) & 1023
  instr (sub_r64_imm32 .rax 2049),
  instr (mov_r64 .r9 .rax),
  instr (mov_r32 .r10d 1023),
  instr (and_r64 .r9 .r10),
  instr (shr_r64_imm8 .rax 10),
  instr (add_r64_imm8 .rax 22),
  instr (mov_r64 .rdx .rax),
  instr (mov_r32 .r8d 10),

  label "comp_pack_dist_code",
  -- Distance symbol is in RDX (0..29). Pack 5 bits of rev5(RDX) MSB first into bitBuf
  instr (push_r64 .r8),
  instr (push_r64 .r9),
  instr (xor_r32 .eax .eax), -- rev5 in EAX
  instr (mov_r32 .r8d 5),
  label "rev5_dist_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "rev5_dist_done",
  instr (shl_r64_imm8 .rax 1),
  instr (mov_r64 .r10 .rdx),
  instr (and_r64_imm8 .r10 1),
  instr (or_r64 .rax .r10),
  instr (shr_r64_imm8 .rdx 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "rev5_dist_loop",
  label "rev5_dist_done",

  -- Pack 5 bits of RAX into bitBuf (RSI):
  instr (push_r64 .rcx),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (pop_r64 .rcx),
  instr (or_r64 .rsi .rax),
  instr (add_r64_imm8 .rdi 5),

  -- Pop extraVal (R9) and extraBits (R8)
  instr (pop_r64 .r9),
  instr (pop_r64 .r8),

  -- If extraBits (R8) > 0, pack R8 bits of extraVal (R9) LSB-first
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "flush_match_bytes_loop",
  instr (push_r64 .rcx),
  instr (mov_r64 .rax .r9),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (pop_r64 .rcx),
  instr (or_r64 .rsi .rax),
  instr (add_r64 .rdi .r8),

  -- Flush bytes from bitBuf while bitCount (RDI) >= 8:
  label "flush_match_bytes_loop",
  instr (cmp_r64_imm8 .rdi 8),
  jb_near_label "flush_match_bytes_done",
  instr (mov_r64 .rax .rsi),
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r13 1),
  instr (shr_r64_imm8 .rsi 8),
  instr (sub_r64_imm8 .rdi 8),
  jmp_near_label "flush_match_bytes_loop",
  label "flush_match_bytes_done",

  -- Advance input index by matchLen (R11)
  instr (add_r64 .rcx .r11),
  jmp_near_label "huff_compress_loop",

  -- =========================================================================
  -- Emit Single Literal Byte
  -- =========================================================================
  label "comp_emit_literal",
  -- Read byte B from inBuf + rcx
  instr (mov_r64 .r8 .r15),
  instr (add_r64 .r8 .rcx),
  instr (movzx_r64_mem8 .rax .r8 0), -- RAX = B

  -- If B <= 143: code = B + 0x30 (8 bits)
  instr (cmp_r64_imm32 .rax 143),
  ja_near_label "comp_byte_ge_144",

  -- B in 0..143:
  instr (add_r64_imm8 .rax 0x30),
  -- Reverse 8 bits of RAX into R8:
  instr (xor_r32 .r8d .r8d),
  instr (mov_r32 .r9d 8),
  label "rev8_loop",
  instr (cmp_r64_imm8 .r9 0),
  je_near_label "rev8_done",
  instr (shl_r64_imm8 .r8 1),
  instr (mov_r64 .rdx .rax),
  instr (and_r64_imm8 .rdx 1),
  instr (or_r64 .r8 .rdx),
  instr (shr_r64_imm8 .rax 1),
  instr (sub_r64_imm8 .r9 1),
  jmp_near_label "rev8_loop",
  label "rev8_done",
  -- Pack 8 bits of R8 into RSI at RDI:
  instr (mov_r32 .r10d 8), -- bitLen = 8
  jmp_near_label "pack_huff_symbol",

  label "comp_byte_ge_144",
  -- B in 144..255: code = B - 144 + 0x190 (9 bits)
  instr (sub_r64_imm32 .rax 144),
  instr (add_r64_imm32 .rax 0x190),
  -- Reverse 9 bits of RAX into R8:
  instr (xor_r32 .r8d .r8d),
  instr (mov_r32 .r9d 9),
  label "rev9_loop",
  instr (cmp_r64_imm8 .r9 0),
  je_near_label "rev9_done",
  instr (shl_r64_imm8 .r8 1),
  instr (mov_r64 .rdx .rax),
  instr (and_r64_imm8 .rdx 1),
  instr (or_r64 .r8 .rdx),
  instr (shr_r64_imm8 .rax 1),
  instr (sub_r64_imm8 .r9 1),
  jmp_near_label "rev9_loop",
  label "rev9_done",
  -- Pack 9 bits of R8 into RSI at RDI:
  instr (mov_r32 .r10d 9), -- bitLen = 9

  label "pack_huff_symbol",
  -- R8 = reversed code, R10 = bitLen (8 or 9)
  -- bitBuf (RSI) |= (R8 << bitCount (RDI))
  instr (push_r64 .rcx),
  instr (mov_r64 .rax .r8),
  instr (mov_r64 .rcx .rdi),
  instr (shl_r64_cl .rax),
  instr (pop_r64 .rcx),
  instr (or_r64 .rsi .rax),
  instr (add_r64 .rdi .r10),

  -- Flush bytes from bitBuf while bitCount (RDI) >= 8:
  label "flush_bytes_loop",
  instr (cmp_r64_imm8 .rdi 8),
  jb_near_label "flush_bytes_done",
  instr (mov_r64 .rax .rsi),
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r13 1),
  instr (shr_r64_imm8 .rsi 8),
  instr (sub_r64_imm8 .rdi 8),
  jmp_near_label "flush_bytes_loop",
  label "flush_bytes_done",

  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "huff_compress_loop",
  label "huff_compress_done",

  -- 4. Write End of Block (Symbol 256 = 7 bits of 0s)
  -- 7 bits of 0 added to bitCount:
  instr (add_r64_imm8 .rdi 7),

  -- Flush bytes while bitCount >= 8:
  label "flush_eob_loop",
  instr (cmp_r64_imm8 .rdi 8),
  jb_near_label "flush_eob_done",
  instr (mov_r64 .rax .rsi),
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r13 1),
  instr (shr_r64_imm8 .rsi 8),
  instr (sub_r64_imm8 .rdi 8),
  jmp_near_label "flush_eob_loop",
  label "flush_eob_done",

  -- Flush remaining partial byte if bitCount > 0:
  instr (cmp_r64_imm8 .rdi 0),
  je_near_label "flush_final_done",
  instr (mov_r64 .rax .rsi),
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r13 1),
  label "flush_final_done",

  -- 5. Calculate CRC-32 of inBuf (r15, len in rbx)
  instr (mov_r64 .rcx .r15),
  instr (mov_r64 .rdx .rbx),
  call_label "zlib_crc32",

  -- 6. Write 4-byte CRC-32 (LE) to outBuf + outPos (R13):
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_r64 .r8 .rax),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64_imm8 .r9 1),
  instr (mov_r64 .r8 .rax),
  instr (shr_r64_imm8 .r8 8),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64_imm8 .r9 2),
  instr (mov_r64 .r8 .rax),
  instr (shr_r64_imm8 .r8 16),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64_imm8 .r9 3),
  instr (mov_r64 .r8 .rax),
  instr (shr_r64_imm8 .r8 24),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .r13 4),

  -- 7. Write 4-byte ISIZE (inLen in RBX, LE) to outBuf + outPos (R13):
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_r64 .r8 .rbx),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64_imm8 .r9 1),
  instr (mov_r64 .r8 .rbx),
  instr (shr_r64_imm8 .r8 8),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64_imm8 .r9 2),
  instr (mov_r64 .r8 .rbx),
  instr (shr_r64_imm8 .r8 16),
  instr (mov_mem8 .r9 .r8),

  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64_imm8 .r9 3),
  instr (mov_r64 .r8 .rbx),
  instr (shr_r64_imm8 .r8 24),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .r13 4),

  -- Return total compressed size in R13
  instr ret_op
]

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Complete x86-64 GZIP decompression subroutine (RFC 1952 / RFC 1951 Fixed Huffman & Stored Blocks).
    Expects inBuf in R15, inLen in RBX, and outBuf in R14.
    Parses full GZIP header, handles dynamic FLG flags (FEXTRA, FNAME, FCOMMENT, FHCRC),
    decodes both stored blocks (BTYPE=00) and Fixed Huffman compressed blocks (BTYPE=01) with LZ77,
    and computes bitwise CRC-32.
    Returns:
    - R13 = decompressed byte count
    - RAX = 0 on success, 1 on error -/
def gzipDecompressSymbolicProgram : List SymbolicInstr := [
  -- 1. Check minimum GZIP stream length (>= 18 bytes)
  instr (cmp_r64_imm8 .rbx 18),
  jb_near_label "decompress_err",

  -- 2. Verify Magic header ID1=0x1F, ID2=0x8B, CM=8
  instr (mov_r64 .r8 .r15),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (cmp_r64_imm8 .r8 0x1F),
  jne_near_label "decompress_err",

  instr (mov_r64 .r8 .r15),
  instr (add_r64_imm8 .r8 1),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (cmp_r64_imm32 .r8 0x8B),
  jne_near_label "decompress_err",

  instr (mov_r64 .r8 .r15),
  instr (add_r64_imm8 .r8 2),
  instr (movzx_r64_mem8 .r8 .r8 0),
  instr (cmp_r64_imm8 .r8 0x08),
  jne_near_label "decompress_err",

  -- 3. Read FLG at inBuf + 3 (R8 = FLG)
  instr (mov_r64 .r8 .r15),
  instr (add_r64_imm8 .r8 3),
  instr (movzx_r64_mem8 .r8 .r8 0),

  -- Allocate 4096 bytes scratch space on stack for Dynamic Huffman tables
  instr (sub_r64_imm32 .rsp 4096),

  -- Initialize inPos = 10 (R12), outPos = 0 (R13), bitBuf = 0 (RSI), bitCount = 0 (RDI)
  instr (mov_r32 .r12d 10),
  instr (xor_r32 .r13d .r13d),
  instr (xor_r32 .esi .esi),
  instr (xor_r32 .edi .edi),

  -- Handle FEXTRA (FLG & 0x04)
  instr (mov_r64 .rax .r8),
  instr (and_r64_imm8 .rax 0x04),
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "skip_fextra",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (add_r64_imm8 .r9 1),
  instr (movzx_r64_mem8 .rdx .r9 0),
  instr (shl_r64_imm8 .rdx 8),
  instr (or_r64 .rax .rdx),
  instr (add_r64_imm8 .rax 2),
  instr (add_r64 .r12 .rax),
  label "skip_fextra",

  -- Handle FNAME (FLG & 0x08)
  instr (mov_r64 .rax .r8),
  instr (and_r64_imm8 .rax 0x08),
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "skip_fname",
  label "fname_loop",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (cmp_r64_imm8 .rax 0),
  jne_near_label "fname_loop",
  label "skip_fname",

  -- Handle FCOMMENT (FLG & 0x10)
  instr (mov_r64 .rax .r8),
  instr (and_r64_imm8 .rax 0x10),
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "skip_fcomment",
  label "fcomment_loop",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (cmp_r64_imm8 .rax 0),
  jne_near_label "fcomment_loop",
  label "skip_fcomment",

  -- Handle FHCRC (FLG & 0x02)
  instr (mov_r64 .rax .r8),
  instr (and_r64_imm8 .rax 0x02),
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "skip_fhcrc",
  instr (add_r64_imm8 .r12 2),
  label "skip_fhcrc",

  -- =========================================================================
  -- DEFLATE Block Loop
  -- =========================================================================
  label "decompress_block_loop",

  -- Read 1 bit BFINAL (into R10)
  -- Bit reader inline: check if EDI == 0
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "bfinal_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "bfinal_ready",
  instr (mov_r64 .r10 .rsi),
  instr (and_r64_imm8 .r10 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),

  -- Persist BFINAL flag at [RSP + 3001]
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3001),
  instr (mov_mem8 .r9 .r10),

  -- Read 2 bits BTYPE (into R11)
  instr (xor_r32 .r11d .r11d),
  -- Bit 0 of BTYPE:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "btype0_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "btype0_ready",
  instr (mov_r64 .rax .rsi),
  instr (and_r64_imm8 .rax 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (or_r64 .r11 .rax),

  -- Bit 1 of BTYPE:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "btype1_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "btype1_ready",
  instr (mov_r64 .rax .rsi),
  instr (and_r64_imm8 .rax 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .r11 .rax),

  -- Check BTYPE: 0 = Stored, 1 = Fixed Huffman, 2 = Dynamic Huffman
  instr (cmp_r64_imm8 .r11 0),
  je_near_label "block_stored",
  instr (cmp_r64_imm8 .r11 1),
  je_near_label "block_fixed_huff",
  instr (cmp_r64_imm8 .r11 2),
  je_near_label "block_dynamic_huff",
  jmp_near_label "decompress_err",

  -- =========================================================================
  -- Block Type 0: Stored Block
  -- =========================================================================
  label "block_stored",
  -- Byte-align bit reader
  instr (xor_r32 .esi .esi),
  instr (xor_r32 .edi .edi),

  -- Read 16-bit LEN (low byte at inBuf + r12, high byte at inBuf + r12 + 1)
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (add_r64_imm8 .r9 1),
  instr (movzx_r64_mem8 .rdx .r9 0),
  instr (shl_r64_imm8 .rdx 8),
  instr (or_r64 .rax .rdx), -- RAX = LEN
  instr (add_r64_imm8 .r12 4), -- skip LEN and NLEN

  -- Copy LEN bytes to outBuf
  instr (xor_r32 .ecx .ecx),
  label "stored_copy_loop",
  instr (cmp_r64 .rcx .rax),
  jge_near_label "stored_copy_done",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (add_r64 .r9 .rcx),
  instr (movzx_r64_mem8 .rdx .r9 0),
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .rdx),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "stored_copy_loop",
  label "stored_copy_done",
  instr (add_r64 .r13 .rax),
  instr (add_r64 .r12 .rax),

  -- Check BFINAL
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3001),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (cmp_r64_imm8 .rax 1),
  je_near_label "decompress_finish",
  jmp_near_label "decompress_block_loop",

  -- =========================================================================
  -- Block Type 1: Fixed Huffman Block
  -- =========================================================================
  label "block_fixed_huff",
  -- Set is_dynamic flag at [RSP + 3000] = 0
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3000),
  instr (xor_r32 .eax .eax),
  instr (mov_mem8 .r9 .rax),

  label "fixed_symbol_loop",
  -- Read 7 bits (MSB first) into RAX
  instr (xor_r32 .eax .eax),
  instr (xor_r32 .ecx .ecx),
  label "read_7bits_loop",
  instr (cmp_r64_imm8 .rcx 7),
  jge_near_label "read_7bits_done",
  -- Read single bit:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "bit_7_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "bit_7_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .rax .rdx),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "read_7bits_loop",
  label "read_7bits_done",

  -- If RAX == 0 -> Symbol 256 (End of Block)
  instr (cmp_r64_imm8 .rax 0),
  jne_near_label "check_len_257_279",
  -- EOB reached: check BFINAL from stack
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3001),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (cmp_r64_imm8 .rax 1),
  je_near_label "decompress_finish",
  jmp_near_label "decompress_block_loop",

  label "check_len_257_279",
  -- If RAX <= 23 -> Symbol 256 + RAX (Length code 257..279)
  instr (cmp_r64_imm8 .rax 23),
  ja_near_label "read_8th_bit",
  instr (add_r64_imm32 .rax 256),
  jmp_near_label "process_length_symbol",

  label "read_8th_bit",
  -- Read 8th bit
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "bit_8_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "bit_8_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .rax .rdx),

  -- If RAX in 48..191 (0x30..0xBF) -> Literal 0..143
  instr (cmp_r64_imm8 .rax 48),
  jb_near_label "decompress_err",
  instr (cmp_r64_imm32 .rax 191),
  ja_near_label "check_len_280_287",
  instr (sub_r64_imm8 .rax 48), -- literal byte
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r13 1),
  jmp_near_label "fixed_symbol_loop",

  label "check_len_280_287",
  -- If RAX in 192..199 (0xC0..0xC7) -> Length code 280..287
  instr (cmp_r64_imm32 .rax 199),
  ja_near_label "read_9th_bit",
  instr (sub_r64_imm32 .rax 192),
  instr (add_r64_imm32 .rax 280),
  jmp_near_label "process_length_symbol",

  label "read_9th_bit",
  -- Read 9th bit
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "bit_9_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "bit_9_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .rax .rdx),

  -- If RAX in 400..511 (0x190..0x1FF) -> Literal 144..255
  instr (cmp_r64_imm32 .rax 400),
  jb_near_label "decompress_err",
  instr (cmp_r64_imm32 .rax 511),
  ja_near_label "decompress_err",
  instr (sub_r64_imm32 .rax 400),
  instr (add_r64_imm32 .rax 144), -- literal byte
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r13 1),
  jmp_near_label "fixed_symbol_loop",

  -- =========================================================================
  -- Process LZ77 Length and Distance (RFC 1951 Closed-Form Formulas)
  -- =========================================================================
  label "process_length_symbol",
  -- Symbol in RAX (257..285).
  -- Let c = RAX - 257 (0..28)
  instr (sub_r64_imm32 .rax 257),
  instr (cmp_r64_imm8 .rax 8),
  jb_near_label "len_lt_8",

  instr (cmp_r64_imm8 .rax 28),
  jne_near_label "len_normal",
  -- c == 28 (symbol 285): baseLen = 258, extraBits = 0
  instr (mov_r32 .ecx 258),
  instr (xor_r32 .r8d .r8d),
  jmp_near_label "read_len_extra",

  label "len_lt_8",
  -- c < 8 (257..264): baseLen = c + 3, extraBits = 0
  instr (add_r64_imm8 .rax 3),
  instr (mov_r64 .rcx .rax),
  instr (xor_r32 .r8d .r8d),
  jmp_near_label "read_len_extra",

  label "len_normal",
  -- c in 8..27:
  -- extraBits = (c - 4) >> 2 (1..5 in R8)
  instr (mov_r64 .r8 .rax),
  instr (sub_r64_imm8 .r8 4),
  instr (shr_r64_imm8 .r8 2),

  -- p = 1 << extraBits (in RDX)
  instr (mov_r32 .edx 1),
  instr (mov_r64 .rcx .r8),
  label "len_pow_loop",
  instr (cmp_r64_imm8 .rcx 0),
  je_near_label "len_pow_done",
  instr (shl_r64_imm8 .rdx 1),
  instr (sub_r64_imm8 .rcx 1),
  jmp_near_label "len_pow_loop",
  label "len_pow_done",

  -- baseLen = (p << 2) + 3 + (c & 3) * p
  instr (mov_r64 .rcx .rdx),
  instr (shl_r64_imm8 .rcx 2),
  instr (add_r64_imm8 .rcx 3),
  -- (c & 3):
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 3),
  label "len_mult_loop",
  instr (cmp_r64_imm8 .r9 0),
  je_near_label "len_mult_done",
  instr (add_r64 .rcx .rdx),
  instr (sub_r64_imm8 .r9 1),
  jmp_near_label "len_mult_loop",
  label "len_mult_done",
  -- Now RCX = baseLen, R8 = extraBits!

  label "read_len_extra",
  -- If extraBits (R8) > 0, read R8 bits LSB-first and add to RCX
  instr (xor_r32 .eax .eax), -- extraVal = 0
  instr (mov_r32 .r9d 1),     -- bitMask = 1
  label "len_extra_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "len_extra_done",
  -- Read 1 bit into RDX:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "len_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "len_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  -- If bit is 1, or bitMask (R9) into RAX:
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "len_skip_bit",
  instr (or_r64 .rax .r9),
  label "len_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "len_extra_loop",
  label "len_extra_done",
  instr (add_r64 .rcx .rax), -- RCX = final matchLen!

  -- Save matchLen (RCX) on stack
  instr (push_r64 .rcx),

  -- =========================================================================
  -- Read Distance Code (into R8)
  -- =========================================================================
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3008), -- is_dynamic flag (stack has 1 push)
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (cmp_r64_imm8 .rax 1),
  je_near_label "dyn_read_dist_tree",

  -- Fixed Huffman: Read 5 bits Distance Code (MSB-first) into R8
  instr (xor_r32 .r8d .r8d),
  instr (xor_r32 .eax .eax),
  label "read_dist_5bits",
  instr (cmp_r64_imm8 .rax 5),
  jge_near_label "dist_code_ready",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dist_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .r9 .r15),
  instr (add_r64 .r9 .r12),
  instr (movzx_r64_mem8 .rsi .r9 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dist_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .r8 1),
  instr (or_r64 .r8 .rdx),
  instr (add_r64_imm8 .rax 1),
  jmp_near_label "read_dist_5bits",

  label "dyn_read_dist_tree",
  -- Dynamic Huffman: Read bits MSB-first into RAX, search in dist_tree [RSP + 2568]
  instr (xor_r32 .eax .eax), -- bitVal = 0
  instr (xor_r32 .r8d .r8d), -- bitLen = 0
  label "dyn_dist_read_bit",
  instr (cmp_r64_imm8 .r8 15),
  ja_near_label "decompress_err",

  -- Read 1 bit into RDX:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_dist_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_dist_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .rax .rdx),
  instr (add_r64_imm8 .r8 1),

  -- Search symbol d in 0..nDist-1:
  instr (xor_r32 .edx .edx),
  label "dyn_match_dist_d",
  instr (mov_reg64_mem64_disp .r11 .rsp 16), -- nDist at [RSP + 8 + 8] (stack has 1 push)
  instr (cmp_r64 .rdx .r11),
  jge_near_label "dyn_dist_read_bit",

  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 2568),
  instr (mov_r64 .r10 .rdx),
  instr (shl_r64_imm8 .r10 2),
  instr (add_r64 .r9 .r10),
  instr (movzx_r64_mem8 .r11 .r9 2), -- len
  instr (cmp_r64 .r11 .r8),
  jne_near_label "dyn_dist_next_d",
  instr (movzx_r64_mem8 .r10 .r9 0), -- code low
  instr (movzx_r64_mem8 .r11 .r9 1), -- code high
  instr (shl_r64_imm8 .r11 8),
  instr (or_r64 .r10 .r11),
  instr (cmp_r64 .r10 .rax),
  je_near_label "dyn_dist_found",

  label "dyn_dist_next_d",
  instr (add_r64_imm8 .rdx 1),
  jmp_near_label "dyn_match_dist_d",

  label "dyn_dist_found",
  instr (mov_r64 .r8 .rdx), -- Distance code is in R8!

  label "dist_code_ready",

  -- Determine baseDist (RDX) and extraBits (R8) from distCode in R8 (0..29)
  instr (mov_r64 .rax .r8),
  instr (cmp_r64_imm8 .rax 4),
  jb_near_label "dist_lt_4",

  -- d in 4..29:
  -- extraBits = (d - 2) >> 1 (1..13 in R8)
  instr (mov_r64 .r8 .rax),
  instr (sub_r64_imm8 .r8 2),
  instr (shr_r64_imm8 .r8 1),

  -- p = 1 << extraBits (in RDX)
  instr (mov_r32 .edx 1),
  instr (mov_r64 .rcx .r8),
  label "dist_pow_loop",
  instr (cmp_r64_imm8 .rcx 0),
  je_near_label "dist_pow_done",
  instr (shl_r64_imm8 .rdx 1),
  instr (sub_r64_imm8 .rcx 1),
  jmp_near_label "dist_pow_loop",
  label "dist_pow_done",

  -- baseDist = (p << 1) + 1 + (if (d & 1) != 0 then p else 0)
  instr (mov_r64 .rcx .rdx),
  instr (shl_r64_imm8 .rcx 1),
  instr (add_r64_imm8 .rcx 1),
  instr (mov_r64 .r9 .rax),
  instr (and_r64_imm8 .r9 1),
  instr (cmp_r64_imm8 .r9 0),
  je_near_label "dist_no_bit0",
  instr (add_r64 .rcx .rdx),
  label "dist_no_bit0",
  instr (mov_r64 .rdx .rcx),
  jmp_near_label "read_dist_extra",

  label "dist_lt_4",
  -- d < 4 (0..3): baseDist = d + 1, extraBits = 0
  instr (add_r64_imm8 .rax 1),
  instr (mov_r64 .rdx .rax),
  instr (xor_r32 .r8d .r8d),

  label "read_dist_extra",
  -- Read R8 bits LSB-first into RAX and add to RDX
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),     -- bitMask = 1
  label "dist_extra_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dist_extra_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dist_extra_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rcx .r15),
  instr (add_r64 .rcx .r12),
  instr (movzx_r64_mem8 .rsi .rcx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dist_extra_bit_ready",
  instr (mov_r64 .rcx .rsi),
  instr (and_r64_imm8 .rcx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  -- If bit is 1, or bitMask (R9) into RAX:
  instr (cmp_r64_imm8 .rcx 0),
  je_near_label "dist_skip_bit",
  instr (or_r64 .rax .r9),
  label "dist_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dist_extra_loop",
  label "dist_extra_done",
  instr (add_r64 .rdx .rax), -- RDX = final matchDist!

  -- Restore matchLen (RCX) from stack
  instr (pop_r64 .rcx),

  -- Copy matchLen (RCX) bytes from outBuf + outPos - matchDist to outBuf + outPos
  instr (xor_r32 .eax .eax),
  label "lz_copy_loop",
  instr (cmp_r64 .rax .rcx),
  jge_near_label "lz_copy_done",
  -- src byte at outBuf + r13 - rdx + rax:
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (sub_r64 .r9 .rdx),
  instr (add_r64 .r9 .rax),
  instr (movzx_r64_mem8 .r8 .r9 0),
  -- dst byte at outBuf + r13 + rax:
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (add_r64 .r9 .rax),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .rax 1),
  jmp_near_label "lz_copy_loop",
  label "lz_copy_done",
  instr (add_r64 .r13 .rcx),
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3000),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (cmp_r64_imm8 .rax 1),
  je_near_label "dynamic_symbol_loop",
  jmp_near_label "fixed_symbol_loop",

  -- =========================================================================
  -- Block Type 2: Dynamic Huffman Block Engine
  -- =========================================================================
  label "block_dynamic_huff",
  -- Set is_dynamic flag at [RSP + 3000] = 1
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3000),
  instr (mov_r32 .eax 1),
  instr (mov_mem8 .r9 .rax),

  -- 1. Read HLIT (5 bits LSB-first into [RSP + 0])
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r8d 5),
  label "dyn_read_hlit_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dyn_read_hlit_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_hlit_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_hlit_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_hlit_skip_bit",
  instr (or_r64 .rax .r9),
  label "dyn_hlit_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dyn_read_hlit_loop",
  label "dyn_read_hlit_done",
  instr (add_r64_imm32 .rax 257), -- nLit = HLIT + 257
  instr (mov_r64 .r9 .rsp),
  instr (mov_mem64_disp .r9 0 .rax),

  -- 2. Read HDIST (5 bits LSB-first into [RSP + 8])
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r8d 5),
  label "dyn_read_hdist_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dyn_read_hdist_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_hdist_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_hdist_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_hdist_skip_bit",
  instr (or_r64 .rax .r9),
  label "dyn_hdist_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dyn_read_hdist_loop",
  label "dyn_read_hdist_done",
  instr (add_r64_imm8 .rax 1), -- nDist = HDIST + 1
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 8),
  instr (mov_mem64_disp .r9 0 .rax),

  -- 3. Read HCLEN (4 bits LSB-first into [RSP + 16])
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r8d 4),
  label "dyn_read_hclen_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dyn_read_hclen_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_hclen_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_hclen_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_hclen_skip_bit",
  instr (or_r64 .rax .r9),
  label "dyn_hclen_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dyn_read_hclen_loop",
  label "dyn_read_hclen_done",
  instr (add_r64_imm8 .rax 4), -- nCLen = HCLEN + 4
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 16),
  instr (mov_mem64_disp .r9 0 .rax),

  -- 4. Clear 19 bytes at [RSP + 32]
  instr (xor_r32 .ecx .ecx),
  label "dyn_clear_cl_loop",
  instr (cmp_r64_imm8 .rcx 19),
  jge_near_label "dyn_clear_cl_done",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 32),
  instr (add_r64 .r9 .rcx),
  instr (xor_r32 .eax .eax),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_clear_cl_loop",
  label "dyn_clear_cl_done",

  -- 5. Read nCLen 3-bit lengths
  -- Permutation map: 0->16, 1->17, 2->18, 3->0, 4->8, 5->7, 6->9, 7->6, 8->10, 9->5, 10->11, 11->4, 12->12, 13->3, 14->13, 15->2, 16->14, 17->1, 18->15
  instr (xor_r32 .ecx .ecx), -- step index in 0..nCLen-1
  label "dyn_read_clens_loop",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 16),
  instr (movzx_r64_mem8 .rax .r9 0), -- RAX = nCLen
  instr (cmp_r64 .rcx .rax),
  jge_near_label "dyn_read_clens_done",

  -- Read 3 bits LSB-first into R8
  instr (xor_r32 .r8d .r8d),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r10d 3),
  label "dyn_clen_3bit_loop",
  instr (cmp_r64_imm8 .r10 0),
  je_near_label "dyn_clen_3bit_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_clen_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_clen_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_clen_skip_bit",
  instr (or_r64 .r8 .r9),
  label "dyn_clen_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r10 1),
  jmp_near_label "dyn_clen_3bit_loop",
  label "dyn_clen_3bit_done",

  -- Map step RCX to permutation index RDX
  instr (mov_r64 .rax .rcx),
  -- Hardcoded permutation check for RCX in 0..18
  instr (mov_r32 .edx 16),
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 17),
  instr (cmp_r64_imm8 .rax 1),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 18),
  instr (cmp_r64_imm8 .rax 2),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 0),
  instr (cmp_r64_imm8 .rax 3),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 8),
  instr (cmp_r64_imm8 .rax 4),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 7),
  instr (cmp_r64_imm8 .rax 5),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 9),
  instr (cmp_r64_imm8 .rax 6),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 6),
  instr (cmp_r64_imm8 .rax 7),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 10),
  instr (cmp_r64_imm8 .rax 8),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 5),
  instr (cmp_r64_imm8 .rax 9),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 11),
  instr (cmp_r64_imm8 .rax 10),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 4),
  instr (cmp_r64_imm8 .rax 11),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 12),
  instr (cmp_r64_imm8 .rax 12),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 3),
  instr (cmp_r64_imm8 .rax 13),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 13),
  instr (cmp_r64_imm8 .rax 14),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 2),
  instr (cmp_r64_imm8 .rax 15),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 14),
  instr (cmp_r64_imm8 .rax 16),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 1),
  instr (cmp_r64_imm8 .rax 17),
  je_near_label "dyn_perm_mapped",
  instr (mov_r32 .edx 15),

  label "dyn_perm_mapped",
  -- Write R8 (3-bit len) to [RSP + 32 + RDX]
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 32),
  instr (add_r64 .r9 .rdx),
  instr (mov_mem8 .r9 .r8),

  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_read_clens_loop",
  label "dyn_read_clens_done",

  -- 6. Build Canonical Table for Code Lengths at [RSP + 64] (19 entries * 4 bytes: 2 bytes code, 1 byte len, 1 byte 0)
  instr (xor_r32 .ecx .ecx),
  label "dyn_clear_cl_tbl",
  instr (cmp_r64_imm8 .rcx 19),
  jge_near_label "dyn_clear_cl_tbl_done",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 64),
  instr (mov_r64 .rax .rcx),
  instr (shl_r64_imm8 .rax 2),
  instr (add_r64 .r9 .rax),
  instr (xor_r32 .eax .eax),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r9 1),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r9 1),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_clear_cl_tbl",
  label "dyn_clear_cl_tbl_done",

  -- Canonical code assignment for lengths L in 1..7:
  instr (xor_r32 .r8d .r8d), -- code = 0
  instr (mov_r32 .r10d 1),   -- L = 1
  label "dyn_cl_assign_L_loop",
  instr (cmp_r64_imm8 .r10 7),
  ja_near_label "dyn_cl_assign_L_done",

  instr (xor_r32 .ecx .ecx), -- s = 0..18
  label "dyn_cl_assign_s_loop",
  instr (cmp_r64_imm8 .rcx 19),
  jge_near_label "dyn_cl_assign_s_done",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 32),
  instr (add_r64 .r9 .rcx),
  instr (movzx_r64_mem8 .rax .r9 0), -- RAX = cl_lens[s]
  instr (cmp_r64 .rax .r10),
  jne_near_label "dyn_cl_skip_s",

  -- Store code (R8) and len (R10) at [RSP + 64 + s*4]
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 64),
  instr (mov_r64 .rax .rcx),
  instr (shl_r64_imm8 .rax 2),
  instr (add_r64 .r9 .rax),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .r9 1),
  instr (mov_r64 .rax .r8),
  instr (shr_r64_imm8 .rax 8),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r9 1),
  instr (mov_mem8 .r9 .r10), -- len

  instr (add_r64_imm8 .r8 1), -- code += 1

  label "dyn_cl_skip_s",
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_cl_assign_s_loop",
  label "dyn_cl_assign_s_done",

  instr (shl_r64_imm8 .r8 1), -- code <<= 1
  instr (add_r64_imm8 .r10 1),
  jmp_near_label "dyn_cl_assign_L_loop",
  label "dyn_cl_assign_L_done",

  -- 7. Decode (nLit + nDist) Code Lengths into [RSP + 256]
  instr (mov_reg64_mem64_disp .rax .rsp 0), -- RAX = nLit
  instr (mov_reg64_mem64_disp .rdx .rsp 8), -- RDX = nDist
  instr (add_r64 .rax .rdx),                -- RAX = total = nLit + nDist
  instr (push_r64 .rax),                    -- save total on stack

  instr (xor_r32 .ecx .ecx),                -- cur = 0
  label "dyn_decode_lens_loop",
  instr (mov_reg64_mem64_disp .rax .rsp 0), -- RAX = total (from top of stack)
  instr (cmp_r64 .rcx .rax),
  jge_near_label "dyn_decode_lens_done",

  -- Decode 1 symbol from code-length tree into R8 (MSB-first bit search)
  instr (xor_r32 .eax .eax), -- bitVal = 0
  instr (xor_r32 .r8d .r8d), -- bitLen = 0
  label "dyn_read_cl_tree_bit",
  instr (cmp_r64_imm8 .r8 7),
  ja_near_label "decompress_err",

  -- Read 1 bit into RDX:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_cl_tree_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_cl_tree_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .rax .rdx),
  instr (add_r64_imm8 .r8 1),

  -- Search symbol s in 0..18:
  instr (xor_r32 .edx .edx),
  label "dyn_match_cl_s",
  instr (cmp_r64_imm8 .rdx 19),
  jge_near_label "dyn_read_cl_tree_bit",

  -- Load table entry [RSP + 72 + s*4] (stack has 1 push)
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm8 .r9 72),
  instr (mov_r64 .r10 .rdx),
  instr (shl_r64_imm8 .r10 2),
  instr (add_r64 .r9 .r10),
  instr (movzx_r64_mem8 .r11 .r9 2), -- len
  instr (cmp_r64 .r11 .r8),
  jne_near_label "dyn_cl_next_s",
  instr (movzx_r64_mem8 .r10 .r9 0), -- code low
  instr (movzx_r64_mem8 .r11 .r9 1), -- code high
  instr (shl_r64_imm8 .r11 8),
  instr (or_r64 .r10 .r11),
  instr (cmp_r64 .r10 .rax),
  je_near_label "dyn_cl_symbol_found",

  label "dyn_cl_next_s",
  instr (add_r64_imm8 .rdx 1),
  jmp_near_label "dyn_match_cl_s",

  label "dyn_cl_symbol_found",
  -- Symbol is in RDX (0..18)
  instr (cmp_r64_imm8 .rdx 16),
  jae_near_label "dyn_cl_repeat_symbol",

  -- Symbol in 0..15: write to [RSP + 264 + cur] (stack has 1 push)
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 264),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .rdx),
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_decode_lens_loop",

  label "dyn_cl_repeat_symbol",
  instr (cmp_r64_imm8 .rdx 16),
  jne_near_label "dyn_cl_sym_17_18",

  -- Symbol 16: Repeat previous length (3 + 2 bits)
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r8d 2),
  label "dyn_sym16_extra_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dyn_sym16_extra_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_sym16_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_sym16_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_sym16_skip_bit",
  instr (or_r64 .rax .r9),
  label "dyn_sym16_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dyn_sym16_extra_loop",
  label "dyn_sym16_extra_done",
  instr (add_r64_imm8 .rax 3), -- count = 3 + extra

  -- prev = [RSP + 264 + cur - 1]
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 264),
  instr (add_r64 .r9 .rcx),
  instr (sub_r64_imm8 .r9 1),
  instr (movzx_r64_mem8 .rdx .r9 0), -- RDX = prev

  -- Fill count (RAX) times:
  label "dyn_sym16_fill_loop",
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "dyn_decode_lens_loop",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 264),
  instr (add_r64 .r9 .rcx),
  instr (mov_mem8 .r9 .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (sub_r64_imm8 .rax 1),
  jmp_near_label "dyn_sym16_fill_loop",

  label "dyn_cl_sym_17_18",
  instr (cmp_r64_imm8 .rdx 17),
  jne_near_label "dyn_cl_sym_18",

  -- Symbol 17: Repeat 0 (3 + 3 bits)
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r8d 3),
  label "dyn_sym17_extra_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dyn_sym17_extra_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_sym17_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_sym17_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_sym17_skip_bit",
  instr (or_r64 .rax .r9),
  label "dyn_sym17_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dyn_sym17_extra_loop",
  label "dyn_sym17_extra_done",
  instr (add_r64_imm8 .rax 3), -- count = 3 + extra

  -- Fill 0 count (RAX) times:
  label "dyn_sym17_fill_loop",
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "dyn_decode_lens_loop",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 264),
  instr (add_r64 .r9 .rcx),
  instr (xor_r32 .edx .edx),
  instr (mov_mem8 .r9 .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (sub_r64_imm8 .rax 1),
  jmp_near_label "dyn_sym17_fill_loop",

  label "dyn_cl_sym_18",
  -- Symbol 18: Repeat 0 (11 + 7 bits)
  instr (xor_r32 .eax .eax),
  instr (mov_r32 .r9d 1),
  instr (mov_r32 .r8d 7),
  label "dyn_sym18_extra_loop",
  instr (cmp_r64_imm8 .r8 0),
  je_near_label "dyn_sym18_extra_done",
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_sym18_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_sym18_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (cmp_r64_imm8 .rdx 0),
  je_near_label "dyn_sym18_skip_bit",
  instr (or_r64 .rax .r9),
  label "dyn_sym18_skip_bit",
  instr (shl_r64_imm8 .r9 1),
  instr (sub_r64_imm8 .r8 1),
  jmp_near_label "dyn_sym18_extra_loop",
  label "dyn_sym18_extra_done",
  instr (add_r64_imm8 .rax 11), -- count = 11 + extra

  -- Fill 0 count (RAX) times:
  label "dyn_sym18_fill_loop",
  instr (cmp_r64_imm8 .rax 0),
  je_near_label "dyn_decode_lens_loop",
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 264),
  instr (add_r64 .r9 .rcx),
  instr (xor_r32 .edx .edx),
  instr (mov_mem8 .r9 .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (sub_r64_imm8 .rax 1),
  jmp_near_label "dyn_sym18_fill_loop",

  label "dyn_decode_lens_done",
  instr (pop_r64 .rax), -- remove total from stack

  -- 8. Build Canonical Literal/Length Table at [RSP + 1024] (nLit entries * 4 bytes)
  instr (xor_r32 .r8d .r8d), -- code = 0
  instr (mov_r32 .r10d 1),   -- L = 1
  label "dyn_lit_assign_L_loop",
  instr (cmp_r64_imm8 .r10 15),
  ja_near_label "dyn_lit_assign_L_done",

  instr (xor_r32 .ecx .ecx), -- s = 0..nLit-1
  label "dyn_lit_assign_s_loop",
  instr (mov_reg64_mem64_disp .rax .rsp 0), -- RAX = nLit
  instr (cmp_r64 .rcx .rax),
  jge_near_label "dyn_lit_assign_s_done",

  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 256),
  instr (add_r64 .r9 .rcx),
  instr (movzx_r64_mem8 .rax .r9 0), -- RAX = lit_lens[s]
  instr (cmp_r64 .rax .r10),
  jne_near_label "dyn_lit_skip_s",

  -- Store code (R8) and len (R10) at [RSP + 1024 + s*4]
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 1024),
  instr (mov_r64 .rax .rcx),
  instr (shl_r64_imm8 .rax 2),
  instr (add_r64 .r9 .rax),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .r9 1),
  instr (mov_r64 .rax .r8),
  instr (shr_r64_imm8 .rax 8),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r9 1),
  instr (mov_mem8 .r9 .r10), -- len

  instr (add_r64_imm8 .r8 1), -- code += 1

  label "dyn_lit_skip_s",
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_lit_assign_s_loop",
  label "dyn_lit_assign_s_done",

  instr (shl_r64_imm8 .r8 1), -- code <<= 1
  instr (add_r64_imm8 .r10 1),
  jmp_near_label "dyn_lit_assign_L_loop",
  label "dyn_lit_assign_L_done",

  -- 9. Build Canonical Distance Table at [RSP + 2560] (nDist entries * 4 bytes)
  instr (xor_r32 .r8d .r8d), -- code = 0
  instr (mov_r32 .r10d 1),   -- L = 1
  label "dyn_dist_assign_L_loop",
  instr (cmp_r64_imm8 .r10 15),
  ja_near_label "dyn_dist_assign_L_done",

  instr (xor_r32 .ecx .ecx), -- d = 0..nDist-1
  label "dyn_dist_assign_d_loop",
  instr (mov_reg64_mem64_disp .rax .rsp 8), -- RAX = nDist
  instr (cmp_r64 .rcx .rax),
  jge_near_label "dyn_dist_assign_d_done",

  instr (mov_reg64_mem64_disp .rdx .rsp 0), -- RDX = nLit
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 256),
  instr (add_r64 .r9 .rdx),
  instr (add_r64 .r9 .rcx),
  instr (movzx_r64_mem8 .rax .r9 0), -- RAX = dist_lens[d]
  instr (cmp_r64 .rax .r10),
  jne_near_label "dyn_dist_skip_d",

  -- Store code (R8) and len (R10) at [RSP + 2560 + d*4]
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 2560),
  instr (mov_r64 .rax .rcx),
  instr (shl_r64_imm8 .rax 2),
  instr (add_r64 .r9 .rax),
  instr (mov_mem8 .r9 .r8),
  instr (add_r64_imm8 .r9 1),
  instr (mov_r64 .rax .r8),
  instr (shr_r64_imm8 .rax 8),
  instr (mov_mem8 .r9 .rax),
  instr (add_r64_imm8 .r9 1),
  instr (mov_mem8 .r9 .r10), -- len

  instr (add_r64_imm8 .r8 1), -- code += 1

  label "dyn_dist_skip_d",
  instr (add_r64_imm8 .rcx 1),
  jmp_near_label "dyn_dist_assign_d_loop",
  label "dyn_dist_assign_d_done",

  instr (shl_r64_imm8 .r8 1), -- code <<= 1
  instr (add_r64_imm8 .r10 1),
  jmp_near_label "dyn_dist_assign_L_loop",
  label "dyn_dist_assign_L_done",

  -- =========================================================================
  -- 10. Decode Dynamic Payload Symbols
  -- =========================================================================
  label "dynamic_symbol_loop",
  -- Read bits MSB-first into RAX, search in lit_tree [RSP + 1024]
  instr (xor_r32 .eax .eax), -- bitVal = 0
  instr (xor_r32 .r8d .r8d), -- bitLen = 0
  label "dyn_read_lit_bit",
  instr (cmp_r64_imm8 .r8 15),
  ja_near_label "decompress_err",

  -- Read 1 bit into RDX:
  instr (cmp_r64_imm8 .rdi 0),
  jne_near_label "dyn_lit_bit_ready",
  instr (cmp_r64 .r12 .rbx),
  jge_near_label "decompress_err",
  instr (mov_r64 .rdx .r15),
  instr (add_r64 .rdx .r12),
  instr (movzx_r64_mem8 .rsi .rdx 0),
  instr (add_r64_imm8 .r12 1),
  instr (mov_r32 .edi 8),
  label "dyn_lit_bit_ready",
  instr (mov_r64 .rdx .rsi),
  instr (and_r64_imm8 .rdx 1),
  instr (shr_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rdi 1),
  instr (shl_r64_imm8 .rax 1),
  instr (or_r64 .rax .rdx),
  instr (add_r64_imm8 .r8 1),

  -- Search symbol s in 0..nLit-1:
  instr (xor_r32 .edx .edx),
  label "dyn_match_lit_s",
  instr (mov_reg64_mem64_disp .r11 .rsp 0), -- R11 = nLit
  instr (cmp_r64 .rdx .r11),
  jge_near_label "dyn_read_lit_bit",

  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 1024),
  instr (mov_r64 .r10 .rdx),
  instr (shl_r64_imm8 .r10 2),
  instr (add_r64 .r9 .r10),
  instr (movzx_r64_mem8 .r11 .r9 2), -- len
  instr (cmp_r64 .r11 .r8),
  jne_near_label "dyn_lit_next_s",
  instr (movzx_r64_mem8 .r10 .r9 0), -- code low
  instr (movzx_r64_mem8 .r11 .r9 1), -- code high
  instr (shl_r64_imm8 .r11 8),
  instr (or_r64 .r10 .r11),
  instr (cmp_r64 .r10 .rax),
  je_near_label "dyn_lit_symbol_found",

  label "dyn_lit_next_s",
  instr (add_r64_imm8 .rdx 1),
  jmp_near_label "dyn_match_lit_s",

  label "dyn_lit_symbol_found",
  -- Symbol is in RDX (0..285)
  instr (cmp_r64_imm32 .rdx 256),
  jae_near_label "dyn_lit_ge_256",

  -- Literal byte in RDX: write to [R14 + R13]
  instr (mov_r64 .r9 .r14),
  instr (add_r64 .r9 .r13),
  instr (mov_mem8 .r9 .rdx),
  instr (add_r64_imm8 .r13 1),
  jmp_near_label "dynamic_symbol_loop",

  label "dyn_lit_ge_256",
  instr (cmp_r64_imm32 .rdx 256),
  jne_near_label "dyn_process_match_length",

  -- Symbol 256 (EOB): Check BFINAL from stack
  instr (mov_r64 .r9 .rsp),
  instr (add_r64_imm32 .r9 3001),
  instr (movzx_r64_mem8 .rax .r9 0),
  instr (cmp_r64_imm8 .rax 1),
  je_near_label "decompress_finish",
  jmp_near_label "decompress_block_loop",

  label "dyn_process_match_length",
  -- Symbol in RDX (257..285) -> compute length, decode distance from dist_tree, and copy!
  instr (mov_r64 .rax .rdx),
  jmp_near_label "process_length_symbol",

  -- =========================================================================
  -- Finish & CRC Calculation
  -- =========================================================================
  label "decompress_finish",
  -- Calculate CRC-32 of decompressed data in outBuf (r14, len in r13)
  instr (mov_r64 .rcx .r14),
  instr (mov_r64 .rdx .r13),
  call_label "zlib_crc32",

  -- Return 0 in RAX
  instr (xor_r32 .eax .eax),
  instr (add_r64_imm32 .rsp 4096),
  instr ret_op,

  label "decompress_err",
  instr (mov_r32 .eax 1),
  instr (add_r64_imm32 .rsp 4096),
  instr ret_op
]


end Stdlib.Zlib.X86_64

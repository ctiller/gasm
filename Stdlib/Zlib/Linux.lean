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
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.X86_64.Assembler
import Stdlib.Zlib.Spec
import Stdlib.Zlib.X86_64

namespace Stdlib.Zlib.Linux

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Stdlib.Zlib.X86_64

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Standard 10-byte RFC 1952 GZIP header bytes for Linux binary data sections. -/
def gzipHeaderBytes : ByteArray :=
  Stdlib.Zlib.X86_64.gzipHeaderBytes

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Complete Linux executable stream harness for GZIP compression.
    Allocates heap via sys_mmap, streams uncompressed input from stdin via sys_read,
    calls GZIP compressor subroutine, emits compressed stream to stdout via sys_write,
    frees heap via sys_munmap, and terminates via sys_exit(0). -/
def gzipStreamSymbolicProgram : List SymbolicInstr := [
  instr (sub_rsp 120),

  -- 1. sys_mmap(NULL, 16MB, PROT_READ|PROT_WRITE (3), MAP_PRIVATE|MAP_ANONYMOUS (0x22), -1, 0)
  instr (mov_r32 .eax 9),
  instr (xor_r32 .edi .edi),
  instr (mov_r32 .esi 0x01000000),
  instr (mov_r32 .edx 3),
  instr (mov_r32 .r10d 0x22),
  instr (mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF),
  instr (xor_r32 .r9d .r9d),
  instr syscall_op,
  instr (mov_r64 .r15 .rax),

  -- 2. Read stdin into inBuf (r15) in a loop until EOF (rax <= 0)
  instr (xor_r32 .ebx .ebx),

  label "gzip_read_loop",
  -- Remaining buffer capacity = 8MB - rbx
  instr (mov_r32 .edx 0x00800000),
  instr (sub_r64 .rdx .rbx),
  jle_near_label "gzip_read_done",

  -- sys_read(0, inBuf + rbx, remaining)
  instr (xor_r32 .edi .edi),
  instr (mov_r64 .rsi .r15),
  instr (add_r64 .rsi .rbx),
  instr (mov_r32 .eax 0),
  instr syscall_op,

  -- If rax <= 0, EOF or read error: finish ingestion
  instr (cmp_r64_imm8 .rax 0),
  jle_near_label "gzip_read_done",

  instr (add_r64 .rbx .rax),
  jmp_near_label "gzip_read_loop",

  label "gzip_read_done",

  -- 3. outBuf = inBuf + 8MB (r14)
  instr (mov_r64 .r14 .r15),
  instr (add_r64_imm32 .r14 0x00800000),

  -- 4. Call gzip compressor subroutine
  call_label "zlib_compress",

  -- 5. sys_write(1 (stdout), outBuf (r14), totalSize (r13))
  instr (mov_r32 .edi 1),
  instr (mov_r64 .rsi .r14),
  instr (mov_r64 .rdx .r13),
  instr (mov_r32 .eax 1),
  instr syscall_op,

  -- 6. sys_munmap(inBuf (r15), 16MB)
  instr (mov_r64 .rdi .r15),
  instr (mov_r32 .esi 0x01000000),
  instr (mov_r32 .eax 11),
  instr syscall_op,

  -- 7. sys_exit(0)
  instr (xor_r32 .edi .edi),
  instr (mov_r32 .eax 60),
  instr syscall_op,

  -- Subroutine labels:
  label "zlib_crc32"
] ++ crc32SymbolicProgram ++ [
  label "zlib_compress"
] ++ gzipCompressSymbolicProgram

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Complete Linux executable stream harness for GUNZIP decompression.
    Allocates heap via sys_mmap, streams compressed GZIP input from stdin via sys_read,
    calls GZIP decompressor subroutine, emits uncompressed stream to stdout via sys_write,
    frees heap via sys_munmap, and terminates via sys_exit(0). -/
def gunzipStreamSymbolicProgram : List SymbolicInstr := [
  instr (sub_rsp 120),

  -- 1. sys_mmap(NULL, 16MB, PROT_READ|PROT_WRITE (3), MAP_PRIVATE|MAP_ANONYMOUS (0x22), -1, 0)
  instr (mov_r32 .eax 9),
  instr (xor_r32 .edi .edi),
  instr (mov_r32 .esi 0x01000000),
  instr (mov_r32 .edx 3),
  instr (mov_r32 .r10d 0x22),
  instr (mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF),
  instr (xor_r32 .r9d .r9d),
  instr syscall_op,
  instr (mov_r64 .r15 .rax),

  -- 2. Read stdin into inBuf (r15) in a loop until EOF (rax <= 0)
  instr (xor_r32 .ebx .ebx),

  label "gunzip_read_loop",
  -- Remaining buffer capacity = 8MB - rbx
  instr (mov_r32 .edx 0x00800000),
  instr (sub_r64 .rdx .rbx),
  jle_near_label "gunzip_read_done",

  -- sys_read(0, inBuf + rbx, remaining)
  instr (xor_r32 .edi .edi),
  instr (mov_r64 .rsi .r15),
  instr (add_r64 .rsi .rbx),
  instr (mov_r32 .eax 0),
  instr syscall_op,

  -- If rax <= 0, EOF or read error: finish ingestion
  instr (cmp_r64_imm8 .rax 0),
  jle_near_label "gunzip_read_done",

  instr (add_r64 .rbx .rax),
  jmp_near_label "gunzip_read_loop",

  label "gunzip_read_done",

  -- 3. outBuf = inBuf + 8MB (r14)
  instr (mov_r64 .r14 .r15),
  instr (add_r64_imm32 .r14 0x00800000),

  -- 4. Call gzip decompressor subroutine
  call_label "zlib_decompress",

  -- 5. Check return code (RAX == 0)
  instr (cmp_r64_imm8 .rax 0),
  jne_near_label "gunzip_fail",

  -- 6. sys_write(1 (stdout), outBuf (r14), decompressedLen (r13))
  instr (mov_r32 .edi 1),
  instr (mov_r64 .rsi .r14),
  instr (mov_r64 .rdx .r13),
  instr (mov_r32 .eax 1),
  instr syscall_op,

  -- 7. sys_munmap(inBuf (r15), 16MB)
  instr (mov_r64 .rdi .r15),
  instr (mov_r32 .esi 0x01000000),
  instr (mov_r32 .eax 11),
  instr syscall_op,

  -- 8. sys_exit(0)
  instr (xor_r32 .edi .edi),
  instr (mov_r32 .eax 60),
  instr syscall_op,

  label "gunzip_fail",
  instr (mov_r32 .edi 1),
  instr (mov_r32 .eax 60),
  instr syscall_op,

  -- Subroutine labels:
  label "zlib_crc32"
] ++ crc32SymbolicProgram ++ [
  label "zlib_decompress"
] ++ gzipDecompressSymbolicProgram

end Stdlib.Zlib.Linux

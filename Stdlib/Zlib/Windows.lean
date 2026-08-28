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

import Stdlib.Zlib.X86_64

namespace Stdlib.Zlib.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Stdlib.Zlib.X86_64

export Stdlib.Zlib.X86_64 (gzipHeaderBytes crc32SymbolicProgram gzipCompressSymbolicProgram gzipDecompressSymbolicProgram)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Complete Windows executable stream harness for GZIP compression.
    Allocates heap, streams input from stdin, calls GZIP compressor subroutine,
    emits compressed stream to stdout, frees heap, and terminates. -/
def gzipStreamSymbolicProgram : List SymbolicInstr := [
  instr (sub_rsp 120),

  -- 1. Obtain stdin: GetStdHandle(STD_INPUT_HANDLE = -10)
  instr (mov_r32 .ecx 0xFFFFFFF6),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax),

  -- 2. VirtualAlloc(NULL, 16777216 (16MB), MEM_COMMIT|MEM_RESERVE = 0x3000, PAGE_READWRITE = 0x04)
  instr (xor_r32 .ecx .ecx),
  instr (mov_r32 .edx 0x01000000),
  instr (mov_r32 .r8d 0x3000),
  instr (mov_r32 .r9d 0x04),
  call_import "VirtualAlloc",
  instr (mov_r64 .r15 .rax),

  -- 3. ReadFile(hStdin, inBuf (r15), 8388608 (8MB), &bytesRead, NULL)
  instr (mov_r64 .rcx .r12),
  instr (mov_r64 .rdx .r15),
  instr (mov_r32 .r8d 0x00800000),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "ReadFile",
  instr (mov_r32_rsp .ebx 0x28),

  -- 4. outBuf = inBuf + 8388608 (r14)
  instr (mov_r64 .r14 .r15),
  instr (add_r64_imm32 .r14 0x00800000),

  -- 5. Call gzip compressor subroutine
  call_label "zlib_compress",

  -- 6. Get stdout: GetStdHandle(STD_OUTPUT_HANDLE = -11)
  instr (mov_r32 .ecx 0xFFFFFFF5),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax),

  -- 7. WriteFile(hStdout, outBuf (r14), totalSize (r13), &written, NULL)
  instr (mov_r64 .rcx .r12),
  instr (mov_r64 .rdx .r14),
  instr (mov_r64 .r8 .r13),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "WriteFile",

  -- 8. VirtualFree(baseAddr (r15), 0, MEM_RELEASE = 0x8000)
  instr (mov_r64 .rcx .r15),
  instr (xor_r32 .edx .edx),
  instr (mov_r32 .r8d 0x8000),
  call_import "VirtualFree",

  -- 9. ExitProcess(0)
  instr (xor_r32 .ecx .ecx),
  call_import "ExitProcess",

  -- Subroutine labels:
  label "zlib_crc32"
] ++ crc32SymbolicProgram ++ [
  label "zlib_compress"
] ++ gzipCompressSymbolicProgram

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Complete Windows executable stream harness for GUNZIP decompression.
    Allocates heap, streams compressed GZIP input from stdin, calls GZIP decompressor,
    emits uncompressed stream to stdout, frees heap, and terminates. -/
def gunzipStreamSymbolicProgram : List SymbolicInstr := [
  instr (sub_rsp 120),

  -- 1. Obtain stdin: GetStdHandle(STD_INPUT_HANDLE = -10)
  instr (mov_r32 .ecx 0xFFFFFFF6),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax),

  -- 2. VirtualAlloc(NULL, 16777216 (16MB), MEM_COMMIT|MEM_RESERVE = 0x3000, PAGE_READWRITE = 0x04)
  instr (xor_r32 .ecx .ecx),
  instr (mov_r32 .edx 0x01000000),
  instr (mov_r32 .r8d 0x3000),
  instr (mov_r32 .r9d 0x04),
  call_import "VirtualAlloc",
  instr (mov_r64 .r15 .rax),

  -- 3. ReadFile(hStdin, inBuf (r15), 8388608 (8MB), &bytesRead, NULL)
  instr (mov_r64 .rcx .r12),
  instr (mov_r64 .rdx .r15),
  instr (mov_r32 .r8d 0x00800000),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "ReadFile",
  instr (mov_r32_rsp .ebx 0x28),

  -- 4. outBuf = inBuf + 8388608 (r14)
  instr (mov_r64 .r14 .r15),
  instr (add_r64_imm32 .r14 0x00800000),

  -- 5. Call gzip decompressor subroutine
  call_label "zlib_decompress",

  -- 6. Check return code (RAX == 0)
  instr (cmp_r64_imm8 .rax 0),
  jne_near_label "gunzip_fail",

  -- 7. Get stdout: GetStdHandle(STD_OUTPUT_HANDLE = -11)
  instr (mov_r32 .ecx 0xFFFFFFF5),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax),

  -- 8. WriteFile(hStdout, outBuf (r14), decompressedLen (r13), &written, NULL)
  instr (mov_r64 .rcx .r12),
  instr (mov_r64 .rdx .r14),
  instr (mov_r64 .r8 .r13),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "WriteFile",

  -- 9. VirtualFree(baseAddr (r15), 0, MEM_RELEASE = 0x8000)
  instr (mov_r64 .rcx .r15),
  instr (xor_r32 .edx .edx),
  instr (mov_r32 .r8d 0x8000),
  call_import "VirtualFree",

  -- 10. ExitProcess(0)
  instr (xor_r32 .ecx .ecx),
  call_import "ExitProcess",

  label "gunzip_fail",
  instr (mov_r32 .ecx 1),
  call_import "ExitProcess",

  -- Subroutine labels:
  label "zlib_crc32"
] ++ crc32SymbolicProgram ++ [
  label "zlib_decompress"
] ++ gzipDecompressSymbolicProgram

end Stdlib.Zlib.Windows

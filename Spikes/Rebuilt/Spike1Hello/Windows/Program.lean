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

import Spikes.Rebuilt.Spike1Hello.Spec
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.Linker

/-!
# Rebuilt Spike 1 Windows realization

This is a clean-slate lowering of `writeAll message orFatal`. Unlike the old spike, it checks both
provider calls, treats both null and `INVALID_HANDLE_VALUE` as missing stdout, validates the
provider's accepted count, and retries every short or zero write. The symbolic program remains an
experimental artifact until the relational target execution is connected and reviewed.
-/

namespace Spikes.Rebuilt.Spike1Hello.Windows

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows.Linker

/-- The first provider profile is intentionally narrow. Admission must carry a live writable handle
opened for synchronous I/O. Handles requiring `OVERLAPPED`, including `ERROR_IO_PENDING`
completion, are not implementations of this profile and must not be classified as write failure. -/
inductive SelectedStdoutProfile where
  | synchronousWritable
deriving DecidableEq, Repr

def selectedStdoutProfile : SelectedStdoutProfile :=
  .synchronousWritable

def messageBytes : ByteArray :=
  "Hello, World!\n".toUTF8

theorem messageBytes_exact : messageBytes.toList = message := by
  rfl

/-- Register convention: `r12` stdout handle, `r13` next byte, `r14` remaining byte count, and
`r15` the most recent provider-accepted count. The 56-byte frame contains Win64 shadow space and
the `lpNumberOfBytesWritten` slot at `rsp+0x28`. -/
def symbolicProgram : List SymbolicInstr := [
  instr (sub_rsp 56),
  instr (mov_r32 .ecx 0xFFFFFFF5),
  call_import "GetStdHandle",
  instr (cmp_r64_imm8 .rax 0),
  je_label "fatal",
  instr (cmp_r64_imm8 .rax 0xFF),
  je_label "fatal",
  instr (mov_r64 .r12 .rax),
  lea_data .r13 "message",
  instr (mov_r32 .r14d messageBytes.size.toUInt32),

  label "write",
  instr (mov_r64 .rcx .r12),
  instr (mov_r64 .rdx .r13),
  instr (mov_r64 .r8 .r14),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "WriteFile",
  instr (cmp_r64_imm8 .rax 0),
  je_label "fatal",
  instr (mov_r32_rsp .r15d 0x28),
  instr (cmp_r64 .r15 .r14),
  ja_label "fatal",
  instr (add_r64 .r13 .r15),
  instr (sub_r64 .r14 .r15),
  instr (cmp_r64_imm8 .r14 0),
  jne_label "write",

  instr (mov_r32 .ecx 0),
  call_import "ExitProcess",

  label "fatal",
  instr (mov_r32 .ecx 1),
  call_import "ExitProcess"
]

def linked :=
  linkWindowsProgram symbolicProgram [("message", messageBytes)]
    ["GetStdHandle", "WriteFile", "ExitProcess"]

def instructions : List X86_64Instr :=
  linked.instructions

def executable :=
  linked.executable

theorem instruction_count : instructions.length = 29 := by
  decide

theorem imports_exact : executable.imports.map (fun imported => imported.symbolName) =
    ["GetStdHandle", "WriteFile", "ExitProcess"] := by
  rfl

end Spikes.Rebuilt.Spike1Hello.Windows

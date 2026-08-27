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
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Linker

namespace Spikes.Spike1Hello.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Pure byte sequence for the 'Hello, World!\r\n' message placed in .rdata. -/
def helloMessage : ByteArray :=
  "Hello, World!\r\n".toUTF8

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Symbolic program definition for Spike 1 (Windows Hello World). -/
def spike1SymbolicProgram : List SymbolicInstr := [
  -- 1. Allocate 56-byte stack frame (32-byte shadow space + 16-byte alignment + 8-byte local for lpBytesWritten)
  instr (sub_rsp 56),

  -- 2. Pass STD_OUTPUT_HANDLE (-11) to GetStdHandle
  instr (mov_r32 .ecx 0xFFFFFFF5),
  call_import "GetStdHandle",

  -- 3. Prepare arguments for WriteFile(hConsole, &helloMessage, 15, &bytesWritten, NULL)
  instr (mov_r64 .rcx .rax),
  lea_data .rdx "helloMessage",
  instr (mov_r32 .r8d 15),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "WriteFile",

  -- 4. Exit cleanly with ExitProcess(0)
  instr (xor_r32 .ecx .ecx),
  call_import "ExitProcess"
]

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Linked binary program artifact for Spike 1. -/
def spike1Linked : LinkedWindowsProgram :=
  linkWindowsProgram spike1SymbolicProgram [("helloMessage", helloMessage)]

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Lowered concrete machine instruction sequence for Spike 1. -/
def spike1Instructions : List X86_64Instr :=
  spike1Linked.instructions

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Complete Windows executable specification for Spike 1. -/
def spike1Executable : WindowsExecutable :=
  spike1Linked.executable

end Spikes.Spike1Hello.Windows

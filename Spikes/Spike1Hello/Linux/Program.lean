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
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Linux.ELFFormat
import Gasm.Targets.Linux.Linker

namespace Spikes.Spike1Hello.Linux

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Linux

/- REF: docs/TARGETS/LINUX.md#spikes-verification -/
/-- Pure byte sequence for the 'Hello, World!\n' message placed in .rodata. -/
def helloMessage : ByteArray :=
  "Hello, World!\n".toUTF8

/- REF: docs/TARGETS/LINUX.md#spikes-verification -/
/-- Symbolic program definition for Spike 1 (Linux x86-64 Hello World). -/
def spike1SymbolicProgram : List SymbolicInstr := [
  -- 1. sys_write(1, &helloMessage, 14)
  instr (mov_r32 .eax 1),
  instr (mov_r32 .edi 1),
  lea_data .rsi "helloMessage",
  instr (mov_r32 .edx 14),
  instr syscall_op,

  -- 2. sys_exit(0)
  instr (xor_r32 .edi .edi),
  instr (mov_r32 .eax 60),
  instr syscall_op
]

/- REF: docs/TARGETS/LINUX.md#spikes-verification -/
/-- Linked binary program artifact for Linux Spike 1. -/
def spike1Linked : LinkedLinuxProgram :=
  linkLinuxProgramStatic spike1SymbolicProgram [("helloMessage", helloMessage)]

/- REF: docs/TARGETS/LINUX.md#spikes-verification -/
/-- Lowered concrete machine instruction sequence for Linux Spike 1. -/
def spike1Instructions : List X86_64Instr :=
  spike1Linked.instructions

/- REF: docs/TARGETS/LINUX.md#spikes-verification -/
/-- Complete Linux executable specification for Spike 1. -/
def spike1Executable : LinuxExecutable :=
  spike1Linked.executable

end Spikes.Spike1Hello.Linux

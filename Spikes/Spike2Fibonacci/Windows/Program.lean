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
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Linker
import Spikes.Spike2Fibonacci.Spec

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Symbolic 64-bit Fibonacci computation routine in x86-64 assembly with symbolic labels. -/
def fibIterSymbolicProgram : List SymbolicInstr := [
  instr (xor_r32 .eax .eax),
  instr (mov_r64_imm64 .rdx 1),
  label "loop_start",
  instr (cmp_r64_imm8 .rcx 0),
  je_label "done",
  instr (mov_r64 .r8 .rax),
  instr (add_r64 .r8 .rdx),
  instr (mov_r64 .rax .rdx),
  instr (mov_r64 .rdx .r8),
  instr (sub_r64_imm8 .rcx 1),
  jmp_label "loop_start",
  label "done",
  instr ret_op
]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Concrete instruction sequence for the iterative Fibonacci routine assembled from symbolic AST. -/
def fibIterInstructions : List X86_64Instr :=
  assembleProgram 0x1000 fibIterSymbolicProgram

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Symbolic main driver program for Spike 2:
    Executes a pure x86-64 hardware loop calculating all 90 Fibonacci numbers
    dynamically in CPU registers, dynamically formatting each line in stack RAM via hardware
    division/modulo itoa instructions, and outputting to standard output via Win32 WriteFile. -/
def spike2SymbolicProgram : List SymbolicInstr := [
  -- 1. Allocate 136-byte stack frame (maintaining 16-byte alignment before CALLs)
  instr (sub_rsp32 136),

  -- 2. Obtain standard output console handle
  instr (mov_r32 .ecx 0xFFFFFFF5),
  call_import "GetStdHandle",
  instr (mov_r64 .r12 .rax),

  -- 3. Initialize dynamic Fibonacci registers: i = 1, a = 1, b = 1
  instr (mov_r64_imm64 .r13 1),
  instr (mov_r64_imm64 .r14 1),
  instr (mov_r64_imm64 .r15 1),

  -- 4. Main loop header: for i = 1 to 90
  label "main_loop",
  instr (cmp_r64_imm8 .r13 91),
  jge_near_label "exit_loop",

  -- 5. Step 1: Write "Fib(" directly into stack buffer [rsp + 0x40]
  instr (mov_rsp_byte 0x40 0x46),
  instr (mov_rsp_byte 0x41 0x69),
  instr (mov_rsp_byte 0x42 0x62),
  instr (mov_rsp_byte 0x43 0x28),

  -- 6. Step 2: Format loop index i (in r13) into stack buffer via hardware division
  instr (cmp_r64_imm8 .r13 10),
  jge_label "two_digits_i",

  -- One-digit formatting (i < 10):
  instr (mov_r64 .rax .r13),
  instr (add_r64_imm8 .rax 0x30),
  instr (lea_rsp .rdi 0x44),
  instr (mov_mem8 .rdi .rax),
  instr (mov_rsp_byte 0x45 0x29),
  instr (mov_rsp_byte 0x46 0x20),
  instr (mov_rsp_byte 0x47 0x3D),
  instr (mov_rsp_byte 0x48 0x20),
  instr (lea_rsp .rdi 0x49),
  jmp_label "itoa_start",

  -- Two-digit formatting (i >= 10):
  label "two_digits_i",
  instr (mov_r64 .rax .r13),
  instr (mov_r64_imm64 .r10 10),
  instr (xor_r32 .edx .edx),
  instr (div_r64 .r10),
  instr (add_r64_imm8 .rax 0x30),
  instr (add_r64_imm8 .rdx 0x30),
  instr (lea_rsp .rdi 0x44),
  instr (mov_mem8 .rdi .rax),
  instr (lea_rsp .rdi 0x45),
  instr (mov_mem8 .rdi .rdx),
  instr (mov_rsp_byte 0x46 0x29),
  instr (mov_rsp_byte 0x47 0x20),
  instr (mov_rsp_byte 0x48 0x3D),
  instr (mov_rsp_byte 0x49 0x20),
  instr (lea_rsp .rdi 0x4A),

  -- 7. Step 3: Hardware itoa on 64-bit Fibonacci value in r14
  label "itoa_start",
  instr (mov_r64 .rax .r14),
  instr (mov_r64_imm64 .r10 10),
  instr (xor_r32 .ecx .ecx),

  -- Digit extraction loop:
  label "digit_extract_loop",
  instr (xor_r32 .edx .edx),
  instr (div_r64 .r10),
  instr (add_r64_imm8 .rdx 0x30),
  instr (push_r64 .rdx),
  instr (add_r64_imm8 .rcx 1),
  instr (cmp_r64_imm8 .rax 0),
  jne_label "digit_extract_loop",

  -- Digit pop and write loop:
  label "digit_write_loop",
  instr (pop_r64 .rdx),
  instr (mov_mem8 .rdi .rdx),
  instr (add_r64_imm8 .rdi 1),
  instr (sub_r64_imm8 .rcx 1),
  jne_label "digit_write_loop",

  -- 8. Step 4: Append "\r\n" to stack buffer
  instr (mov_r64_imm64 .rax 0x0D),
  instr (mov_mem8 .rdi .rax),
  instr (add_r64_imm8 .rdi 1),
  instr (mov_r64_imm64 .rax 0x0A),
  instr (mov_mem8 .rdi .rax),
  instr (add_r64_imm8 .rdi 1),

  -- 9. Step 5: Output line to console via Win32 WriteFile
  instr (mov_r64 .rcx .r12),
  instr (lea_rsp .rdx 0x40),
  instr (mov_r64 .r8 .rdi),
  instr (sub_r64 .r8 .rdx),
  instr (lea_rsp .r9 0x28),
  instr (mov_rsp64 0x20 0),
  call_import "WriteFile",

  -- 10. Step 6: Advance Fibonacci recurrence in hardware registers
  instr (mov_r64 .r8 .r14),
  instr (add_r64 .r8 .r15),
  instr (mov_r64 .r14 .r15),
  instr (mov_r64 .r15 .r8),
  instr (add_r64_imm8 .r13 1),
  jmp_near_label "main_loop",

  -- 11. Exit cleanly with code 0
  label "exit_loop",
  instr (xor_r32 .ecx .ecx),
  call_import "ExitProcess"
]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Linked binary program artifact for Spike 2. -/
def spike2Linked : LinkedWindowsProgram :=
  linkWindowsProgram spike2SymbolicProgram []

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Lowered concrete machine instruction sequence for Spike 2. -/
def spike2Instructions : List X86_64Instr :=
  spike2Linked.instructions

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Complete Windows executable specification for Spike 2. -/
def spike2Executable : WindowsExecutable :=
  spike2Linked.executable

end Spikes.Spike2Fibonacci.Windows

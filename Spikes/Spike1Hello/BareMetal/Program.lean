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
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.In
import Gasm.Targets.X86_64.Instructions.Out
import Gasm.Targets.X86_64.Instructions.Hlt
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.BareMetal.ELFFormat
import Gasm.Targets.BareMetal.UART
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Executable
import Gasm.Targets.BareMetal.Linker

namespace Spikes.Spike1Hello.BareMetal

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.BareMetal
open Gasm.Targets.BareMetal.UART
open Gasm.Targets.BareMetal.Linker

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Pure byte sequence for the 'Hello, World!\n' message placed in data section. -/
def helloMessage : ByteArray :=
  "Hello, World!\n".toUTF8

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Symbolic program definition for Spike 1 (Bare Metal x86-64 Hello World). -/
def spike1BareMetalSymbolicProgram : List SymbolicInstr := [
  -- 1. Initialize 16550 UART COM1 (0x3F8)
  -- Disable interrupts: IER (0x3F9) := 0
  instr (mov_r32 .edx UART_IER.toUInt32),
  instr (xor_r32 .eax .eax),
  instr out_dx_al,

  -- Enable DLAB: LCR (0x3FB) := 0x80
  instr (mov_r32 .edx UART_LCR.toUInt32),
  instr (mov_r32 .eax LCR_DLAB.toUInt32),
  instr out_dx_al,

  -- Set baud rate divisor (115,200 baud): DLL (0x3F8) := 1, DLM (0x3F9) := 0
  instr (mov_r32 .edx UART_DATA.toUInt32),
  instr (mov_r32 .eax BAUD_115200_DLL.toUInt32),
  instr out_dx_al,
  instr (mov_r32 .edx UART_IER.toUInt32),
  instr (xor_r32 .eax .eax),
  instr out_dx_al,

  -- Set 8N1 word length & clear DLAB: LCR (0x3FB) := 0x03
  instr (mov_r32 .edx UART_LCR.toUInt32),
  instr (mov_r32 .eax LCR_8N1.toUInt32),
  instr out_dx_al,

  -- Enable & clear FIFOs: FCR (0x3FA) := 0xC7
  instr (mov_r32 .edx UART_IIR_FCR.toUInt32),
  instr (mov_r32 .eax FCR_INIT.toUInt32),
  instr out_dx_al,

  -- Assert modem control lines: MCR (0x3FC) := 0x0B
  instr (mov_r32 .edx UART_MCR.toUInt32),
  instr (mov_r32 .eax MCR_INIT.toUInt32),
  instr out_dx_al,

  -- 2. Transmit message loop (14 bytes)
  instr (mov_r32 .ecx 14),
  mov_data_32 .esi "helloMessage",
  instr (mov_r32 .edx UART_DATA.toUInt32),

  label "loop_top",
  instr (movzx_r64_mem8 .rax .rsi 0),
  instr out_dx_al,
  instr (add_r64_imm8 .rsi 1),
  instr (sub_r64_imm8 .rcx 1),
  jne_label "loop_top",

  -- 3. Exit via QEMU isa-debug-exit (0xF4) and HLT
  instr (mov_r32 .edx DEBUG_EXIT_PORT.toUInt32),
  instr (xor_r32 .eax .eax),
  instr out_dx_al,
  instr hlt_op
]

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Linked binary program artifact for Spike 1 Bare Metal. -/
def spike1BareMetalLinked : LinkedBareMetalProgram :=
  linkBareMetalProgram spike1BareMetalSymbolicProgram [("helloMessage", helloMessage)]

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Lowered concrete machine instruction sequence for Spike 1 Bare Metal. -/
def spike1BareMetalInstructions : List X86_64Instr :=
  spike1BareMetalLinked.instructions

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Complete BareMetalExecutable for Spike 1. -/
def spike1BareMetalExecutable : BareMetalExecutable :=
  spike1BareMetalLinked.executable

end Spikes.Spike1Hello.BareMetal

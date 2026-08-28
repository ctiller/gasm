/-
Copyright 2026 Google LLC

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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Instructions.Base
import Gasm.Targets.AArch64.Instructions.Mov
import Gasm.Targets.AArch64.Instructions.Branch
import Gasm.Targets.AArch64.Instructions.System
import Gasm.Targets.AArch64.Linux.Linker

namespace Spikes.Spike1Hello.AArch64Linux

open Gasm.Core
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions
open Gasm.Targets.AArch64.Linux

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
def helloMessage : ByteArray :=
  "Hello, World!\n".toUTF8

-- Helpers
/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
private def instr {ι : Type} [Gasm.Targets.AArch64.AArch64Instruction ι] (i : ι) : SymbolTable → Address → Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  fun _ _ => Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk i

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
private def adrLabel (rd : Reg64) (lbl : String) : SymbolTable → Address → Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  fun syms pc =>
    let target := lookupSymbol syms lbl
    let targetInt : Int := (target.toNat : Int)
    let pcInt : Int := (pc.toNat : Int)
    let offset : Int64 := int64OfInt (targetInt - pcInt)
    Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk (adrInstr rd offset)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- Symbolic program for Spike 1 AArch64 Linux. -/
def spike1AArch64LinuxSymbolicProgram : List ProgramElement := [
  -- 1. SYS_write (64)
  .instr (instr (movz64 .x8 64)),
  -- 2. fd := 1 (stdout)
  .instr (instr (movz64 .x0 1)),
  -- 3. buf := address of helloMessage
  .instr (adrLabel .x1 "helloMessage"),
  -- 4. count := 14
  .instr (instr (movz64 .x2 14)),
  -- 5. Trigger syscall
  .instr (instr (svcInstr 0)),
  
  -- 6. SYS_exit (93)
  .instr (instr (movz64 .x8 93)),
  -- 7. status := 0
  .instr (instr (movz64 .x0 0)),
  -- 8. Trigger syscall
  .instr (instr (svcInstr 0))
]

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
def spike1AArch64LinuxLinked : LinkedLinuxProgram :=
  linkLinuxProgram 0x400000 spike1AArch64LinuxSymbolicProgram [("helloMessage", helloMessage)]

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
def spike1AArch64LinuxInstructions : List Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  spike1AArch64LinuxLinked.instructions

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
def spike1AArch64LinuxExecutable : AArch64LinuxExecutable :=
  spike1AArch64LinuxLinked.executable

end Spikes.Spike1Hello.AArch64Linux

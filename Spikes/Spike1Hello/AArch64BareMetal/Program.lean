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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Instructions.Base
import Gasm.Targets.AArch64.Instructions.Add
import Gasm.Targets.AArch64.Instructions.Sub
import Gasm.Targets.AArch64.Instructions.Mov
import Gasm.Targets.AArch64.Instructions.LoadStore
import Gasm.Targets.AArch64.Instructions.Branch
import Gasm.Targets.AArch64.Instructions.System
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Executable
import Gasm.Targets.AArch64.BareMetal.Linker

namespace Spikes.Spike1Hello.AArch64BareMetal

open Gasm.Core
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions
open Gasm.Targets.AArch64.BareMetal

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
def helloMessage : ByteArray :=
  "Hello, World!\n".toUTF8

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Semihosting exit block: [0x20026 (64-bit), 0 (64-bit)] -/
def semihostingExitBlock : ByteArray :=
  ByteArray.mk #[0x26, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00] ++
  ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

-- Helpers
/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
private def instr {ι : Type} [Gasm.Targets.AArch64.AArch64Instruction ι] (i : ι) : SymbolTable → Address → Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  fun _ _ => Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk i

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
private def adrLabel (rd : Reg64) (lbl : String) : SymbolTable → Address → Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  fun syms pc =>
    let target := lookupSymbol syms lbl
    let targetInt : Int := (target.toNat : Int)
    let pcInt : Int := (pc.toNat : Int)
    let offset : Int64 := int64OfInt (targetInt - pcInt)
    Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk (adrInstr rd offset)

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
private def bCondLabel (cond : Cond) (lbl : String) : SymbolTable → Address → Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  fun syms pc =>
    let target := lookupSymbol syms lbl
    let targetInt : Int := (target.toNat : Int)
    let pcInt : Int := (pc.toNat : Int)
    let offset : Int64 := int64OfInt (targetInt - pcInt)
    Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk (bCondInstr cond offset)

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Symbolic program for Spike 1 AArch64 Bare Metal. -/
def spike1AArch64BareMetalSymbolicProgram : List ProgramElement := [
  -- 1. Load UART base address 0x09000000 into x0
  .instr (instr (movz64 .x0 0x0900 1)),
  -- 2. Load address of helloMessage into x1
  .instr (adrLabel .x1 "helloMessage"),
  -- 3. Load message length (14) into x2
  .instr (instr (movz64 .x2 14)),
  
  .label "loop_top",
  -- 4. Load byte from [x1] into x3
  .instr (fun _ _ => Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk ({ rt := .x3, rn := .x1, offset := 0 } : LdrbImm)),
  -- 5. Store byte from x3 into [x0] (UART DR)
  .instr (fun _ _ => Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction.mk (strbReg .w3 .x0)),
  -- 6. Increment x1 by 1
  .instr (instr (addImm64 .x1 .x1 1)),
  -- 7. Decrement x2 by 1
  .instr (instr (subImm64 .x2 .x2 1)),
  -- 8. Compare x2 to 0
  .instr (instr (cmpImm64 .x2 0)),
  -- 9. Branch back to loop_top if not zero (NE)
  .instr (bCondLabel .NE "loop_top"),
  
  -- 10. Exit semihosting: x0 := 0x18 (SYS_EXIT), x1 := address of exit block
  .instr (instr (movz64 .x0 0x18)),
  .instr (adrLabel .x1 "semihostingExitBlock"),
  .instr (instr (hltInstr 0xF000))
]

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
def spike1AArch64BareMetalLinked : LinkedBareMetalProgram :=
  linkBareMetalProgram 0x40001000 spike1AArch64BareMetalSymbolicProgram
    [("helloMessage", helloMessage), ("semihostingExitBlock", semihostingExitBlock)]

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
def spike1AArch64BareMetalInstructions : List Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction :=
  spike1AArch64BareMetalLinked.instructions

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
def spike1AArch64BareMetalExecutable : AArch64BareMetalExecutable :=
  spike1AArch64BareMetalLinked.executable

end Spikes.Spike1Hello.AArch64BareMetal

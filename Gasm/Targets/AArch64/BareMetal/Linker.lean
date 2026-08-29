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
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Executable

namespace Gasm.Targets.AArch64.BareMetal

open Gasm.Core
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Mappings from named labels or data constants to absolute addresses. -/
abbrev SymbolTable := List (String × Address)

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Resolves a symbol's absolute address from the symbol table. -/
def lookupSymbol (syms : SymbolTable) (name : String) : Address :=
  match syms.find? (fun (n, _) => n == name) with
  | some (_, addr) => addr
  | none => 0

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Symbolic representation of a program element in AArch64 assembly. -/
inductive ProgramElement where
  | label (name : String)
  | instr (builder : SymbolTable → Address → AnyAArch64Instruction)

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
def layoutDataSection (baseDataAddr : Address) (dataItems : List (String × ByteArray)) : SymbolTable × ByteArray :=
  let rec loop (curAddr : Address) (items : List (String × ByteArray)) (symAcc : SymbolTable) (bytesAcc : ByteArray) :=
    match items with
    | [] => (symAcc, bytesAcc)
    | (name, bytes) :: rest =>
      let symAcc' := (name, curAddr) :: symAcc
      let bytesAcc' := bytesAcc ++ bytes
      loop (curAddr + bytes.size.toUInt64) rest symAcc' bytesAcc'
  loop baseDataAddr dataItems [] ByteArray.empty

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
structure LinkedBareMetalProgram where
  instructions : List AnyAArch64Instruction
  executable   : AArch64BareMetalExecutable

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Serializes a list of AnyAArch64Instruction into a flat ByteArray. -/
def serializeInstructions (instrs : List AnyAArch64Instruction) : ByteArray :=
  instrs.foldl (fun acc i => acc ++ AArch64Instruction.encode i) ByteArray.empty

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Links a symbolic ProgramElement-based AArch64 program and data items. -/
def linkBareMetalProgram (entryAddr : Address) (elements : List ProgramElement)
                         (dataItems : List (String × ByteArray) := []) : LinkedBareMetalProgram :=
  -- Pass 1: Compute instruction label addresses
  let rec computeLabels (curPc : Address) (syms : SymbolTable) : List ProgramElement → SymbolTable
    | [] => syms
    | .label name :: rest => computeLabels curPc ((name, curPc) :: syms) rest
    | .instr _ :: rest => computeLabels (curPc + 4) syms rest
  
  let initialSyms := computeLabels entryAddr [] elements
  
  -- Compute data section start address
  let rec countInstrs : List ProgramElement → Nat
    | [] => 0
    | .label _ :: rest => countInstrs rest
    | .instr _ :: rest => countInstrs rest + 1
  
  let textSize := countInstrs elements * 4
  let dataBaseAddr := entryAddr + textSize.toUInt64
  let (dataSymbols, dataBytes) := layoutDataSection dataBaseAddr dataItems
  
  -- Combine symbol tables
  let allSymbols := initialSyms ++ dataSymbols
  
  -- Pass 2: Build concrete instructions
  let rec resolve (curPc : Address) : List ProgramElement → List AnyAArch64Instruction
    | [] => []
    | .label _ :: rest => resolve curPc rest
    | .instr builder :: rest => builder allSymbols curPc :: resolve (curPc + 4) rest
  
  let concreteInstrs := resolve entryAddr elements
  let textBytes := serializeInstructions concreteInstrs
  
  let executable : AArch64BareMetalExecutable := {
    loadBase  := 0x40000000,
    entryAddr := entryAddr,
    textBytes := textBytes,
    dataBytes := dataBytes
  }
  { instructions := concreteInstrs, executable := executable }

end Gasm.Targets.AArch64.BareMetal

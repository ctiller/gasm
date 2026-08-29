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
import Gasm.Targets.AArch64.Linux.ELFFormat
import Gasm.Targets.AArch64.Linux.Emitter

namespace Gasm.Targets.AArch64.Linux

open Gasm.Core
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Structured definition of a static AArch64 Linux ELF executable image. -/
structure AArch64LinuxExecutable where
  imageBase   : Address := 0x400000
  textBytes   : ByteArray
  rodataBytes : ByteArray := ByteArray.empty
  deriving Inhabited, DecidableEq

namespace AArch64LinuxExecutable

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def emit (exe : AArch64LinuxExecutable) : ByteArray :=
  emitELF64Executable exe.imageBase exe.textBytes exe.rodataBytes

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def load (exe : AArch64LinuxExecutable) : AArch64MachineState :=
  let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
  let layout := computeElf64Layout exe.imageBase exe.textBytes.size exe.rodataBytes.size shstrtabSize
  { pc               := layout.textVma,
    gprs             := fun _ => 0,
    sp               := 0x7FFFFFFF0000, -- Standard high SP mapping
    nzcv             := default,
    memory           := AArch64Mem.initRegion (fun a =>
      if a >= layout.textVma && a < layout.textVma + exe.textBytes.size.toUInt64 then
        exe.textBytes.get! (a - layout.textVma).toNat
      else if a >= layout.rodataVma && a < layout.rodataVma + exe.rodataBytes.size.toUInt64 then
        exe.rodataBytes.get! (a - layout.rodataVma).toNat
      else 0),
    stdinBuffer      := ByteArray.empty,
    incomingRequests := [] }

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def loadWithStdin (exe : AArch64LinuxExecutable) (stdin : ByteArray) : AArch64MachineState :=
  { exe.load with stdinBuffer := stdin }

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def loadWithRequests (exe : AArch64LinuxExecutable) (requests : List ByteArray) : AArch64MachineState :=
  { exe.load with incomingRequests := requests }

end AArch64LinuxExecutable

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Mappings from named labels or data constants to absolute addresses. -/
abbrev SymbolTable := List (String × Address)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Resolves a symbol's absolute address from the symbol table. -/
def lookupSymbol (syms : SymbolTable) (name : String) : Address :=
  match syms.find? (fun (n, _) => n == name) with
  | some (_, addr) => addr
  | none => 0

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Symbolic representation of a program element in AArch64 assembly. -/
inductive ProgramElement where
  | label (name : String)
  | instr (builder : SymbolTable → Address → Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction)

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
def layoutDataSection (baseDataAddr : Address) (dataItems : List (String × ByteArray)) : SymbolTable × ByteArray :=
  let rec loop (curAddr : Address) (items : List (String × ByteArray)) (symAcc : SymbolTable) (bytesAcc : ByteArray) :=
    match items with
    | [] => (symAcc, bytesAcc)
    | (name, bytes) :: rest =>
      let symAcc' := (name, curAddr) :: symAcc
      let bytesAcc' := bytesAcc ++ bytes
      loop (curAddr + bytes.size.toUInt64) rest symAcc' bytesAcc'
  loop baseDataAddr dataItems [] ByteArray.empty

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
structure LinkedLinuxProgram where
  instructions : List Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction
  executable   : AArch64LinuxExecutable

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Serializes a list of AnyAArch64Instruction into a flat ByteArray. -/
def serializeInstructions (instrs : List Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction) : ByteArray :=
  instrs.foldl (fun acc i => acc ++ AArch64Instruction.encode i) ByteArray.empty

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Links a symbolic ProgramElement-based AArch64 Linux program and data items. -/
def linkLinuxProgram (imageBase : Address) (elements : List ProgramElement)
                     (dataItems : List (String × ByteArray) := []) : LinkedLinuxProgram :=
  let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
  
  -- Compute instruction count to get text segment size
  let rec countInstrs : List ProgramElement → Nat
    | [] => 0
    | .label _ :: rest => countInstrs rest
    | .instr _ :: rest => countInstrs rest + 1
  let textSize := countInstrs elements * 4
  
  -- Compute ELF segment layout to resolve absolute VMAs
  let rodataSize := dataItems.foldl (fun acc (_, b) => acc + b.size) 0
  let layout := computeElf64Layout imageBase textSize rodataSize shstrtabSize
  let entryAddr := layout.textVma
  
  -- Pass 1: Compute instruction label addresses
  let rec computeLabels (curPc : Address) (syms : SymbolTable) : List ProgramElement → SymbolTable
    | [] => syms
    | .label name :: rest => computeLabels curPc ((name, curPc) :: syms) rest
    | .instr _ :: rest => computeLabels (curPc + 4) syms rest
  
  let initialSyms := computeLabels entryAddr [] elements
  
  -- Layout rodata section at its computed segment VMA
  let (dataSymbols, dataBytes) := layoutDataSection layout.rodataVma dataItems
  let allSymbols := initialSyms ++ dataSymbols
  
  -- Pass 2: Resolve and build concrete instructions
  let rec resolve (curPc : Address) : List ProgramElement → List Gasm.Targets.AArch64.Instructions.AnyAArch64Instruction
    | [] => []
    | .label _ :: rest => resolve curPc rest
    | .instr builder :: rest => builder allSymbols curPc :: resolve (curPc + 4) rest
  
  let concreteInstrs := resolve entryAddr elements
  let textBytes := serializeInstructions concreteInstrs
  
  let executable : AArch64LinuxExecutable := {
    imageBase   := imageBase,
    textBytes   := textBytes,
    rodataBytes := dataBytes
  }
  { instructions := concreteInstrs, executable := executable }

end Gasm.Targets.AArch64.Linux

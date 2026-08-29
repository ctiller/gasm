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
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Linux.ELFFormat
import Gasm.Targets.Linux.Emitter

namespace Gasm.Targets.Linux

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Structured definition of a 64-bit static Linux ELF executable image. -/
structure LinuxExecutable where
  imageBase   : Address := 0x400000
  textBytes   : ByteArray
  rodataBytes : ByteArray := ByteArray.empty
  deriving Inhabited

namespace LinuxExecutable

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Serializes the Linux executable to a standalone static ELF64 binary image. -/
def emit (exe : LinuxExecutable) : ByteArray :=
  emitELF64Executable exe.imageBase exe.textBytes exe.rodataBytes

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Loads the Linux executable into an initial X86_64MachineState with mapped text and rodata segments. -/
def load (exe : LinuxExecutable) : X86_64MachineState :=
  let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
  let layout := computeElf64Layout exe.imageBase exe.textBytes.size exe.rodataBytes.size shstrtabSize
  { rip              := layout.textVma,
    gprs             := fun r => if r == .rsp then 0x7FFFFFFF0000 else 0,
    flags            := 0x202,
    memory           := X86_64Mem.initRegion (fun a =>
      if a >= layout.textVma && a < layout.textVma + exe.textBytes.size.toUInt64 then
        exe.textBytes.get! (a - layout.textVma).toNat
      else if a >= layout.rodataVma && a < layout.rodataVma + exe.rodataBytes.size.toUInt64 then
        exe.rodataBytes.get! (a - layout.rodataVma).toNat
      else 0),
    stdinBuffer      := ByteArray.empty,
    incomingRequests := [] }

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Loads the Linux executable into initial machine state with pre-seeded standard input. -/
def loadWithStdin (exe : LinuxExecutable) (stdin : ByteArray) : X86_64MachineState :=
  let s := exe.load
  { s with stdinBuffer := stdin }

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Loads the Linux executable into initial machine state with pre-seeded network requests. -/
def loadWithRequests (exe : LinuxExecutable) (reqs : List ByteArray) : X86_64MachineState :=
  let s := exe.load
  { s with incomingRequests := reqs }

end LinuxExecutable

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Layouts named data items sequentially in the read-only data segment and returns the symbol table and merged bytes. -/
def layoutDataSection (baseRodataVma : Address) (dataItems : List (String × ByteArray)) : SymbolTable × ByteArray :=
  let rec loop (curVma : Address) (items : List (String × ByteArray)) (symAcc : SymbolTable) (bytesAcc : ByteArray) :=
    match items with
    | [] => (symAcc, bytesAcc)
    | (name, bytes) :: rest =>
      let symAcc' := (name, curVma) :: symAcc
      let bytesAcc' := bytesAcc ++ bytes
      loop (curVma + bytes.size.toUInt64) rest symAcc' bytesAcc'
  loop baseRodataVma dataItems [] ByteArray.empty

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Result of statically linking a Linux assembly program into concrete instructions and a LinuxExecutable. -/
structure LinkedLinuxProgram where
  instructions : List X86_64Instr
  executable   : LinuxExecutable

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Statically links a symbolic x86-64 assembly program and data items into a concrete LinuxExecutable and instruction list. -/
def linkLinuxProgramStatic (symbolicProgram : List SymbolicInstr)
                           (dataItems : List (String × ByteArray) := [])
                           (baseVma : Address := 0x400000) : LinkedLinuxProgram :=
  let estTextSize := (symbolicProgram.map estimatedSize).foldl (· + ·) 0
  let (_, rodataBytesEst) := layoutDataSection 0 dataItems
  let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
  let layoutEst := computeElf64Layout baseVma estTextSize rodataBytesEst.size shstrtabSize
  let (dataSymbols, rodataBytes) := layoutDataSection layoutEst.rodataVma dataItems
  let concreteInstrs := assembleProgram layoutEst.textVma symbolicProgram dataSymbols
  let textBytes := serializeInstructions concreteInstrs
  let exe : LinuxExecutable := {
    imageBase   := baseVma,
    textBytes   := textBytes,
    rodataBytes := rodataBytes
  }
  ⟨concreteInstrs, exe⟩

end Gasm.Targets.Linux

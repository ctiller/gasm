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
import Gasm.Targets.BareMetal.ELFFormat
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Executable

namespace Gasm.Targets.BareMetal.Linker

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.BareMetal

/- REF: docs/TARGETS/BARE_METAL.md#33-flat-physical-memory-model-linker-layout -/
/-- Lays out named data byte arrays contiguously in data section and produces symbol table. -/
def layoutDataSection (baseDataAddr : Address) (dataItems : List (String × ByteArray)) : SymbolTable × ByteArray :=
  let rec loop (curAddr : Address) (items : List (String × ByteArray)) (symAcc : SymbolTable) (bytesAcc : ByteArray) :=
    match items with
    | [] => (symAcc, bytesAcc)
    | (name, bytes) :: rest =>
      let symAcc' := (name, curAddr) :: symAcc
      let bytesAcc' := bytesAcc ++ bytes
      loop (curAddr + bytes.size.toUInt64) rest symAcc' bytesAcc'
  loop baseDataAddr dataItems [] ByteArray.empty

/- REF: docs/TARGETS/BARE_METAL.md#33-flat-physical-memory-model-linker-layout -/
/-- Result of linking a symbolic bare-metal program into concrete instructions and BareMetalExecutable. -/
structure LinkedBareMetalProgram where
  instructions : List X86_64Instr
  executable   : BareMetalExecutable

/- REF: docs/TARGETS/BARE_METAL.md#33-flat-physical-memory-model-linker-layout -/
/-- Links a symbolic x86-64 assembly program and data items into a concrete BareMetalExecutable. -/
def linkBareMetalProgram (symbolicProgram : List SymbolicInstr)
                         (dataItems : List (String × ByteArray) := []) : LinkedBareMetalProgram :=
  let entryAddr : Address := 0x201000
  let estTextSize := (symbolicProgram.map estimatedSize).foldl (· + ·) 0
  let dataBaseAddr := entryAddr + estTextSize.toUInt64
  let (dataSymbols, dataBytes) := layoutDataSection dataBaseAddr dataItems
  let concreteInstrs := assembleProgram entryAddr symbolicProgram dataSymbols
  let textBytes := serializeInstructions concreteInstrs
  let exe : BareMetalExecutable := {
    textBytes := textBytes,
    dataBytes := dataBytes
  }
  ⟨concreteInstrs, exe⟩

end Gasm.Targets.BareMetal.Linker

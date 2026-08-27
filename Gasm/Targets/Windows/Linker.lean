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
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Emitter
import Gasm.Targets.Windows.Win32API

namespace Gasm.Targets.Windows.Linker

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Standard imported Win32 symbol mapping with dynamic IAT RVA. -/
def standardWin32Imports (idataRva : Address) (names : List String := ["GetStdHandle", "ReadFile", "WriteFile", "ExitProcess", "VirtualAlloc", "VirtualFree"]) : SymbolTable :=
  let rec loop (idx : Nat) (items : List String) (acc : SymbolTable) : SymbolTable :=
    match items with
    | [] => acc
    | name :: rest => loop (idx + 1) rest (acc ++ [(name, idataRva + (idx * 8).toUInt64)])
  loop 0 names []

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Layouts a list of named data byte arrays into the .rdata section and returns symbol offsets and merged ByteArray. -/
def layoutDataSection (baseRdataRva : Address) (dataItems : List (String × ByteArray)) : SymbolTable × ByteArray :=
  let rec loop (curRva : Address) (items : List (String × ByteArray)) (symAcc : SymbolTable) (bytesAcc : ByteArray) :=
    match items with
    | [] => (symAcc, bytesAcc)
    | (name, bytes) :: rest =>
      let symAcc' := (name, curRva) :: symAcc
      let bytesAcc' := bytesAcc ++ bytes
      loop (curRva + bytes.size.toUInt64) rest symAcc' bytesAcc'
  loop baseRdataRva dataItems [] ByteArray.empty

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Result of linking a Windows symbolic program into concrete instructions and WindowsExecutable. -/
structure LinkedWindowsProgram where
  instructions : List X86_64Instr
  executable   : WindowsExecutable

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Links a symbolic x86-64 assembly program and data items into a concrete WindowsExecutable and X86_64Instr list with dynamic section layout. -/
def linkWindowsProgram (symbolicProgram : List SymbolicInstr)
                       (dataItems : List (String × ByteArray) := [])
                       (importNames : List String := ["GetStdHandle", "ReadFile", "WriteFile", "ExitProcess", "VirtualAlloc", "VirtualFree"]) : LinkedWindowsProgram :=
  let estTextSize := (symbolicProgram.map estimatedSize).foldl (· + ·) 0
  let (_, rdataBytesEst) := layoutDataSection 0 dataItems
  let layout := computeSectionLayout estTextSize rdataBytesEst.size 512
  let (dataSymbols, rdataBytes) := layoutDataSection layout.rdataRva.toUInt64 dataItems
  let importSymbols := standardWin32Imports layout.idataRva.toUInt64 importNames
  let externalSymbols := dataSymbols ++ importSymbols
  let concreteInstrs := assembleProgram layout.textRva.toUInt64 symbolicProgram externalSymbols
  let textBytes := serializeInstructions concreteInstrs
  let importFunctions := importNames.map (fun name => { moduleName := "KERNEL32.dll", symbolName := name : Win32Function })
  let exe : WindowsExecutable := {
    textBytes  := textBytes,
    rdataBytes := rdataBytes,
    imports    := importFunctions
  }
  ⟨concreteInstrs, exe⟩

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Standard imported Win32 symbol mapping with dynamic IAT RVA for multi-DLL imports accounting for per-DLL null terminators. -/
def multiDllWin32Imports (idataRva : Address) (dllImports : List (String × List String)) : SymbolTable :=
  let rec loopDlls (curRva : Address) (dlls : List (String × List String)) (acc : SymbolTable) : SymbolTable :=
    match dlls with
    | [] => acc
    | (_, fns) :: rest =>
      let rec loopFns (fnRva : Address) (items : List String) (fnAcc : SymbolTable) : SymbolTable :=
        match items with
        | [] => fnAcc
        | fn :: frest => loopFns (fnRva + 8) frest (fnAcc ++ [(fn, fnRva)])
      let dllSyms := loopFns curRva fns []
      let nextDllRva := curRva + ((fns.length + 1) * 8).toUInt64
      loopDlls nextDllRva rest (acc ++ dllSyms)
  loopDlls idataRva dllImports []

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Links a symbolic x86-64 assembly program and data items with multi-DLL imports into a concrete WindowsExecutable and X86_64Instr list with dynamic section layout. -/
def linkWindowsProgramMultiDll (symbolicProgram : List SymbolicInstr)
                              (dataItems : List (String × ByteArray) := [])
                              (dllImports : List (String × List String) := []) : LinkedWindowsProgram :=
  let estTextSize := (symbolicProgram.map estimatedSize).foldl (· + ·) 0
  let (_, rdataBytesEst) := layoutDataSection 0 dataItems
  let layout := computeSectionLayout estTextSize rdataBytesEst.size 1024
  let (dataSymbols, rdataBytes) := layoutDataSection layout.rdataRva.toUInt64 dataItems
  let importSymbols := multiDllWin32Imports layout.idataRva.toUInt64 dllImports
  let externalSymbols := dataSymbols ++ importSymbols
  let concreteInstrs := assembleProgram layout.textRva.toUInt64 symbolicProgram externalSymbols
  let textBytes := serializeInstructions concreteInstrs
  let importFunctions := dllImports.flatMap (fun (dll, fns) => fns.map (fun fn => { moduleName := dll, symbolName := fn : Win32Function }))
  let exe : WindowsExecutable := {
    textBytes  := textBytes,
    rdataBytes := rdataBytes,
    imports    := importFunctions
  }
  ⟨concreteInstrs, exe⟩

end Gasm.Targets.Windows.Linker

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
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret

namespace Gasm.Targets.X86_64.Assembler

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Symbolic x86-64 instruction element with symbolic label support. -/
inductive SymbolicInstr where
  | concrete   : X86_64Instr → SymbolicInstr
  | label      : String → SymbolicInstr
  | jmp        : String → SymbolicInstr
  | jmpNear    : String → SymbolicInstr
  | je         : String → SymbolicInstr
  | jeNear     : String → SymbolicInstr
  | jne        : String → SymbolicInstr
  | jneNear    : String → SymbolicInstr
  | jl         : String → SymbolicInstr
  | jle        : String → SymbolicInstr
  | jg         : String → SymbolicInstr
  | jge        : String → SymbolicInstr
  | jgeNear    : String → SymbolicInstr
  | jb         : String → SymbolicInstr
  | jbNear     : String → SymbolicInstr
  | jae        : String → SymbolicInstr
  | jaeNear    : String → SymbolicInstr
  | ja         : String → SymbolicInstr
  | jaNear     : String → SymbolicInstr
  | jbe        : String → SymbolicInstr
  | jleNear    : String → SymbolicInstr
  | leaSymbol  : Reg64 → String → SymbolicInstr
  | movData32  : Reg32 → String → SymbolicInstr
  | callSymbol : String → SymbolicInstr
  | callLabel  : String → SymbolicInstr
  deriving Inhabited

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for concrete instructions. -/
def instr (i : X86_64Instr) : SymbolicInstr := .concrete i

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for labels. -/
def label (name : String) : SymbolicInstr := .label name

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic unconditional jump. -/
def jmp_label (target : String) : SymbolicInstr := .jmp target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic near unconditional jump (32-bit displacement). -/
def jmp_near_label (target : String) : SymbolicInstr := .jmpNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JE / JZ. -/
def je_label (target : String) : SymbolicInstr := .je target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic near JE / JZ (32-bit displacement). -/
def je_near_label (target : String) : SymbolicInstr := .jeNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JNE / JNZ. -/
def jne_label (target : String) : SymbolicInstr := .jne target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic near JNE / JNZ (32-bit displacement). -/
def jne_near_label (target : String) : SymbolicInstr := .jneNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JL. -/
def jl_label (target : String) : SymbolicInstr := .jl target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JLE. -/
def jle_label (target : String) : SymbolicInstr := .jle target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JLE near. -/
def jle_near_label (target : String) : SymbolicInstr := .jleNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JG. -/
def jg_label (target : String) : SymbolicInstr := .jg target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JGE. -/
def jge_label (target : String) : SymbolicInstr := .jge target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JGE near. -/
def jge_near_label (target : String) : SymbolicInstr := .jgeNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JB. -/
def jb_label (target : String) : SymbolicInstr := .jb target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JB near. -/
def jb_near_label (target : String) : SymbolicInstr := .jbNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JAE. -/
def jae_label (target : String) : SymbolicInstr := .jae target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JAE near. -/
def jae_near_label (target : String) : SymbolicInstr := .jaeNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JA. -/
def ja_label (target : String) : SymbolicInstr := .ja target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JA near. -/
def ja_near_label (target : String) : SymbolicInstr := .jaNear target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic JBE. -/
def jbe_label (target : String) : SymbolicInstr := .jbe target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic RIP-relative LEA. -/
def lea_data (dst : Reg64) (symbolName : String) : SymbolicInstr := .leaSymbol dst symbolName

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic 32-bit absolute MOV immediate. -/
def mov_data_32 (dst : Reg32) (symbolName : String) : SymbolicInstr := .movData32 dst symbolName

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic indirect CALL through IAT symbol. -/
def call_import (symbolName : String) : SymbolicInstr := .callSymbol symbolName

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Shorthand constructor for symbolic direct near CALL to a local label. -/
def call_label (target : String) : SymbolicInstr := .callLabel target

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Computes estimated instruction size for pass-1 address layout. -/
def estimatedSize (s : SymbolicInstr) : Nat :=
  match s with
  | .concrete i      => (X86_64Instruction.encode i).size
  | .label _         => 0
  | .jmp _           => 2 -- EB rel8
  | .jmpNear _       => 5 -- E9 rel32
  | .je _            => 2 -- 74 rel8
  | .jeNear _        => 6 -- 0F 84 rel32
  | .jne _           => 2 -- 75 rel8
  | .jneNear _       => 6 -- 0F 85 rel32
  | .jl _            => 2 -- 7C rel8
  | .jle _           => 2 -- 7E rel8
  | .jleNear _       => 6 -- 0F 8E rel32
  | .jg _            => 2 -- 7F rel8
  | .jge _           => 2 -- 7D rel8
  | .jgeNear _       => 6 -- 0F 8D rel32
  | .jb _            => 2 -- 72 rel8
  | .jbNear _        => 6 -- 0F 82 rel32
  | .jae _           => 2 -- 73 rel8
  | .jaeNear _       => 6 -- 0F 83 rel32
  | .ja _            => 2 -- 77 rel8
  | .jaNear _        => 6 -- 0F 87 rel32
  | .jbe _           => 2 -- 76 rel8
  | .leaSymbol _ _   => 7 -- REX 8D ModRM disp32
  | .movData32 _ _   => 5 -- B8+r imm32
  | .callSymbol _    => 6 -- FF 15 disp32
  | .callLabel _     => 5 -- E8 disp32

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Symbol table mapping label names to absolute/RVA byte addresses. -/
abbrev SymbolTable := List (String × Address)

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Looks up a symbol's address in the symbol table. -/
def lookupSymbol (syms : SymbolTable) (name : String) : Option Address :=
  match syms with
  | [] => none
  | (k, v) :: rest => if k == name then some v else lookupSymbol rest name

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Pass 1: Scans symbolic instructions and collects label addresses based on instruction offsets.
    Panics if duplicate label definitions are encountered. -/
def buildSymbolTable (baseRip : Address) (program : List SymbolicInstr) : SymbolTable :=
  let rec scan (curRip : Address) (items : List SymbolicInstr) (acc : SymbolTable) : SymbolTable :=
    match items with
    | [] => acc
    | .label name :: rest =>
      if (lookupSymbol acc name).isSome then
        panic! s!"buildSymbolTable: duplicate label definition '{name}' at RIP {curRip}"
      else
        scan curRip rest ((name, curRip) :: acc)
    | item :: rest =>
      let sz := estimatedSize item
      scan (curRip + sz.toUInt64) rest acc
  scan baseRip program []

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Converts signed relative offset (target - nextRip) to an 8-bit unsigned displacement byte.
    Panics if the relative offset cannot fit into a signed 8-bit integer [-128, 127]. -/
def toDisp8 (target : Address) (nextRip : Address) : UInt8 :=
  let diff : Int := target.toNat - nextRip.toNat
  if diff < -128 || diff > 127 then
    panic! s!"toDisp8: displacement out of 8-bit range [-128, 127]: {diff} (target {target}, nextRip {nextRip})"
  else if diff >= 0 then
    UInt8.ofNat diff.toNat
  else
    let neg := (-diff).toNat
    UInt8.ofNat (256 - (neg % 256))

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Converts signed relative offset (target - nextRip) to a 32-bit signed integer displacement. -/
def toDisp32 (target : Address) (nextRip : Address) : Int32 :=
  let diff : Int := target.toNat - nextRip.toNat
  if diff >= 0 then
    Int32.ofNat diff.toNat
  else
    -Int32.ofNat (-diff).toNat

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Resolves a symbolic label to its concrete memory address, panicking on unresolved symbols. -/
def resolveSymbol (allSymbols : SymbolTable) (target : String) (curRip : Address) : Address :=
  match lookupSymbol allSymbols target with
  | some addr => addr
  | none => panic! s!"assembleProgram: undefined or unresolved symbol '{target}' referenced at RIP {curRip}"

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Pass 2: Resolves symbolic labels and emits concrete X86_64Instr sequence. -/
def assembleProgram (baseRip : Address) (program : List SymbolicInstr) (externalSymbols : SymbolTable := []) : List X86_64Instr :=
  let internalSymbols := buildSymbolTable baseRip program
  let allSymbols := internalSymbols ++ externalSymbols
  let rec emit (curRip : Address) (items : List SymbolicInstr) (acc : List X86_64Instr) : List X86_64Instr :=
    match items with
    | [] => acc
    | .concrete i :: rest =>
      let sz := (X86_64Instruction.encode i).size
      emit (curRip + sz.toUInt64) rest (acc ++ [i])
    | .label _ :: rest =>
      emit curRip rest acc
    | .jmp target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jmp_rel8 disp])
    | .jmpNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 5
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [jmp_rel32 disp])
    | .je target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [je_rel8 disp])
    | .jeNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [je_rel32 disp])
    | .jne target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jne_rel8 disp])
    | .jneNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [jne_rel32 disp])
    | .jl target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jl_rel8 disp])
    | .jle target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jle_rel8 disp])
    | .jleNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [jle_rel32 disp])
    | .jg target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jg_rel8 disp])
    | .jge target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jge_rel8 disp])
    | .jgeNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [jge_rel32 disp])
    | .jb target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jb_rel8 disp])
    | .jbNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [jb_rel32 disp])
    | .jae target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jae_rel8 disp])
    | .jaeNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [jae_rel32 disp])
    | .ja target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [ja_rel8 disp])
    | .jaNear target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [ja_rel32 disp])
    | .jbe target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 2
      let disp := toDisp8 targetAddr nextRip
      emit nextRip rest (acc ++ [jbe_rel8 disp])
    | .leaSymbol dst target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 7
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [lea_rip dst disp])
    | .movData32 dst target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 5
      emit nextRip rest (acc ++ [mov_r32 dst targetAddr.toUInt32])
    | .callSymbol target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 6
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [call_rip disp])
    | .callLabel target :: rest =>
      let targetAddr := resolveSymbol allSymbols target curRip
      let nextRip := curRip + 5
      let disp := toDisp32 targetAddr nextRip
      emit nextRip rest (acc ++ [call_rel32 disp])
  emit baseRip program []

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Serializes a list of concrete instructions into raw bytes. -/
def serializeInstructions (instrs : List X86_64Instr) : ByteArray :=
  instrs.foldl (fun acc i => acc ++ X86_64Instruction.encode i) ByteArray.empty

end Gasm.Targets.X86_64.Assembler

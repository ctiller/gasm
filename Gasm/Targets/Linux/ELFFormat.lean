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
import Gasm.Targets.ELF.Format

namespace Gasm.Targets.Linux

open Gasm.Core
open Gasm.Targets.ELF

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Standard ELF executable file type (ET_EXEC = 2). -/
def ET_EXEC : UInt16 := Gasm.Targets.ELF.ET_EXEC

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Standard ELF position-independent / shared object file type (ET_DYN = 3). -/
def ET_DYN : UInt16 := Gasm.Targets.ELF.ET_DYN

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Standard x86-64 ELF machine architecture identifier (EM_X86_64 = 62). -/
def EM_X86_64 : UInt16 := Gasm.Targets.ELF.EM_X86_64

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Loadable program segment type (PT_LOAD = 1). -/
def PT_LOAD : UInt32 := Gasm.Targets.ELF.PT_LOAD

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Program header segment flag: Executable (PF_X = 1). -/
def PF_X : UInt32 := Gasm.Targets.ELF.PF_X

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Program header segment flag: Writable (PF_W = 2). -/
def PF_W : UInt32 := Gasm.Targets.ELF.PF_W

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Program header segment flag: Readable (PF_R = 4). -/
def PF_R : UInt32 := Gasm.Targets.ELF.PF_R

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Section header type: Inactive / Null (SHT_NULL = 0). -/
def SHT_NULL : UInt32 := Gasm.Targets.ELF.SHT_NULL

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Section header type: Program data (SHT_PROGBITS = 1). -/
def SHT_PROGBITS : UInt32 := Gasm.Targets.ELF.SHT_PROGBITS

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Section header type: String table (SHT_STRTAB = 3). -/
def SHT_STRTAB : UInt32 := Gasm.Targets.ELF.SHT_STRTAB

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Section header flag: Writable (SHF_WRITE = 1). -/
def SHF_WRITE : UInt64 := Gasm.Targets.ELF.SHF_WRITE

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Section header flag: Occupies memory during execution (SHF_ALLOC = 2). -/
def SHF_ALLOC : UInt64 := Gasm.Targets.ELF.SHF_ALLOC

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Section header flag: Executable machine instructions (SHF_EXECINSTR = 4). -/
def SHF_EXECINSTR : UInt64 := Gasm.Targets.ELF.SHF_EXECINSTR

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Standard 64-bit ELF file header (Elf64_Ehdr, 64 bytes). -/
abbrev Elf64_Ehdr := Gasm.Targets.ELF.Elf64_Ehdr

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Standard 64-bit ELF program header entry (Elf64_Phdr, 56 bytes). -/
abbrev Elf64_Phdr := Gasm.Targets.ELF.Elf64_Phdr

/- REF: docs/TARGETS/LINUX.md#31-elf64-layout-header-structure -/
/-- Standard 64-bit ELF section header entry (Elf64_Shdr, 64 bytes). -/
abbrev Elf64_Shdr := Gasm.Targets.ELF.Elf64_Shdr

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Aligns a value up to the nearest multiple of alignment. -/
def alignUp (val : Nat) (alignment : Nat) : Nat :=
  Gasm.Targets.ELF.alignUp val alignment

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Computed memory and file offsets for a 64-bit static ELF binary. -/
structure Elf64Layout where
  textOffset     : Nat
  textVma        : Address
  textSize       : Nat
  rodataOffset   : Nat
  rodataVma      : Address
  rodataSize     : Nat
  shstrtabOffset : Nat
  shstrtabSize   : Nat
  shdrsOffset    : Nat
  fileSize       : Nat
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Computes canonical static ELF64 layout with 4KB page alignment. -/
def computeElf64Layout (baseVma : Address) (textSize : Nat) (rodataSize : Nat) (shstrtabSize : Nat) : Elf64Layout :=
  let textOffset := 0x1000
  let textVma := baseVma + textOffset.toUInt64
  let rodataOffset := alignUp (textOffset + textSize) 0x1000
  let rodataVma := baseVma + rodataOffset.toUInt64
  let shstrtabOffset := alignUp (rodataOffset + rodataSize) 16
  let shdrsOffset := alignUp (shstrtabOffset + shstrtabSize) 8
  let shdrsSize := 4 * 64 -- NULL, .text, .rodata, .shstrtab
  let fileSize := shdrsOffset + shdrsSize
  { textOffset     := textOffset,
    textVma        := textVma,
    textSize       := textSize,
    rodataOffset   := rodataOffset,
    rodataVma      := rodataVma,
    rodataSize     := rodataSize,
    shstrtabOffset := shstrtabOffset,
    shstrtabSize   := shstrtabSize,
    shdrsOffset    := shdrsOffset,
    fileSize       := fileSize }

end Gasm.Targets.Linux

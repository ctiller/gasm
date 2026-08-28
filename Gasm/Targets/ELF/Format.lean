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

namespace Gasm.Targets.ELF

open Gasm.Core

/- REF: elf-sysv-psabi#object-files -/
/-- Standard ELF executable file type (ET_EXEC = 2). -/
def ET_EXEC : UInt16 := 2

/- REF: elf-sysv-psabi#object-files -/
/-- Standard ELF position-independent / shared object file type (ET_DYN = 3). -/
def ET_DYN : UInt16 := 3

/- REF: elf-sysv-psabi#object-files -/
/-- Standard x86-64 ELF machine architecture identifier (EM_X86_64 = 62 / 0x3E). -/
def EM_X86_64 : UInt16 := 62

/- REF: elf-sysv-psabi#object-files -/
/-- Loadable program segment type (PT_LOAD = 1). -/
def PT_LOAD : UInt32 := 1

/- REF: elf-sysv-psabi#object-files -/
/-- Auxiliary information / note segment type (PT_NOTE = 4). -/
def PT_NOTE : UInt32 := 4

/- REF: elf-sysv-psabi#object-files -/
/-- Program header segment flag: Executable (PF_X = 1). -/
def PF_X : UInt32 := 1

/- REF: elf-sysv-psabi#object-files -/
/-- Program header segment flag: Writable (PF_W = 2). -/
def PF_W : UInt32 := 2

/- REF: elf-sysv-psabi#object-files -/
/-- Program header segment flag: Readable (PF_R = 4). -/
def PF_R : UInt32 := 4

/- REF: elf-sysv-psabi#object-files -/
/-- Section header type: Inactive / Null (SHT_NULL = 0). -/
def SHT_NULL : UInt32 := 0

/- REF: elf-sysv-psabi#object-files -/
/-- Section header type: Program data (SHT_PROGBITS = 1). -/
def SHT_PROGBITS : UInt32 := 1

/- REF: elf-sysv-psabi#object-files -/
/-- Section header type: String table (SHT_STRTAB = 3). -/
def SHT_STRTAB : UInt32 := 3

/- REF: elf-sysv-psabi#object-files -/
/-- Section header flag: Writable (SHF_WRITE = 1). -/
def SHF_WRITE : UInt64 := 1

/- REF: elf-sysv-psabi#object-files -/
/-- Section header flag: Occupies memory during execution (SHF_ALLOC = 2). -/
def SHF_ALLOC : UInt64 := 2

/- REF: elf-sysv-psabi#object-files -/
/-- Section header flag: Executable machine instructions (SHF_EXECINSTR = 4). -/
def SHF_EXECINSTR : UInt64 := 4

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF file header (Elf64_Ehdr, 64 bytes). -/
structure Elf64_Ehdr where
  identMag0       : UInt8  := 0x7F
  identMag1       : UInt8  := 0x45 -- 'E'
  identMag2       : UInt8  := 0x4C -- 'L'
  identMag3       : UInt8  := 0x46 -- 'F'
  identClass      : UInt8  := 2    -- ELFCLASS64
  identData       : UInt8  := 1    -- ELFDATA2LSB (little-endian)
  identVersion    : UInt8  := 1    -- EV_CURRENT
  identOsAbi      : UInt8  := 0    -- ELFOSABI_NONE / System V
  identAbiVersion : UInt8  := 0
  e_type          : UInt16 := ET_EXEC
  e_machine       : UInt16 := EM_X86_64
  e_version       : UInt32 := 1
  e_entry         : Address
  e_phoff         : UInt64 := 64
  e_shoff         : UInt64 := 0
  e_flags         : UInt32 := 0
  e_ehsize        : UInt16 := 64
  e_phentsize     : UInt16 := 56
  e_phnum         : UInt16 := 1
  e_shentsize     : UInt16 := 64
  e_shnum         : UInt16 := 0
  e_shstrndx      : UInt16 := 0
  deriving Repr, DecidableEq

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF program header entry (Elf64_Phdr, 56 bytes). -/
structure Elf64_Phdr where
  p_type   : UInt32 := PT_LOAD
  p_flags  : UInt32
  p_offset : UInt64
  p_vaddr  : Address
  p_paddr  : Address
  p_filesz : UInt64
  p_memsz  : UInt64
  p_align  : UInt64 := 0x1000
  deriving Repr, DecidableEq

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF section header entry (Elf64_Shdr, 64 bytes). -/
structure Elf64_Shdr where
  sh_name      : UInt32
  sh_type      : UInt32
  sh_flags     : UInt64
  sh_addr      : Address
  sh_offset    : UInt64
  sh_size      : UInt64
  sh_link      : UInt32 := 0
  sh_info      : UInt32 := 0
  sh_addralign : UInt64 := 1
  sh_entsize   : UInt64 := 0
  deriving Repr, DecidableEq

/- REF: elf-sysv-psabi#object-files -/
/-- Aligns a value up to the nearest multiple of alignment. -/
def alignUp (val : Nat) (alignment : Nat) : Nat :=
  if alignment == 0 then val
  else ((val + alignment - 1) / alignment) * alignment

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes a UInt16 to two little-endian bytes. -/
def writeUInt16LE (v : UInt16) : ByteArray :=
  ByteArray.mk #[ (v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8 ]

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes a UInt32 to four little-endian bytes. -/
def writeUInt32LE (v : UInt32) : ByteArray :=
  ByteArray.mk #[
    (v &&& 0xFF).toUInt8,
    ((v >>> 8) &&& 0xFF).toUInt8,
    ((v >>> 16) &&& 0xFF).toUInt8,
    ((v >>> 24) &&& 0xFF).toUInt8
  ]

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes a UInt64 to eight little-endian bytes. -/
def writeUInt64LE (v : UInt64) : ByteArray :=
  ByteArray.mk #[
    (v &&& 0xFF).toUInt8,
    ((v >>> 8) &&& 0xFF).toUInt8,
    ((v >>> 16) &&& 0xFF).toUInt8,
    ((v >>> 24) &&& 0xFF).toUInt8,
    ((v >>> 32) &&& 0xFF).toUInt8,
    ((v >>> 40) &&& 0xFF).toUInt8,
    ((v >>> 48) &&& 0xFF).toUInt8,
    ((v >>> 56) &&& 0xFF).toUInt8
  ]

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes an Elf64_Ehdr into a 64-byte ByteArray. -/
def serializeElf64Header (h : Elf64_Ehdr) : ByteArray :=
  let ident := ByteArray.mk #[
    h.identMag0, h.identMag1, h.identMag2, h.identMag3,
    h.identClass, h.identData, h.identVersion, h.identOsAbi,
    h.identAbiVersion, 0, 0, 0, 0, 0, 0, 0
  ]
  ident ++
  writeUInt16LE h.e_type ++
  writeUInt16LE h.e_machine ++
  writeUInt32LE h.e_version ++
  writeUInt64LE h.e_entry ++
  writeUInt64LE h.e_phoff ++
  writeUInt64LE h.e_shoff ++
  writeUInt32LE h.e_flags ++
  writeUInt16LE h.e_ehsize ++
  writeUInt16LE h.e_phentsize ++
  writeUInt16LE h.e_phnum ++
  writeUInt16LE h.e_shentsize ++
  writeUInt16LE h.e_shnum ++
  writeUInt16LE h.e_shstrndx

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes an Elf64_Phdr into a 56-byte ByteArray. -/
def serializeElf64Phdr (ph : Elf64_Phdr) : ByteArray :=
  writeUInt32LE ph.p_type ++
  writeUInt32LE ph.p_flags ++
  writeUInt64LE ph.p_offset ++
  writeUInt64LE ph.p_vaddr ++
  writeUInt64LE ph.p_paddr ++
  writeUInt64LE ph.p_filesz ++
  writeUInt64LE ph.p_memsz ++
  writeUInt64LE ph.p_align

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes an Elf64_Shdr into a 64-byte ByteArray. -/
def serializeElf64Shdr (sh : Elf64_Shdr) : ByteArray :=
  writeUInt32LE sh.sh_name ++
  writeUInt32LE sh.sh_type ++
  writeUInt64LE sh.sh_flags ++
  writeUInt64LE sh.sh_addr ++
  writeUInt64LE sh.sh_offset ++
  writeUInt64LE sh.sh_size ++
  writeUInt32LE sh.sh_link ++
  writeUInt32LE sh.sh_info ++
  writeUInt64LE sh.sh_addralign ++
  writeUInt64LE sh.sh_entsize

end Gasm.Targets.ELF

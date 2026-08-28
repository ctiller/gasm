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

namespace Gasm.Targets.BareMetal

open Gasm.Core

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF file header (Elf64_Ehdr). -/
structure ELF64Header where
  identMag0       : UInt8  := 0x7F
  identMag1       : UInt8  := 0x45 -- 'E'
  identMag2       : UInt8  := 0x4C -- 'L'
  identMag3       : UInt8  := 0x46 -- 'F'
  identClass      : UInt8  := 2    -- ELFCLASS64
  identData       : UInt8  := 1    -- ELFDATA2LSB (little-endian)
  identVersion    : UInt8  := 1    -- EV_CURRENT
  identOsAbi      : UInt8  := 0    -- ELFOSABI_NONE / System V
  identAbiVersion : UInt8  := 0
  e_type          : UInt16 := 2    -- ET_EXEC
  e_machine       : UInt16 := 0x3E -- EM_X86_64
  e_version       : UInt32 := 1    -- EV_CURRENT
  e_entry         : UInt64         -- Entry point virtual/physical address
  e_phoff         : UInt64 := 0x40 -- Program header table file offset (64 bytes)
  e_shoff         : UInt64 := 0    -- Section header table file offset
  e_flags         : UInt32 := 0
  e_ehsize        : UInt16 := 64   -- ELF header size (64 bytes)
  e_phentsize     : UInt16 := 56   -- Program header table entry size (56 bytes)
  e_phnum         : UInt16 := 2    -- Number of program header entries (PT_LOAD + PT_NOTE)
  e_shentsize     : UInt16 := 0
  e_shnum         : UInt16 := 0
  e_shstrndx      : UInt16 := 0
  deriving Repr, DecidableEq

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF program header entry (Elf64_Phdr). -/
structure ELF64ProgramHeader where
  p_type   : UInt32 -- 1 = PT_LOAD, 4 = PT_NOTE
  p_flags  : UInt32 -- 1 = PF_X, 2 = PF_W, 4 = PF_R
  p_offset : UInt64 -- Segment file offset
  p_vaddr  : UInt64 -- Segment virtual address
  p_paddr  : UInt64 -- Segment physical address
  p_filesz : UInt64 -- Segment size in file
  p_memsz  : UInt64 -- Segment size in memory
  p_align  : UInt64 -- Segment alignment
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/BARE_METAL.md#32-xen-pvh-elf-note-xenelfnotephys32entry -/
/-- Xen PVH ELF boot note (XEN_ELFNOTE_PHYS32_ENTRY) required by QEMU -kernel. -/
structure XenPVHNote where
  namesz    : UInt32 := 4  -- "Xen\0" length
  descsz    : UInt32 := 4  -- 32-bit physical entry point address size
  noteType  : UInt32 := 18 -- XEN_ELFNOTE_PHYS32_ENTRY
  entryAddr : UInt32
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/BARE_METAL.md#33-flat-physical-memory-model-linker-layout -/
/-- Memory layout descriptor for bare-metal x86-64 flat ELF executable. -/
structure BareMetalLayout where
  loadBase      : UInt64 := 0x200000 -- 2 MB physical/virtual base
  headerPageSize: Nat    := 0x1000   -- 4 KB page for ELF headers & PVH note
  entryAddr     : UInt64 := 0x201000 -- Entry point at start of .text
  textSize      : Nat
  dataSize      : Nat
  totalFileSize : Nat
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/BARE_METAL.md#33-flat-physical-memory-model-linker-layout -/
/-- Computes canonical bare-metal memory and file layout. -/
def computeBareMetalLayout (textSize : Nat) (dataSize : Nat) : BareMetalLayout :=
  let headerSize := 0x1000
  let totalSize := headerSize + textSize + dataSize
  { loadBase := 0x200000,
    headerPageSize := headerSize,
    entryAddr := 0x201000,
    textSize := textSize,
    dataSize := dataSize,
    totalFileSize := totalSize }

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
/-- Serializes an ELF64Header into a 64-byte ByteArray. -/
def serializeELF64Header (h : ELF64Header) : ByteArray :=
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
/-- Serializes an ELF64ProgramHeader into a 56-byte ByteArray. -/
def serializeELF64ProgramHeader (ph : ELF64ProgramHeader) : ByteArray :=
  writeUInt32LE ph.p_type ++
  writeUInt32LE ph.p_flags ++
  writeUInt64LE ph.p_offset ++
  writeUInt64LE ph.p_vaddr ++
  writeUInt64LE ph.p_paddr ++
  writeUInt64LE ph.p_filesz ++
  writeUInt64LE ph.p_memsz ++
  writeUInt64LE ph.p_align

/- REF: docs/TARGETS/BARE_METAL.md#32-xen-pvh-elf-note-xenelfnotephys32entry -/
/-- Serializes a XenPVHNote into a 20-byte ByteArray. -/
def serializeXenPVHNote (note : XenPVHNote) : ByteArray :=
  writeUInt32LE note.namesz ++
  writeUInt32LE note.descsz ++
  writeUInt32LE note.noteType ++
  ByteArray.mk #[0x58, 0x65, 0x6E, 0x00] ++ -- "Xen\0"
  writeUInt32LE note.entryAddr

end Gasm.Targets.BareMetal

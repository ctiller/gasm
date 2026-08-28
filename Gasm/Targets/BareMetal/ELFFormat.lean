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
import Gasm.Targets.ELF.Notes

namespace Gasm.Targets.BareMetal

open Gasm.Core
open Gasm.Targets.ELF

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF file header (alias for Elf64_Ehdr). -/
abbrev ELF64Header := Gasm.Targets.ELF.Elf64_Ehdr

/- REF: elf-sysv-psabi#object-files -/
/-- Standard 64-bit ELF program header entry (alias for Elf64_Phdr). -/
abbrev ELF64ProgramHeader := Gasm.Targets.ELF.Elf64_Phdr

/- REF: docs/TARGETS/BARE_METAL.md#32-xen-pvh-elf-note-xenelfnotephys32entry -/
/-- Re-export of XenPVHNote from Gasm.Targets.ELF. -/
abbrev XenPVHNote := Gasm.Targets.ELF.XenPVHNote

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
/-- Serializes an ELF64Header into a 64-byte ByteArray. -/
def serializeELF64Header (h : ELF64Header) : ByteArray :=
  Gasm.Targets.ELF.serializeElf64Header h

/- REF: elf-sysv-psabi#object-files -/
/-- Serializes an ELF64ProgramHeader into a 56-byte ByteArray. -/
def serializeELF64ProgramHeader (ph : ELF64ProgramHeader) : ByteArray :=
  Gasm.Targets.ELF.serializeElf64Phdr ph

/- REF: docs/TARGETS/BARE_METAL.md#32-xen-pvh-elf-note-xenelfnotephys32entry -/
/-- Serializes a XenPVHNote into a 20-byte ByteArray. -/
def serializeXenPVHNote (note : XenPVHNote) : ByteArray :=
  Gasm.Targets.ELF.serializeXenPVHNote note

end Gasm.Targets.BareMetal

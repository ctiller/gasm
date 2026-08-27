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

namespace Gasm.Targets.Windows

/- REF: windows-pe-format#overview -/
/-- MS-DOS 2.0 MZ Header. -/
structure DOSHeader where
  e_magic    : UInt16 := 0x5A4D  -- 'MZ'
  e_lfanew   : UInt32 := 0x40    -- Offset to PE Header

/- REF: windows-pe-format#coff-file-header-object-and-image -/
/-- COFF Standard File Header. -/
structure COFFHeader where
  machine              : UInt16 := 0x8664  -- AMD64 / x86-64
  numberOfSections     : UInt16 := 3       -- .text, .rdata, .idata
  timeDateStamp        : UInt32 := 0
  pointerToSymbolTable : UInt32 := 0
  numberOfSymbols      : UInt32 := 0
  sizeOfOptionalHeader : UInt16 := 240     -- Optional Header 64 size
  characteristics      : UInt16 := 0x0022  -- EXECUTABLE_IMAGE | LARGE_ADDRESS_AWARE

/- REF: windows-pe-format#optional-header-image-only -/
/-- PE32+ 64-bit Optional Header. -/
structure OptionalHeader64 where
  magic                       : UInt16 := 0x020B  -- PE32+ (64-bit)
  majorLinkerVersion          : UInt8  := 14
  minorLinkerVersion          : UInt8  := 0
  sizeOfCode                  : UInt32
  sizeOfInitializedData       : UInt32
  sizeOfUninitializedData     : UInt32 := 0
  addressOfEntryPoint         : UInt32            -- RVA of Entry Point
  baseOfCode                  : UInt32 := 0x1000  -- RVA of .text
  imageBase                   : UInt64 := 0x140000000
  sectionAlignment            : UInt32 := 0x1000  -- 4096 bytes
  fileAlignment               : UInt32 := 0x200   -- 512 bytes
  majorOperatingSystemVersion : UInt16 := 6
  minorOperatingSystemVersion : UInt16 := 0
  majorImageVersion           : UInt16 := 0
  minorImageVersion           : UInt16 := 0
  majorSubsystemVersion       : UInt16 := 6
  minorSubsystemVersion       : UInt16 := 0
  win32VersionValue           : UInt32 := 0
  sizeOfImage                 : UInt32
  sizeOfHeaders               : UInt32 := 0x400
  checkSum                    : UInt32 := 0
  subsystem                   : UInt16 := 3       -- IMAGE_SUBSYSTEM_WINDOWS_CUI
  dllCharacteristics          : UInt16 := 0x8160  -- HIGH_ENTROPY_VA | DYNAMIC_BASE | NX_COMPAT | TERMINAL_SERVER_AWARE
  sizeOfStackReserve          : UInt64 := 0x100000
  sizeOfStackCommit           : UInt64 := 0x1000
  sizeOfHeapReserve           : UInt64 := 0x100000
  sizeOfHeapCommit            : UInt64 := 0x1000
  loaderFlags                 : UInt32 := 0
  numberOfRvaAndSizes         : UInt32 := 16

/- REF: windows-pe-format#section-table-section-headers -/
/-- Section Table Entry (Section Header). -/
structure SectionHeader where
  name                 : String
  virtualSize          : UInt32
  virtualAddress       : UInt32
  sizeOfRawData        : UInt32
  pointerToRawData     : UInt32
  pointerToRelocations : UInt32 := 0
  pointerToLinenumbers : UInt32 := 0
  numberOfRelocations  : UInt16 := 0
  numberOfLinenumbers  : UInt16 := 0
  characteristics      : UInt32

/- REF: windows-pe-format#the-idata-section -/
/-- Import Directory Table Entry. -/
structure ImportDirectoryEntry where
  importLookupTableRVA  : UInt32
  timeDateStamp         : UInt32 := 0
  forwarderChain        : UInt32 := 0
  nameRVA               : UInt32
  importAddressTableRVA : UInt32

/- REF: windows-pe-format#overview -/
/-- Aligns a value up to the nearest multiple of alignment. -/
def alignUp (val : Nat) (alignment : Nat) : Nat :=
  if alignment == 0 then val
  else ((val + alignment - 1) / alignment) * alignment

/- REF: windows-pe-format#section-table-section-headers -/
/-- Computes section RVAs and raw file sizes for PE image layout. -/
structure SectionLayout where
  textRva      : UInt32 := 0x1000
  textRawSize  : Nat
  rdataRva     : UInt32
  rdataRawSize : Nat
  idataRva     : UInt32
  idataRawSize : Nat
  sizeOfImage  : UInt32
  deriving Repr, DecidableEq

/- REF: windows-pe-format#section-table-section-headers -/
/-- Computes the canonical section layout for given section payload sizes. -/
def computeSectionLayout (textSize rdataSize idataSize : Nat) : SectionLayout :=
  let textRaw := alignUp (max 0x200 textSize) 0x200
  let rdataRaw := alignUp (max 0x200 rdataSize) 0x200
  let idataRaw := alignUp (max 0x200 idataSize) 0x200
  let textRva : UInt32 := 0x1000
  let rdataRva : UInt32 := textRva + (alignUp (max 0x1000 textSize) 0x1000).toUInt32
  let idataRva : UInt32 := rdataRva + (alignUp (max 0x1000 rdataSize) 0x1000).toUInt32
  let sizeOfImage : UInt32 := idataRva + (alignUp idataRaw 0x1000).toUInt32
  { textRva := textRva,
    textRawSize := textRaw,
    rdataRva := rdataRva,
    rdataRawSize := rdataRaw,
    idataRva := idataRva,
    idataRawSize := idataRaw,
    sizeOfImage := sizeOfImage }

end Gasm.Targets.Windows

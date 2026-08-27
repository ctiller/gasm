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
import Gasm.Targets.Windows.PEFormat

namespace Gasm.Targets.Windows

/- REF: windows-pe-format#overview -/
/-- Appends a 16-bit integer in little-endian order to a ByteArray. -/
def pushUInt16LE (b : ByteArray) (v : UInt16) : ByteArray :=
  b.push v.toUInt8 |>.push (v >>> 8).toUInt8

/- REF: windows-pe-format#overview -/
/-- Appends a 32-bit integer in little-endian order to a ByteArray. -/
def pushUInt32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push v.toUInt8
   |>.push (v >>> 8).toUInt8
   |>.push (v >>> 16).toUInt8
   |>.push (v >>> 24).toUInt8

/- REF: windows-pe-format#overview -/
/-- Appends a 64-bit integer in little-endian order to a ByteArray. -/
def pushUInt64LE (b : ByteArray) (v : UInt64) : ByteArray :=
  pushUInt32LE (pushUInt32LE b v.toUInt32) (v >>> 32).toUInt32

/- REF: windows-pe-format#overview -/
/-- Appends zero bytes until the buffer reaches the specified target size. -/
def padTo (b : ByteArray) (targetSize : Nat) : ByteArray :=
  if b.size >= targetSize then b
  else
    let zeros := ByteArray.mk (Array.replicate (targetSize - b.size) (0 : UInt8))
    b ++ zeros

/- REF: windows-pe-format#section-table-section-headers -/
/-- Serializes a section header into 40 bytes. -/
def serializeSectionHeader (h : SectionHeader) : ByteArray :=
  let nameBytes := String.toUTF8 h.name
  let namePad := ByteArray.mk (Array.replicate (8 - min 8 nameBytes.size) (0 : UInt8))
  let name8 := (ByteArray.mk (nameBytes.data.extract 0 (min 8 nameBytes.size))) ++ namePad
  let b := name8
  let b := pushUInt32LE b h.virtualSize
  let b := pushUInt32LE b h.virtualAddress
  let b := pushUInt32LE b h.sizeOfRawData
  let b := pushUInt32LE b h.pointerToRawData
  let b := pushUInt32LE b h.pointerToRelocations
  let b := pushUInt32LE b h.pointerToLinenumbers
  let b := pushUInt16LE b h.numberOfRelocations
  let b := pushUInt16LE b h.numberOfLinenumbers
  let b := pushUInt32LE b h.characteristics
  b

/- REF: windows-pe-format#the-idata-section -/
/-- Constructs an .idata section binding across multiple DLLs with dynamic section RVA and dynamic imports. -/
def buildMultiDllIDataSection (idataRva : UInt32) (dllImports : List (String × List String)) : ByteArray := Id.run do
  let mut idata := ByteArray.empty
  
  -- Calculate per-DLL IAT counts and offsets
  let mut dllIatOffsets : List Nat := []
  let mut curIatOffset := 0
  for (_, fns) in dllImports do
    dllIatOffsets := dllIatOffsets ++ [curIatOffset]
    let dllIatBytes := (fns.length + 1) * 8
    curIatOffset := curIatOffset + dllIatBytes
  let totalIatSize := curIatOffset
  
  let idtOffset := alignUp totalIatSize 16
  let idtSize := (dllImports.length + 1) * 20
  let iltOffset := idtOffset + idtSize
  let dllNamesBaseOffset := iltOffset + totalIatSize
  
  -- Calculate per-DLL Name offsets
  let mut dllNameOffsets : List Nat := []
  let mut curDllNameOffset := dllNamesBaseOffset
  for (dll, _) in dllImports do
    dllNameOffsets := dllNameOffsets ++ [curDllNameOffset]
    let nameLen := (String.toUTF8 dll).size + 1
    let alignedLen := alignUp nameLen 2
    curDllNameOffset := curDllNameOffset + alignedLen
    
  let hintNameBaseOffset := alignUp curDllNameOffset 16
  
  -- Calculate per-function HintName offsets
  let mut allHintOffsets : List (List Nat) := []
  let mut curHintOffset := hintNameBaseOffset
  for (_, fns) in dllImports do
    let mut dllHints : List Nat := []
    for fn in fns do
      dllHints := dllHints ++ [curHintOffset]
      let entryLen := 2 + (String.toUTF8 fn).size + 1
      let alignedLen := alignUp entryLen 2
      curHintOffset := curHintOffset + alignedLen
    allHintOffsets := allHintOffsets ++ [dllHints]
    
  -- 1. IAT
  for dllHints in allHintOffsets do
    for hOff in dllHints do
      idata := pushUInt64LE idata (idataRva.toUInt64 + hOff.toUInt64)
    idata := pushUInt64LE idata 0 -- Null terminator for this DLL
    
  -- 2. IDT
  idata := padTo idata idtOffset
  let dllImportsArr := dllImports.toArray
  let dllIatOffsetsArr := dllIatOffsets.toArray
  let dllNameOffsetsArr := dllNameOffsets.toArray
  for i in [0:dllImports.length] do
    let iatOff := dllIatOffsetsArr[i]!
    let nameOff := dllNameOffsetsArr[i]!
    let iltOff := iltOffset + iatOff
    idata := pushUInt32LE idata (idataRva + iltOff.toUInt32)      -- ImportLookupTableRVA (ILT)
    idata := pushUInt32LE idata 0                               -- TimeDateStamp
    idata := pushUInt32LE idata 0                               -- ForwarderChain
    idata := pushUInt32LE idata (idataRva + nameOff.toUInt32)    -- NameRVA
    idata := pushUInt32LE idata (idataRva + iatOff.toUInt32)     -- ImportAddressTableRVA (IAT)
    
  -- Null terminating IDT descriptor (20 zero bytes)
  idata := padTo idata (idtOffset + idtSize)
  
  -- 3. ILT
  idata := padTo idata iltOffset
  for dllHints in allHintOffsets do
    for hOff in dllHints do
      idata := pushUInt64LE idata (idataRva.toUInt64 + hOff.toUInt64)
    idata := pushUInt64LE idata 0 -- Null terminator
    
  -- 4. DLL Names
  for i in [0:dllImports.length] do
    let (dll, _) := dllImportsArr[i]!
    let nameOff := dllNameOffsetsArr[i]!
    idata := padTo idata nameOff
    idata := idata ++ (String.toUTF8 dll) ++ ByteArray.mk #[0]
    
  -- 5. Hint/Name Entries
  let allHintOffsetsArr := allHintOffsets.toArray
  for i in [0:dllImports.length] do
    let (_, fns) := dllImportsArr[i]!
    let dllHintsArr := allHintOffsetsArr[i]!.toArray
    let fnsArr := fns.toArray
    for j in [0:fns.length] do
      let fn := fnsArr[j]!
      let hOff := dllHintsArr[j]!
      idata := padTo idata hOff
      idata := pushUInt16LE idata 0
      idata := idata ++ (String.toUTF8 fn) ++ ByteArray.mk #[0]
      
  let finalSize := alignUp idata.size 512
  idata := padTo idata (max 512 finalSize)
  idata

/- REF: windows-pe-format#the-idata-section -/
/-- Constructs a standard .idata section binding to KERNEL32.dll with dynamic section RVA and dynamic imports. -/
def buildKernel32IDataSection (idataRva : UInt32) (importNames : List String := ["GetStdHandle", "WriteFile", "ExitProcess"]) : ByteArray :=
  buildMultiDllIDataSection idataRva [("KERNEL32.dll", importNames)]

/- REF: windows-pe-format#overview -/
/-- Emits a valid, fully formed 64-bit PE32+ (AMD64) executable image supporting multiple DLL imports. -/
def emitPE32ExecutableMultiDll (textBytes : ByteArray) (rdataBytes : ByteArray) (dllImports : List (String × List String)) : ByteArray := Id.run do
  let mut pe := ByteArray.empty
  
  -- 1. DOS Header (64 bytes)
  pe := pushUInt16LE pe 0x5A4D  -- 'MZ'
  pe := padTo pe 0x3C
  pe := pushUInt32LE pe 0x40    -- e_lfanew -> PE header at 0x40
  
  -- 2. PE Signature (4 bytes at offset 0x40)
  pe := pe ++ String.toUTF8 "PE\x00\x00"
  
  -- 3. COFF File Header (20 bytes at offset 0x44)
  pe := pushUInt16LE pe 0x8664  -- Machine: AMD64
  pe := pushUInt16LE pe 3       -- NumberOfSections: 3 (.text, .rdata, .idata)
  pe := pushUInt32LE pe 0       -- TimeDateStamp
  pe := pushUInt32LE pe 0       -- PointerToSymbolTable
  pe := pushUInt32LE pe 0       -- NumberOfSymbols
  pe := pushUInt16LE pe 240     -- SizeOfOptionalHeader
  pe := pushUInt16LE pe 0x0022  -- Characteristics: EXECUTABLE_IMAGE | LARGE_ADDRESS_AWARE
  
  -- Dynamic Section Alignment Calculations using shared computeSectionLayout
  let idataEst := buildMultiDllIDataSection 0x3000 dllImports
  let layout := computeSectionLayout textBytes.size rdataBytes.size idataEst.size
  let idata := buildMultiDllIDataSection layout.idataRva dllImports
  
  let textPtr := 0x400
  let rdataPtr := textPtr + layout.textRawSize
  let idataPtr := rdataPtr + layout.rdataRawSize
  
  let totalIatEntries := dllImports.foldl (fun acc (_, fns) => acc + fns.length + 1) 0
  let totalIatSize := totalIatEntries * 8
  let idtOffset := alignUp totalIatSize 16
  let idtSize := (dllImports.length + 1) * 20
  
  -- 4. Optional Header 64 (240 bytes at offset 0x58)
  pe := pushUInt16LE pe 0x020B  -- Magic: PE32+ (64-bit)
  pe := pe.push 14              -- MajorLinkerVersion
  pe := pe.push 0               -- MinorLinkerVersion
  pe := pushUInt32LE pe layout.textRawSize.toUInt32   -- SizeOfCode
  pe := pushUInt32LE pe (layout.rdataRawSize + layout.idataRawSize).toUInt32 -- SizeOfInitializedData
  pe := pushUInt32LE pe 0       -- SizeOfUninitializedData
  pe := pushUInt32LE pe layout.textRva -- AddressOfEntryPoint (RVA of .text)
  pe := pushUInt32LE pe layout.textRva -- BaseOfCode
  pe := pushUInt64LE pe 0x140000000 -- ImageBase
  pe := pushUInt32LE pe 0x1000  -- SectionAlignment (4096)
  pe := pushUInt32LE pe 0x200   -- FileAlignment (512)
  pe := pushUInt16LE pe 6       -- MajorOSVersion
  pe := pushUInt16LE pe 0       -- MinorOSVersion
  pe := pushUInt16LE pe 0       -- MajorImageVersion
  pe := pushUInt16LE pe 0       -- MinorImageVersion
  pe := pushUInt16LE pe 6       -- MajorSubsystemVersion
  pe := pushUInt16LE pe 0       -- MinorSubsystemVersion
  pe := pushUInt32LE pe 0       -- Win32VersionValue
  pe := pushUInt32LE pe layout.sizeOfImage  -- SizeOfImage (dynamically calculated)
  pe := pushUInt32LE pe 0x400   -- SizeOfHeaders (1024 bytes)
  pe := pushUInt32LE pe 0       -- CheckSum
  pe := pushUInt16LE pe 3       -- Subsystem: IMAGE_SUBSYSTEM_WINDOWS_CUI
  pe := pushUInt16LE pe 0x8120  -- DllCharacteristics: NX_COMPAT | TERMINAL_SERVER_AWARE (Fixed ImageBase, No ASLR)
  pe := pushUInt64LE pe 0x100000 -- SizeOfStackReserve
  pe := pushUInt64LE pe 0x1000   -- SizeOfStackCommit
  pe := pushUInt64LE pe 0x100000 -- SizeOfHeapReserve
  pe := pushUInt64LE pe 0x1000   -- SizeOfHeapCommit
  pe := pushUInt32LE pe 0        -- LoaderFlags
  pe := pushUInt32LE pe 16       -- NumberOfRvaAndSizes
  
  -- Data Directories (16 entries * 8 bytes = 128 bytes):
  -- Entry 0: Export Directory (0, 0)
  pe := pushUInt32LE (pushUInt32LE pe 0) 0
  -- Entry 1: Import Directory -> RVA (layout.idataRva + idtOffset), Size idtSize
  pe := pushUInt32LE (pushUInt32LE pe (layout.idataRva + idtOffset.toUInt32)) idtSize.toUInt32
  -- Entries 2 to 11: (0, 0)
  for _ in [0:10] do
    pe := pushUInt32LE (pushUInt32LE pe 0) 0
  -- Entry 12: IAT -> RVA layout.idataRva, Size totalIatSize
  pe := pushUInt32LE (pushUInt32LE pe layout.idataRva) totalIatSize.toUInt32
  -- Entries 13 to 15: (0, 0)
  for _ in [0:3] do
    pe := pushUInt32LE (pushUInt32LE pe 0) 0
    
  -- 5. Section Table (3 sections * 40 bytes = 120 bytes)
  -- .text Section Header
  pe := pe ++ serializeSectionHeader {
    name := ".text"
    virtualSize := textBytes.size.toUInt32
    virtualAddress := layout.textRva
    sizeOfRawData := layout.textRawSize.toUInt32
    pointerToRawData := textPtr.toUInt32
    characteristics := 0x60000020 -- CODE | EXECUTE | READ
  }
  
  -- .rdata Section Header
  pe := pe ++ serializeSectionHeader {
    name := ".rdata"
    virtualSize := (max 0x200 rdataBytes.size).toUInt32
    virtualAddress := layout.rdataRva
    sizeOfRawData := layout.rdataRawSize.toUInt32
    pointerToRawData := rdataPtr.toUInt32
    characteristics := 0xC0000040 -- INITIALIZED_DATA | READ | WRITE
  }
  
  -- .idata Section Header
  pe := pe ++ serializeSectionHeader {
    name := ".idata"
    virtualSize := layout.idataRawSize.toUInt32
    virtualAddress := layout.idataRva
    sizeOfRawData := layout.idataRawSize.toUInt32
    pointerToRawData := idataPtr.toUInt32
    characteristics := 0xC0000040 -- INITIALIZED_DATA | READ | WRITE
  }
  
  -- Pad Headers to FileAlignment (0x400 bytes)
  pe := padTo pe 0x400
  
  -- 6. .text Section Data
  pe := pe ++ padTo textBytes layout.textRawSize
  
  -- 7. .rdata Section Data
  pe := pe ++ padTo rdataBytes layout.rdataRawSize
  
  -- 8. .idata Section Data
  pe := pe ++ idata
  
  pe

/- REF: windows-pe-format#overview -/
/-- Emits a valid, fully formed 64-bit PE32+ (AMD64) executable image with dynamic section RVAs, alignments, and imports. -/
def emitPE32Executable (textBytes : ByteArray) (rdataBytes : ByteArray) (importNames : List String := ["GetStdHandle", "WriteFile", "ExitProcess"]) : ByteArray :=
  emitPE32ExecutableMultiDll textBytes rdataBytes [("KERNEL32.dll", importNames)]

end Gasm.Targets.Windows

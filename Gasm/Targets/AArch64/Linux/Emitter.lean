/-
Copyright 2026 Google LLC

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
import Gasm.Targets.AArch64.Linux.ELFFormat

namespace Gasm.Targets.AArch64.Linux

open Gasm.Core
open Gasm.Targets.ELF

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
def padTo (b : ByteArray) (targetSize : Nat) : ByteArray :=
  if b.size >= targetSize then b
  else
    let zeros := ByteArray.mk (Array.replicate (targetSize - b.size) (0 : UInt8))
    b ++ zeros

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
def buildShStrTab (names : List String) : ByteArray × List (String × UInt32) :=
  let rec loop (items : List String) (bytes : ByteArray) (offsets : List (String × UInt32)) :=
    match items with
    | [] => (bytes, offsets)
    | name :: rest =>
      let off := bytes.size.toUInt32
      let nameBytes := name.toUTF8.push 0
      loop rest (bytes ++ nameBytes) (offsets ++ [(name, off)])
  loop names (ByteArray.mk #[0]) []

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- Emits a valid static ELF64 binary image for AArch64 Linux. -/
def emitELF64Executable (baseVma : Address) (textBytes : ByteArray) (rodataBytes : ByteArray) : ByteArray := Id.run do
  let (shstrtabBytes, shstrOffsets) := buildShStrTab [".text", ".rodata", ".shstrtab"]
  let lookupOffset (name : String) : UInt32 :=
    match shstrOffsets.find? (fun (n, _) => n == name) with
    | some (_, off) => off
    | none => 0

  let layout := computeElf64Layout baseVma textBytes.size rodataBytes.size shstrtabBytes.size

  -- Program Headers
  let phdrText : Elf64_Phdr := {
    p_type   := PT_LOAD,
    p_flags  := PF_R ||| PF_X,
    p_offset := 0,
    p_vaddr  := baseVma,
    p_paddr  := baseVma,
    p_filesz := (layout.textOffset + textBytes.size).toUInt64,
    p_memsz  := (layout.textOffset + textBytes.size).toUInt64,
    p_align  := 0x1000
  }

  let phdrRodata : Elf64_Phdr := {
    p_type   := PT_LOAD,
    p_flags  := PF_R,
    p_offset := layout.rodataOffset.toUInt64,
    p_vaddr  := layout.rodataVma,
    p_paddr  := layout.rodataVma,
    p_filesz := rodataBytes.size.toUInt64,
    p_memsz  := rodataBytes.size.toUInt64,
    p_align  := 0x1000
  }

  -- Section Headers
  let shdrNull : Elf64_Shdr := {
    sh_name      := 0,
    sh_type      := SHT_NULL,
    sh_flags     := 0,
    sh_addr      := 0,
    sh_offset    := 0,
    sh_size      := 0,
    sh_addralign := 0
  }

  let shdrText : Elf64_Shdr := {
    sh_name      := lookupOffset ".text",
    sh_type      := SHT_PROGBITS,
    sh_flags     := SHF_ALLOC ||| SHF_EXECINSTR,
    sh_addr      := layout.textVma,
    sh_offset    := layout.textOffset.toUInt64,
    sh_size      := textBytes.size.toUInt64,
    sh_addralign := 16
  }

  let shdrRodata : Elf64_Shdr := {
    sh_name      := lookupOffset ".rodata",
    sh_type      := SHT_PROGBITS,
    sh_flags     := SHF_ALLOC,
    sh_addr      := layout.rodataVma,
    sh_offset    := layout.rodataOffset.toUInt64,
    sh_size      := rodataBytes.size.toUInt64,
    sh_addralign := 8
  }

  let shdrShstrtab : Elf64_Shdr := {
    sh_name      := lookupOffset ".shstrtab",
    sh_type      := SHT_STRTAB,
    sh_flags     := 0,
    sh_addr      := 0,
    sh_offset    := layout.shstrtabOffset.toUInt64,
    sh_size      := shstrtabBytes.size.toUInt64,
    sh_addralign := 1
  }

  -- ELF File Header (Explicitly EM_AARCH64)
  let ehdr : Elf64_Ehdr := {
    e_machine   := EM_AARCH64,
    e_entry     := layout.textVma,
    e_phoff     := 64,
    e_shoff     := layout.shdrsOffset.toUInt64,
    e_phnum     := 2,
    e_shnum     := 4,
    e_shstrndx  := 3
  }

  -- Buffer emission
  let mut elf := serializeElf64Header ehdr
  elf := elf ++ serializeElf64Phdr phdrText
  elf := elf ++ serializeElf64Phdr phdrRodata
  elf := padTo elf layout.textOffset
  elf := elf ++ textBytes
  elf := padTo elf layout.rodataOffset
  elf := elf ++ rodataBytes
  elf := padTo elf layout.shstrtabOffset
  elf := elf ++ shstrtabBytes
  elf := padTo elf layout.shdrsOffset
  elf := elf ++ serializeElf64Shdr shdrNull
  elf := elf ++ serializeElf64Shdr shdrText
  elf := elf ++ serializeElf64Shdr shdrRodata
  elf := elf ++ serializeElf64Shdr shdrShstrtab
  elf

end Gasm.Targets.AArch64.Linux

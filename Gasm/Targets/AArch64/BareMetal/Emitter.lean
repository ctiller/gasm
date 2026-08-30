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

namespace Gasm.Targets.AArch64.BareMetal

open Gasm.Core
open Gasm.Targets.ELF

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Memory layout descriptor for AArch64 bare-metal flat ELF executable loaded at 1 GB. -/
structure AArch64BareMetalLayout where
  loadBase      : UInt64 := 0x40000000 -- 1 GB physical base in QEMU virt
  headerPageSize: Nat    := 0x1000   -- 4 KB page for ELF headers
  entryAddr     : UInt64 := 0x40001000 -- Entry point just after headers (.text start)
  textSize      : Nat
  dataSize      : Nat
  totalFileSize : Nat
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Computes canonical AArch64 bare-metal memory and file layout. -/
def computeAArch64BareMetalLayout (textSize : Nat) (dataSize : Nat) : AArch64BareMetalLayout :=
  let headerSize := 0x1000
  let totalSize := headerSize + textSize + dataSize
  { loadBase := 0x40000000,
    headerPageSize := headerSize,
    entryAddr := 0x40001000,
    textSize := textSize,
    dataSize := dataSize,
    totalFileSize := totalSize }

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Emits an AArch64 image using the layout shared by the executable's loader. -/
def emitBareMetalELFExecutableWithLayout (layout : AArch64BareMetalLayout)
    (textBytes : ByteArray) (dataBytes : ByteArray) : ByteArray :=
  let elfHdr : Elf64_Ehdr := {
    e_machine := EM_AARCH64,
    e_entry   := layout.entryAddr,
    e_phnum   := 1
  }
  let phdrLoad : Elf64_Phdr := {
    p_type   := 1, -- PT_LOAD
    p_flags  := 7, -- PF_R | PF_W | PF_X
    p_offset := 0,
    p_vaddr  := layout.loadBase,
    p_paddr  := layout.loadBase,
    p_filesz := layout.totalFileSize.toUInt64,
    p_memsz  := layout.totalFileSize.toUInt64,
    p_align  := 0x1000
  }

  let hdrBytes := serializeElf64Header elfHdr
  let phdrLoadBytes := serializeElf64Phdr phdrLoad

  let prePad := hdrBytes ++ phdrLoadBytes
  let padSize := if prePad.size < layout.headerPageSize then layout.headerPageSize - prePad.size else 0
  let padBytes := ByteArray.mk (Array.replicate padSize 0)

  let headerPage := prePad ++ padBytes
  headerPage ++ textBytes ++ dataBytes

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Emits the canonical standalone AArch64 ELF image. -/
def emitBareMetalELFExecutable (textBytes : ByteArray) (dataBytes : ByteArray) : ByteArray :=
  emitBareMetalELFExecutableWithLayout
    (computeAArch64BareMetalLayout textBytes.size dataBytes.size) textBytes dataBytes

end Gasm.Targets.AArch64.BareMetal

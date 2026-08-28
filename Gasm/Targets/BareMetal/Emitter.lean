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
import Gasm.Targets.BareMetal.ELFFormat

namespace Gasm.Targets.BareMetal

open Gasm.Core

/- REF: docs/TARGETS/BARE_METAL.md#31-elf64-header-program-headers -/
/-- Emits a minimal standalone 64-bit ELF executable with Xen PVH boot note directly bootable by QEMU -kernel. -/
def emitBareMetalELFExecutable (textBytes : ByteArray) (dataBytes : ByteArray) : ByteArray :=
  let layout := computeBareMetalLayout textBytes.size dataBytes.size
  let elfHdr : ELF64Header := {
    e_entry := layout.entryAddr
  }
  let phdrLoad : ELF64ProgramHeader := {
    p_type   := 1, -- PT_LOAD
    p_flags  := 7, -- PF_R | PF_W | PF_X
    p_offset := 0,
    p_vaddr  := layout.loadBase,
    p_paddr  := layout.loadBase,
    p_filesz := layout.totalFileSize.toUInt64,
    p_memsz  := layout.totalFileSize.toUInt64,
    p_align  := 0x1000
  }
  let phdrNote : ELF64ProgramHeader := {
    p_type   := 4, -- PT_NOTE
    p_flags  := 4, -- PF_R
    p_offset := 0xB0,
    p_vaddr  := layout.loadBase + 0xB0,
    p_paddr  := layout.loadBase + 0xB0,
    p_filesz := 20,
    p_memsz  := 20,
    p_align  := 4
  }
  let pvhNote : XenPVHNote := {
    entryAddr := layout.entryAddr.toUInt32
  }

  let hdrBytes := serializeELF64Header elfHdr
  let phdrLoadBytes := serializeELF64ProgramHeader phdrLoad
  let phdrNoteBytes := serializeELF64ProgramHeader phdrNote
  let pvhNoteBytes := serializeXenPVHNote pvhNote

  let prePad := hdrBytes ++ phdrLoadBytes ++ phdrNoteBytes ++ pvhNoteBytes
  let padSize := if prePad.size < layout.headerPageSize then layout.headerPageSize - prePad.size else 0
  let padBytes := ByteArray.mk (Array.replicate padSize 0)

  let headerPage := prePad ++ padBytes
  headerPage ++ textBytes ++ dataBytes

end Gasm.Targets.BareMetal

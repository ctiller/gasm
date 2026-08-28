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

namespace Gasm.Targets.ELF

open Gasm.Core

/- REF: docs/TARGETS/BARE_METAL.md#32-xen-pvh-elf-note-xenelfnotephys32entry -/
/-- Xen PVH ELF boot note (XEN_ELFNOTE_PHYS32_ENTRY) required by QEMU -kernel. -/
structure XenPVHNote where
  namesz    : UInt32 := 4  -- "Xen\0" length
  descsz    : UInt32 := 4  -- 32-bit physical entry point address size
  noteType  : UInt32 := 18 -- XEN_ELFNOTE_PHYS32_ENTRY
  entryAddr : UInt32
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/BARE_METAL.md#32-xen-pvh-elf-note-xenelfnotephys32entry -/
/-- Serializes a XenPVHNote into a 20-byte ByteArray. -/
def serializeXenPVHNote (note : XenPVHNote) : ByteArray :=
  writeUInt32LE note.namesz ++
  writeUInt32LE note.descsz ++
  writeUInt32LE note.noteType ++
  ByteArray.mk #[0x58, 0x65, 0x6E, 0x00] ++ -- "Xen\0"
  writeUInt32LE note.entryAddr

end Gasm.Targets.ELF

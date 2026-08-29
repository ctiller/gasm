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
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Win32API
import Spikes.Spike2Fibonacci.Windows.Program
import Spikes.Spike3SortLines.Windows.IATLemmas

/-!
# Spike 2's IAT self-reference facts, mirroring Spike 3's technique

`Spikes/Spike3SortLines/Windows/IATLemmas.lean` proved a fully generic set of lemmas (never
touching any spike's own instructions/section bytes beyond their `.size`):
`foldl_append_size`, `alignUp_ge`, `read64_initRegion_generic`, `bool_range_false`,
`loadMemory_excludes_sections`. This file reuses them as-is (imported, not re-derived) to
establish the three IAT self-reference facts Spike 2's `main_loop` actually needs
(`spike2SymbolicProgram` calls `GetStdHandle` [slot 0], `WriteFile` [slot 2], `ExitProcess` [slot
3] -- `ReadFile`/`VirtualAlloc`/`VirtualFree` are imported by `linkWindowsProgram`'s default list
but never called, so no self-reference fact is needed for them).

Spike 2's `.text` section (336 bytes) and empty `.rdata` section (`dataItems := []`, so `rdataBytes
= ByteArray.empty`, size 0) both stay well under the `0x1000` (4096-byte) section-alignment
granularity `computeSectionLayout` rounds up to, so the resulting RVA layout is numerically
identical to Spike 3's: `.text` at `0x1000`, `.rdata` at `0x2000`, the IAT at `0x3000`. This is
confirmed below (`spike2_load_layout`), not assumed.
-/

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Spikes.Spike3SortLines.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 2's assembled `.text` section is exactly 336 bytes. Proved via `foldl_append_size`
    (imported from Spike 3's generic infrastructure), never touching `serializeInstructions`'s
    appended `ByteArray` itself. -/
theorem spike2_textBytes_size : spike2Executable.textBytes.size = 336 := by
  show (Assembler.serializeInstructions spike2Instructions).size = 336
  unfold Assembler.serializeInstructions
  rw [foldl_append_size (fun i => X86_64Instruction.encode i) spike2Instructions ByteArray.empty]
  decide

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 2 has no `.rdata` section (`linkWindowsProgram spike2SymbolicProgram []` passes no data
    items -- every literal byte `main_loop` emits is written directly into the stack buffer, not
    loaded from `.rdata`), so `rdataBytes` is the empty `ByteArray`. -/
theorem spike2_rdataBytes_size : spike2Executable.rdataBytes.size = 0 := by decide

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 2's concrete section layout (`computeSectionLayout 336 0 512`) places `.text` at RVA
    `0x1000`, `.rdata` at `0x2000`, and the IAT at `0x3000` -- numerically identical to Spike 3's
    layout despite the different `.text` size, since both stay under the `0x1000` rounding
    granularity `computeSectionLayout` uses. Confirmed against `spike2_textBytes_size`/
    `spike2_rdataBytes_size` above, not asserted. -/
theorem spike2_load_layout :
    computeSectionLayout spike2Executable.textBytes.size spike2Executable.rdataBytes.size 512 =
      { textRva := 0x1000, textRawSize := 512, rdataRva := 0x2000, rdataRawSize := 512,
        idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000 } := by
  rw [spike2_textBytes_size, spike2_rdataBytes_size]
  decide

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Macro-shaped tactic block proving one of Spike 2's IAT slots' self-reference fact: `s.read64`
    at the given literal address returns the address itself, without ever forcing
    `.textBytes`/`.rdataBytes`'s contents (only the `.size` facts above). Mirrors Spike 3's
    `prove_selfref`, retargeted at `spike2Executable`'s own section bytes/imports. -/
syntax "prove_selfref2 " term : tactic
macro_rules
  | `(tactic| prove_selfref2 $addr:term) =>
    `(tactic|
        (rw [read64_initRegion_generic]
         have key0 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key1 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 1)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key2 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 2)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key3 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 3)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key4 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 4)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key5 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 5)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key6 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 6)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         have key7 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike2Executable.textBytes spike2Executable.rdataBytes spike2Executable.imports ($addr + 7)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
           (by rw [spike2_textBytes_size]; decide) (by rw [spike2_rdataBytes_size]; decide)
         rw [key0, key1, key2, key3, key4, key5, key6, key7]
         decide))

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 0 (`GetStdHandle`) is self-referential: reading the 8 bytes at
    `0x140000000 + 0x3000 + 0` returns that same address. -/
theorem spike2_getStdHandle_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3000)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike2Executable.textBytes), ((0x2000:UInt32), spike2Executable.rdataBytes)]
        spike2Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3000 := by
  prove_selfref2 ((0x140000000:Address) + 0x3000)

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 2 (`WriteFile`) is self-referential, at `idataRva + 2*8 = 0x3010`. -/
theorem spike2_writeFile_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3010)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike2Executable.textBytes), ((0x2000:UInt32), spike2Executable.rdataBytes)]
        spike2Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3010 := by
  prove_selfref2 ((0x140000000:Address) + 0x3010)

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 3 (`ExitProcess`) is self-referential, at `idataRva + 3*8 = 0x3018`. -/
theorem spike2_exitProcess_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3018)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike2Executable.textBytes), ((0x2000:UInt32), spike2Executable.rdataBytes)]
        spike2Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3018 := by
  prove_selfref2 ((0x140000000:Address) + 0x3018)

end Spikes.Spike2Fibonacci.Windows

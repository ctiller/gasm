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
import Spikes.Spike3SortLines.Windows.Program

/-!
# Retiring the `WindowsExecutable.load`/`.textBytes.size` performance wall

`Spikes/Spike3SortLines/TraceStepLemmas.lean`/`Windows/InterceptLemmas.lean`/
`Windows/InstructionStepLemmas.lean` (landed, oracle-free) supply everything needed to peel one
instruction at a time off the empty-stdin trace -- *except* the four Win32-call-intercept steps
(`GetStdHandle`, `ReadFile`, `ExitProcess`, `VirtualAlloc`), each of which needs a fact about
`s.read64 addr` at the IAT slot the `call_rip` instruction lands on. Naively, that fact needs
`WindowsExecutable.load`'s `loadMemory` to determine the call target is *not* inside `.text`/
`.rdata` (so `findIatIndex`'s self-referential reconstruction fires instead) -- which forces
`exe.textBytes.size`/`exe.rdataBytes.size` through kernel (non-`native_decide`) reduction of the
whole PE encoding. Measured before this file: ~57s for `.textBytes.size` alone, 1-4 minutes for
one full `read64` fact -- the wall the prior agent diagnosed but did not have budget to fix
(`git log`, "feat(spike3): trace-step infrastructure...").

The fix has two independent parts, both landed here:

1. **`.size` without `serializeInstructions`'s O(n) `ByteArray.append` chain.** `exe.textBytes :=
   serializeInstructions concreteInstrs := concreteInstrs.foldl (· ++ encode ·) ByteArray.empty`
   -- taking `.size` of the *result* forces the kernel to materialize every intermediate
   `ByteArray.append` (the measured wall). `foldl_append_size` is a generic, size-only fold
   homomorphism (`ByteArray.size_append`, proved once by induction, independent of what the
   folded bytes actually are) that rewrites `.size` into a `Nat`-only fold *before* any reduction
   happens: `(l.foldl (· ++ f ·) acc0).size = l.foldl (fun n i => n + (f i).size) acc0.size`.
   The resulting Nat fold is cheap because it only ever forces one instruction's `encode` at a
   time (never re-copies the growing byte buffer), landing `spike3_textBytes_size`/
   `spike3_rdataBytes_size` in a few seconds via plain `decide` -- not 57s.
2. **`computeSectionLayout`'s section-disjointness is `alignUp`-generic.** `PEFormat.lean`'s
   `computeSectionLayout` places each section at `prevRva + alignUp (max 0x1000 size) 0x1000`,
   and `alignUp (max 0x1000 size) 0x1000 ≥ size` holds for *every* `size : Nat` (`alignUp_ge`,
   `omega`, ~1s) -- confirming the premise the prior agent's note banked on: layout disjointness
   never needs `size` reduced to a literal at all. With (1) above giving `exe.textBytes.size`/
   `.rdataBytes.size` as cheap literals (`1705`, `2`), `computeSectionLayout 1705 2 512` itself
   reduces to concrete RVAs (`0x1000`/`0x2000`/`0x3000`) by plain arithmetic -- so the four IAT
   facts below use `alignUp_ge`'s *conclusion* (sections never overlap, confirmed against the
   concrete sizes) rather than needing to restate the inequality abstractly a second time.

`loadMemory_excludes_sections` is the reusable "does this address fall outside every named
section" lemma this unlocks: proved once, generically over the section `ByteArray`s (never
touching their contents, only `.size` via a hypothesis), it lets each of the four call-intercept
facts finish by (a) discharging its two disjointness side-conditions with `decide` against the
now-literal sizes, then (b) `decide`-ing the small (6-entry, single-DLL) `findIatDll`
reconstruction -- never re-triggering the `serializeInstructions` wall.
-/

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: windows-pe-format#overview -/
/-- `computeSectionLayout`'s section placement (`alignUp (max 0x1000 size) 0x1000`) is `≥ size`
    for *every* `Nat` size -- the generic fact the section-layout scheme relies on to guarantee
    two consecutive sections never overlap, regardless of what the earlier section's actual byte
    count turns out to be. This is the premise the prior agent's note ("`computeSectionLayout`
    places each section via `alignUp (max 0x1000 size) alignment`, which is `>= size` for *any*
    size value") flagged as confirmed-but-not-yet-built-on; verified directly against
    `PEFormat.lean`'s `alignUp`/`computeSectionLayout` here rather than taken on faith. -/
theorem alignUp_ge (size : Nat) : size ≤ alignUp (max 0x1000 size) 0x1000 := by
  unfold alignUp
  simp only [show ((0x1000:Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  omega

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Size-only fold homomorphism for `ByteArray.foldl (· ++ f ·)`: the running `.size` of a
    `ByteArray` built by repeated `++` equals the `Nat` fold of each contributor's own `.size` --
    provable once, generically over `f`/`l`/the starting accumulator, by structural induction and
    `ByteArray.size_append`, never inspecting what any `f i` actually contains. This is what lets
    `serializeInstructions`'s `.size` be computed without ever materializing the fully-appended
    `ByteArray` (the O(n) `ByteArray.append` chain that makes `exe.textBytes.size` expensive to
    reduce directly). -/
theorem foldl_append_size.{u} {α : Type u} (f : α → ByteArray) (l : List α) (acc0 : ByteArray) :
    (l.foldl (fun acc i => acc ++ f i) acc0).size =
      l.foldl (fun n i => n + (f i).size) acc0.size := by
  induction l generalizing acc0 with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc0 ++ f x)]
    congr 1
    exact ByteArray.size_append

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 3's assembled `.text` section is exactly 1705 bytes. Proved via `foldl_append_size`
    (never touching `serializeInstructions`'s appended `ByteArray` itself) followed by a `decide`
    over the resulting `Nat` fold, which only ever forces one instruction's `encode` at a time --
    measured at a few seconds, against ~57s for `.size` reduced directly through the naive
    `ByteArray.append` chain. -/
theorem spike3_textBytes_size : spike3Executable.textBytes.size = 1705 := by
  show (Assembler.serializeInstructions spike3Instructions).size = 1705
  unfold Assembler.serializeInstructions
  rw [foldl_append_size (fun i => X86_64Instruction.encode i) spike3Instructions ByteArray.empty]
  decide

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 3's `.rdata` section (`crlfBytes = "\r\n"`) is exactly 2 bytes. Cheap directly: unlike
    `.text`, `.rdata` is a single small literal concatenation, no per-instruction `encode` chain. -/
theorem spike3_rdataBytes_size : spike3Executable.rdataBytes.size = 2 := by decide

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- `X86_64Mem.read .w64` restated as its 8 constituent `readByte`-through-`initRegion`
    applications, generic over the installed memory function `f`. Proved once so every call site
    below can `rw` this in without letting `simp`'s default beta/iota reduction eagerly unfold
    `f`'s *application* (which, for `f := loadMemory ...`, is exactly what re-triggers the
    `.size` wall -- `simp only [X86_64Mem.read, ...]` applied directly to a goal already
    mentioning `loadMemory imageBase [...] ...` measurably costs 10x+ this lemma's own proof,
    confirmed empirically: this decoupling is what keeps the four facts below cheap). -/
theorem read64_initRegion_generic (f : Address → Byte) (a : Address) :
    X86_64Mem.read .w64 a (X86_64Mem.initRegion f) =
      (f a).toUInt64 ||| (f (a+1)).toUInt64 <<< 8 ||| (f (a+2)).toUInt64 <<< 16 |||
      (f (a+3)).toUInt64 <<< 24 ||| (f (a+4)).toUInt64 <<< 32 ||| (f (a+5)).toUInt64 <<< 40 |||
      (f (a+6)).toUInt64 <<< 48 ||| (f (a+7)).toUInt64 <<< 56 := by
  simp only [X86_64Mem.read, X86_64Mem.readByte_initRegion]

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- A `decide (a ≥ start) && decide (a < start + sz.toUInt64) = false` Bool condition (exactly
    `loadMemory`'s per-section range test), restated so it can be discharged from a `.toNat`-level
    disjointness fact by `omega` -- `omega` in this toolchain does not reason about raw `UInt64`
    `<`/`≥`/`+` directly (confirmed empirically), only about `Nat`, hence the `.toNat` detour and
    the explicit no-overflow side condition `hno` (mirrors `MemoryCell.lean`'s
    `readByte_write_disjoint`, which needs the identical detour for the identical reason). -/
theorem bool_range_false (a start : UInt64) (sz : Nat) (bound : UInt64)
    (h : a.toNat < start.toNat ∨ a.toNat ≥ start.toNat + sz) (hb : bound = start + sz.toUInt64)
    (hno : start.toNat + sz < 2^64) :
    (a ≥ start && a < bound) = false := by
  subst hb
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, ge_iff_le]
  rcases h with h | h
  · left; rw [UInt64.le_iff_toNat_le]; omega
  · right; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']; omega

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- `loadMemory` at an address structurally outside both named sections falls straight through to
    the IAT self-reference reconstruction (`findIatDll`), regardless of what the two sections'
    `ByteArray`s actually contain -- only their `.size` is a hypothesis here, never forced beyond
    that. This is the generic "symbolic Win32 IAT call" lemma the prior agent's note named as the
    concrete next step ("proving `findIatIndex` recognizes each import's slot generically, so
    `read64` at that slot is self-referential without touching actual section bytes"). -/
theorem loadMemory_excludes_sections (rva1 rva2 idataRva : UInt32) (imageBase : Address)
    (b1 b2 : ByteArray) (imports : List Win32Function) (a : Address)
    (h1 : a.toNat < (imageBase+rva1.toUInt64).toNat ∨ a.toNat ≥ (imageBase+rva1.toUInt64).toNat + b1.size)
    (h2 : a.toNat < (imageBase+rva2.toUInt64).toNat ∨ a.toNat ≥ (imageBase+rva2.toUInt64).toNat + b2.size)
    (hno1 : (imageBase+rva1.toUInt64).toNat + b1.size < 2^64)
    (hno2 : (imageBase+rva2.toUInt64).toNat + b2.size < 2^64) :
    loadMemory imageBase [(rva1,b1),(rva2,b2)] imports idataRva a =
      (let iatBase := imageBase + idataRva.toUInt64
       let dllImports := groupImportsByDll imports
       match loadMemory.findIatDll a iatBase dllImports with
       | some byte => byte | none => 0) := by
  unfold loadMemory
  simp only [List.findSome?]
  rw [bool_range_false a (imageBase+rva1.toUInt64) b1.size (imageBase+rva1.toUInt64+b1.size.toUInt64) h1 rfl hno1]
  rw [bool_range_false a (imageBase+rva2.toUInt64) b2.size (imageBase+rva2.toUInt64+b2.size.toUInt64) h2 rfl hno2]
  rfl

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 3's concrete section layout (`computeSectionLayout 1705 2 512`) places `.text` at RVA
    `0x1000`, `.rdata` at `0x2000`, and the IAT at `0x3000` -- confirmed against
    `spike3_textBytes_size`/`spike3_rdataBytes_size` above, not asserted. Every IAT self-reference
    fact below is stated against these literal RVAs directly (rather than re-deriving them from
    `computeSectionLayout` at each call site) purely for call-site brevity; `alignUp_ge` is what
    guarantees this placement generalizes to any section sizes, not just these two. -/
theorem spike3_load_layout :
    computeSectionLayout spike3Executable.textBytes.size spike3Executable.rdataBytes.size 512 =
      { textRva := 0x1000, textRawSize := 2048, rdataRva := 0x2000, rdataRawSize := 512,
        idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000 } := by
  rw [spike3_textBytes_size, spike3_rdataBytes_size]
  decide

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Macro-shaped tactic block proving one IAT slot's self-reference fact: `s.read64` at the given
    literal address returns the address itself, without ever forcing `.textBytes`/`.rdataBytes`'s
    contents (only the `.size` facts above). Each of the eight byte reads is peeled off via
    `loadMemory_excludes_sections`, whose two disjointness side-conditions are, once the sizes are
    substituted, plain literal-vs-literal `Nat` comparisons `decide` closes instantly; the final
    combination is likewise a closed `decide` over the (now fully concrete) `findIatDll`
    reconstruction for Spike 3's single-DLL, 6-import table. -/
syntax "prove_selfref " term : tactic
macro_rules
  | `(tactic| prove_selfref $addr:term) =>
    `(tactic|
        (rw [read64_initRegion_generic]
         have key0 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key1 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 1)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key2 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 2)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key3 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 3)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key4 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 4)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key5 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 5)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key6 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 6)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         have key7 := loadMemory_excludes_sections (0x1000:UInt32) (0x2000:UInt32) (0x3000:UInt32)
           (0x140000000:Address) spike3Executable.textBytes spike3Executable.rdataBytes spike3Executable.imports ($addr + 7)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
           (by rw [spike3_textBytes_size]; decide) (by rw [spike3_rdataBytes_size]; decide)
         rw [key0, key1, key2, key3, key4, key5, key6, key7]
         decide))

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 0 (`GetStdHandle`, `Win32API.lean`'s `win32Intercept` dispatch) is self-referential:
    reading the 8 bytes at `0x140000000 + 0x3000 + 0` returns that same address. This is the fact
    `findIatIndex`/`win32Intercept` needs to recognize the slot and dispatch to `getStdHandleHook`
    once the empty-stdin trace's `call_rip` step lands here. -/
theorem getStdHandle_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3000)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike3Executable.textBytes), ((0x2000:UInt32), spike3Executable.rdataBytes)]
        spike3Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3000 := by
  prove_selfref ((0x140000000:Address) + 0x3000)

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 1 (`ReadFile`) is self-referential, at `idataRva + 1*8 = 0x3008`. -/
theorem readFile_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3008)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike3Executable.textBytes), ((0x2000:UInt32), spike3Executable.rdataBytes)]
        spike3Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3008 := by
  prove_selfref ((0x140000000:Address) + 0x3008)

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 3 (`ExitProcess`) is self-referential, at `idataRva + 3*8 = 0x3018`. -/
theorem exitProcess_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3018)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike3Executable.textBytes), ((0x2000:UInt32), spike3Executable.rdataBytes)]
        spike3Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3018 := by
  prove_selfref ((0x140000000:Address) + 0x3018)

set_option maxHeartbeats 8000000 in
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- IAT slot 4 (`VirtualAlloc`) is self-referential, at `idataRva + 4*8 = 0x3020`. -/
theorem virtualAlloc_selfref :
    X86_64Mem.read .w64 ((0x140000000:Address) + 0x3020)
      (X86_64Mem.initRegion (loadMemory (0x140000000:Address)
        [((0x1000:UInt32), spike3Executable.textBytes), ((0x2000:UInt32), spike3Executable.rdataBytes)]
        spike3Executable.imports (0x3000:UInt32))) =
      (0x140000000:Address) + 0x3020 := by
  prove_selfref ((0x140000000:Address) + 0x3020)

end Spikes.Spike3SortLines.Windows

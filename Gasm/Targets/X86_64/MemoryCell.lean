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

namespace Gasm.Targets.X86_64

open Gasm.Core

/- REF: docs/MEMORY_HOOK.md#3-layer-s-the-semantic-hook -/
/-- Memory access width, in bytes. The four widths x86-64's 88 current forms and the
    expansion's Wave A/B need. -/
inductive MemWidth where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#3-layer-s-the-semantic-hook -/
/-- Byte count of a memory access width. -/
def MemWidth.bytes : MemWidth → Nat
  | .w8  => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Whether a declared memory access reads or writes machine memory. -/
inductive MemAccessKind where
  | load | store
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- Sealed x86-64 machine memory cell. `mk` and `raw` are `private` to this module (module-scoped
    in Lean 4, verified to elaborate at this repo's pinned toolchain v4.33.1): outside this file,
    no term can construct an `X86_64Memory` from an arbitrary `Address → Byte` function, nor
    project one back out. `X86_64Mem.read`/`X86_64Mem.write` below -- defined in this same file,
    the only place the seal permits touching `raw` -- are consequently the only functions in the
    whole tree that can observe or change machine memory bytes; every other module (instruction
    `step`s, Win32 interceptor hooks, loaders, proof-side observation) is structurally forced
    through them. This is Law 13 preference-tier 1: the bypass is unrepresentable, not linted. -/
structure X86_64Memory where
  private mk ::
  private raw : Address → Byte

namespace X86_64Mem

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- Reads a single byte. The only place outside `write`/`initRegion` that projects `raw`. -/
def readByte (m : X86_64Memory) (a : Address) : Byte := m.raw a

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- Writes a single byte, leaving every other address unchanged. -/
def writeByte (m : X86_64Memory) (a : Address) (v : Byte) : X86_64Memory :=
  ⟨fun addr => if addr == a then v else m.raw addr⟩

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Width-indexed little-endian read -- one of the two functions that can observe machine memory
    bytes (the other is `write`). Hand-unrolled per width (rather than a generic fold) so it
    stays exactly the byte ladder `X86_64MachineState.read64` etc. used before sealing, which is
    what keeps every existing `rfl` step lemma closing once these become thin `abbrev`s over it
    (`docs/MEMORY_HOOK.md` §7). -/
def read (w : MemWidth) (a : Address) (m : X86_64Memory) : UInt64 :=
  match w with
  | .w8 => (readByte m a).toUInt64
  | .w16 =>
    (readByte m a).toUInt64 |||
    ((readByte m (a + 1)).toUInt64 <<< 8)
  | .w32 =>
    (readByte m a).toUInt64 |||
    ((readByte m (a + 1)).toUInt64 <<< 8) |||
    ((readByte m (a + 2)).toUInt64 <<< 16) |||
    ((readByte m (a + 3)).toUInt64 <<< 24)
  | .w64 =>
    (readByte m a).toUInt64 |||
    ((readByte m (a + 1)).toUInt64 <<< 8) |||
    ((readByte m (a + 2)).toUInt64 <<< 16) |||
    ((readByte m (a + 3)).toUInt64 <<< 24) |||
    ((readByte m (a + 4)).toUInt64 <<< 32) |||
    ((readByte m (a + 5)).toUInt64 <<< 40) |||
    ((readByte m (a + 6)).toUInt64 <<< 48) |||
    ((readByte m (a + 7)).toUInt64 <<< 56)

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Width-indexed little-endian write -- the ONLY function (with `read`) that can touch machine
    memory bytes from outside this file. Hand-unrolled per width for the same `rfl`-preservation
    reason as `read`. -/
def write (w : MemWidth) (a : Address) (v : UInt64) (m : X86_64Memory) : X86_64Memory :=
  match w with
  | .w8 => writeByte m a v.toUInt8
  | .w16 =>
    ⟨fun addr =>
      if addr == a then v.toUInt8
      else if addr == a + 1 then (v >>> 8).toUInt8
      else m.raw addr⟩
  | .w32 =>
    ⟨fun addr =>
      if addr == a then v.toUInt8
      else if addr == a + 1 then (v >>> 8).toUInt8
      else if addr == a + 2 then (v >>> 16).toUInt8
      else if addr == a + 3 then (v >>> 24).toUInt8
      else m.raw addr⟩
  | .w64 =>
    ⟨fun addr =>
      if addr == a then v.toUInt8
      else if addr == a + 1 then (v >>> 8).toUInt8
      else if addr == a + 2 then (v >>> 16).toUInt8
      else if addr == a + 3 then (v >>> 24).toUInt8
      else if addr == a + 4 then (v >>> 32).toUInt8
      else if addr == a + 5 then (v >>> 40).toUInt8
      else if addr == a + 6 then (v >>> 48).toUInt8
      else if addr == a + 7 then (v >>> 56).toUInt8
      else m.raw addr⟩

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- Loader-facing bulk-install entry point: wraps an arbitrary total `Address → Byte` function
    (a computed image layout) as a sealed `X86_64Memory` in one step. Installing an executable
    image is a legitimate bulk write; naming it keeps loaders inside the chokepoint instead of
    allowlisted around it, per `docs/MEMORY_HOOK.md` §3.2. -/
def initRegion (f : Address → Byte) : X86_64Memory := ⟨f⟩

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- The all-zero memory image every `initMachineState`/`default`/loader-adjacent construction in
    the tree used to spell as a raw `fun _ => 0` literal before sealing made that unrepresentable
    outside this file. -/
def zero : X86_64Memory := initRegion (fun _ => 0)

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- Bulk byte-range write, built from `writeByte`: installs `bytes` starting at `a`, one byte per
    increasing address. The hook-blessed replacement for the raw `memory := fun a => if a ∈
    [dest, dest+n) then ... else s.memory a` pattern `Win32API.lean`'s syscall interceptor hooks
    (`readFileHook`, `recvHook`, `writeFileHook`) and `Linux/Syscall.lean`'s `sysReadHook` used
    before sealing. -/
def writeBytes (a : Address) (bytes : List Byte) (m : X86_64Memory) : X86_64Memory :=
  let rec loop (offset : Nat) : List Byte → X86_64Memory → X86_64Memory
    | [], m' => m'
    | b :: rest, m' => loop (offset + 1) rest (writeByte m' (a + offset.toUInt64) b)
  loop 0 bytes m

--------------------------------------------------------------------------------------------------
-- §3.4 lemma set (byte-granular half): read-over-write and `initRegion` read-back, proved once
-- here so every width-indexed fact in `Memory.lean` reduces to these instead of re-deriving
-- byte-selection arithmetic per width pair (`docs/MEMORY_HOOK.md` §3.4).
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Read-over-write, same address, byte-granular: a single-byte write is read back exactly. -/
@[simp] theorem readByte_writeByte_same (m : X86_64Memory) (a : Address) (v : Byte) :
    readByte (writeByte m a v) a = v := by
  simp [readByte, writeByte]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Read-over-write, disjoint addresses, byte-granular: a single-byte write at `a` never disturbs
    a read at any other address. -/
@[simp] theorem readByte_writeByte_diff (m : X86_64Memory) (a a' : Address) (v : Byte) (h : a' ≠ a) :
    readByte (writeByte m a v) a' = readByte m a' := by
  simp [readByte, writeByte, h]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Read-over-write, disjoint ranges: a width-`w` write at `a` never disturbs a byte read at any
    address outside `[a, a+w.bytes)`. This is the one generic fact every `writesWithin` frame
    lemma (§3.3) reduces to. `hno` is the no-overflow side condition `docs/MEMORY_HOOK.md` §3.4
    names (matching `MemoryPerm.validRange`'s convention): without it, `a`'s range could wrap
    past `2⁶⁴` and make an address that is numerically "less than `a`" actually alias into the
    write's range, which `omega` catches as a genuine counterexample if this hypothesis is
    dropped. -/
theorem readByte_write_disjoint (w : MemWidth) (a : Address) (v : UInt64) (m : X86_64Memory) (a' : Address)
    (hno : a.toNat + w.bytes ≤ 2 ^ 64)
    (h : a'.toNat < a.toNat ∨ a.toNat + w.bytes ≤ a'.toNat) :
    readByte (write w a v m) a' = readByte m a' := by
  have hbytes1 : 1 ≤ w.bytes := by cases w <;> decide
  have ha1 : a' ≠ a := by intro he; subst he; omega
  cases w with
  | w8 => simpa [write] using readByte_writeByte_diff m a a' v.toUInt8 ha1
  | w16 =>
    have ha2 : a' ≠ a + 1 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    simp only [write]; unfold readByte
    simp [ha1, ha2]
  | w32 =>
    have ha2 : a' ≠ a + 1 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha3 : a' ≠ a + 2 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha4 : a' ≠ a + 3 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    simp only [write]; unfold readByte
    simp [ha1, ha2, ha3, ha4]
  | w64 =>
    have ha2 : a' ≠ a + 1 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha3 : a' ≠ a + 2 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha4 : a' ≠ a + 3 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha5 : a' ≠ a + 4 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha6 : a' ≠ a + 5 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha7 : a' ≠ a + 6 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    have ha8 : a' ≠ a + 7 := by intro he; rw [he] at h; simp [MemWidth.bytes] at h hno; omega
    simp only [write]; unfold readByte
    simp [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `initRegion` read-back: reading any byte of an installed image returns exactly what the
    installing function says at that address. -/
theorem readByte_initRegion (f : Address → Byte) (a : Address) :
    readByte (initRegion f) a = f a := rfl

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `zero`'s bytes are all zero. -/
theorem readByte_zero (a : Address) : readByte zero a = 0 := rfl

end X86_64Mem

end Gasm.Targets.X86_64

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
    the names `X86_64Memory.mk` and `X86_64Memory.raw` do not resolve, `⟨f⟩` and `{ raw := f }`
    are rejected, and `m.raw`/`m.1` are rejected.

    **What the seal is and is not (corrected 2026-08-28 by adversarial review; the earlier
    wording here claimed more than `private` delivers).** Two limits are load-bearing:

    1. `private mk ::` does NOT privatize the auto-generated eliminators. `X86_64Memory.casesOn`,
       `.rec` and `.recOn` remain public, and `m.casesOn (fun f => f)` yields the raw
       `Address → Byte` from any module -- it elaborates, compiles, and runs.
    2. That leak is nonetheless SEMANTICALLY EMPTY, because the blessed API is itself total and
       public: `fun a => X86_64Mem.readByte m a` is definitionally the very same function
       (`rfl`-equal to `m.casesOn (fun f => f)`), and `initRegion` accepts an arbitrary
       `Address → Byte` by design so loaders can install an image. Byte-level observation and
       bulk construction are *deliberately* available; hiding them was never the point.

    So the property this seal actually buys is not confidentiality of the bytes -- it is that
    every memory touch in the tree goes through a NAMED function in this file
    (`readByte`/`writeByte`/`read`/`write`/`initRegion`/`writeBytes`), so the set of memory
    access sites is enumerable and future instrumentation (fault checks, Law 11 permission
    checks, cost accounting) has exactly one place to land. That is an auditable-chokepoint
    property, and it is enforced at Law 13 preference-tier 3 by
    `Gasm/Targets/X86_64/MemoryFrameAudit.lean`'s seal audit, which fails the build if any
    declaration outside this module mentions `X86_64Memory.casesOn`/`.rec`/`.recOn`. It is NOT
    tier 1: the bypass is linted, not unrepresentable. See `docs/MEMORY_HOOK.md` §3.2. -/
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
/-- Two byte offsets below 8 from the same base are distinct addresses, unconditionally. Unlike
    `readByte_write_disjoint`'s external `a'`, this needs no no-overflow side condition: the
    offsets are bounded constants `< 8`, so `a + i` and `a + j` cannot collide mod `2⁶⁴` for
    `i ≠ j` whatever `a` is (`X86_64Mem.read64_write64_same`'s docstring in `Memory.lean` states
    the same fact informally; this is it as a reusable lemma). -/
theorem addr_offset_ne (a : Address) (i j : Nat) (hi : i < 8) (hj : j < 8) (hij : i ≠ j) :
    a + i.toUInt64 ≠ a + j.toUInt64 := by
  intro he
  have h := congrArg UInt64.toNat he
  simp [UInt64.toNat_add, Nat.toUInt64, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  omega

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Read-over-write, INSIDE the written range: within `[a, a + w.bytes)` a width-`w` write's
    bytes are determined entirely by the value written -- the underlying memory is irrelevant, so
    two different pre-images yield the same byte. This is the dual of `readByte_write_disjoint`
    (which covers the outside) and the one generic fact every `ReadsWithin` frame lemma's
    store-footprint conjunct reduces to: a store form's written bytes are a function of its
    operands alone, so two states agreeing outside memory write identical bytes regardless of
    what memory held before. Without it each of the 9 store forms would re-derive per-width
    byte-selection arithmetic by hand. -/
theorem readByte_write_inside (w : MemWidth) (a : Address) (v : UInt64) (m1 m2 : X86_64Memory)
    (k : Nat) (hk : k < w.bytes) :
    readByte (write w a v m1) (a + k.toUInt64) = readByte (write w a v m2) (a + k.toUInt64) := by
  have hne := addr_offset_ne a
  cases w <;> simp only [MemWidth.bytes] at hk
  · have hk0 : k = 0 := by omega
    subst hk0; simp [write, readByte, writeByte, Nat.toUInt64]
  · have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with h|h <;> subst h <;>
      simp [write, readByte, writeByte, Nat.toUInt64, hne]
  · have hk0 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk0 with h|h|h|h <;> subst h <;>
      simp [write, readByte, writeByte, Nat.toUInt64, hne]
  · have hk0 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk0 with h|h|h|h|h|h|h|h <;> subst h <;>
      simp [write, readByte, writeByte, Nat.toUInt64, hne]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `initRegion` read-back: reading any byte of an installed image returns exactly what the
    installing function says at that address. -/
theorem readByte_initRegion (f : Address → Byte) (a : Address) :
    readByte (initRegion f) a = f a := rfl

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `zero`'s bytes are all zero. -/
theorem readByte_zero (a : Address) : readByte zero a = 0 := rfl

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Reading any width at any address of `zero` yields `0` -- the fact every proof that used to
    state `s.memory = (fun _ => 0)` and then `simp [X86_64MachineState.read64]` through it now
    needs one extra step for (`docs/MEMORY_HOOK.md` §7's "gains one definitional layer"). -/
@[simp] theorem read_zero (w : MemWidth) (a : Address) : read w a zero = 0 := by
  cases w <;> simp [read, readByte_zero]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Width decomposition: a width-`w` read is determined entirely by its `w.bytes` individual byte
    reads -- the fact every `readsWithin` frame lemma needs to lift a byte-granular `agreeOn`
    hypothesis up to the width the instruction's `step` actually reads at. -/
theorem read_congr (w : MemWidth) (a : Address) (m1 m2 : X86_64Memory)
    (h : ∀ k : Nat, k < w.bytes → readByte m1 (a + k.toUInt64) = readByte m2 (a + k.toUInt64)) :
    read w a m1 = read w a m2 := by
  cases w with
  | w8 =>
    have h0 : readByte m1 a = readByte m2 a := by simpa using h 0 (by decide)
    simp [read, h0]
  | w16 =>
    have h0 : readByte m1 a = readByte m2 a := by simpa using h 0 (by decide)
    have h1 : readByte m1 (a+1) = readByte m2 (a+1) := by simpa using h 1 (by decide)
    simp [read, h0, h1]
  | w32 =>
    have h0 : readByte m1 a = readByte m2 a := by simpa using h 0 (by decide)
    have h1 : readByte m1 (a+1) = readByte m2 (a+1) := by simpa using h 1 (by decide)
    have h2 : readByte m1 (a+2) = readByte m2 (a+2) := by simpa using h 2 (by decide)
    have h3 : readByte m1 (a+3) = readByte m2 (a+3) := by simpa using h 3 (by decide)
    simp [read, h0, h1, h2, h3]
  | w64 =>
    have h0 : readByte m1 a = readByte m2 a := by simpa using h 0 (by decide)
    have h1 : readByte m1 (a+1) = readByte m2 (a+1) := by simpa using h 1 (by decide)
    have h2 : readByte m1 (a+2) = readByte m2 (a+2) := by simpa using h 2 (by decide)
    have h3 : readByte m1 (a+3) = readByte m2 (a+3) := by simpa using h 3 (by decide)
    have h4 : readByte m1 (a+4) = readByte m2 (a+4) := by simpa using h 4 (by decide)
    have h5 : readByte m1 (a+5) = readByte m2 (a+5) := by simpa using h 5 (by decide)
    have h6 : readByte m1 (a+6) = readByte m2 (a+6) := by simpa using h 6 (by decide)
    have h7 : readByte m1 (a+7) = readByte m2 (a+7) := by simpa using h 7 (by decide)
    simp [read, h0, h1, h2, h3, h4, h5, h6, h7]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `read_congr` restated with a `read .w8`-shaped hypothesis instead of `readByte` -- the exact
    shape `agreeOn` (Memory.lean) supplies, so `readsWithin` frame lemmas can apply it directly
    without a manual `readByte`/`read .w8` conversion at each call site. -/
theorem read_congr' (w : MemWidth) (a : Address) (m1 m2 : X86_64Memory)
    (h : ∀ k : Nat, k < w.bytes → read .w8 (a + k.toUInt64) m1 = read .w8 (a + k.toUInt64) m2) :
    read w a m1 = read w a m2 := by
  have h' : ∀ k : Nat, k < w.bytes → readByte m1 (a + k.toUInt64) = readByte m2 (a + k.toUInt64) := by
    intro k hk
    have hk2 := h k hk
    simp only [read] at hk2
    apply UInt8.toNat_inj.mp
    have := congrArg UInt64.toNat hk2
    simpa using this
  exact read_congr w a m1 m2 h'

end X86_64Mem

end Gasm.Targets.X86_64

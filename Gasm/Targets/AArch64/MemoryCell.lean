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

namespace Gasm.Targets.AArch64

open Gasm.Core

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Memory access width, in bytes, for AArch64 load and store operations. -/
inductive MemWidth where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Byte count corresponding to each memory access width. -/
def MemWidth.bytes : MemWidth → Nat
  | .w8  => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Bit count corresponding to each memory access width. -/
def MemWidth.bits : MemWidth → Nat
  | .w8  => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Bitmask for checking natural alignment for a given access width. -/
def MemWidth.alignmentMask : MemWidth → UInt64
  | .w8  => 0
  | .w16 => 1
  | .w32 => 3
  | .w64 => 7

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Checks if an address satisfies natural alignment for the specified width. -/
def isAligned (a : Address) (w : MemWidth) : Bool :=
  (a &&& w.alignmentMask) == 0

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Checks if a stack pointer satisfies the AAPCS64 mandatory 16-byte alignment invariant. -/
def isSpAligned (sp : Address) : Bool :=
  (sp &&& 0xF) == 0

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Declares whether a memory operation is a read (load) or write (store). -/
inductive MemAccessKind where
  | load | store
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Sealed AArch64 machine memory cell. The constructor `mk` and field `raw` are private to this
    module: outside this file, no term can synthesize an `AArch64Memory` from an arbitrary
    `Address → Byte` function, nor project one back out. All machine memory observations and
    mutations must route through `AArch64Mem.read` and `AArch64Mem.write`. -/
structure AArch64Memory where
  private mk ::
  private raw : Address → Byte

namespace AArch64Mem

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Reads a single raw byte from machine memory. -/
def readByte (m : AArch64Memory) (a : Address) : Byte := m.raw a

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Writes a single raw byte to machine memory, leaving all other addresses unchanged. -/
def writeByte (m : AArch64Memory) (a : Address) (v : Byte) : AArch64Memory :=
  ⟨fun addr => if addr == a then v else m.raw addr⟩

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Width-indexed little-endian memory read. Hand-unrolled per width to preserve definitional
    reduction ladders in step lemmas. -/
def read (w : MemWidth) (a : Address) (m : AArch64Memory) : UInt64 :=
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

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Width-indexed little-endian memory write. Hand-unrolled per width to ensure mechanical
    chokepoint enforcement and exact bit-level round-trips. -/
def write (w : MemWidth) (a : Address) (v : UInt64) (m : AArch64Memory) : AArch64Memory :=
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

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Bulk region initialization from an image layout function. -/
def initRegion (f : Address → Byte) : AArch64Memory := ⟨f⟩

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- The all-zero initialized memory image. -/
def zero : AArch64Memory := initRegion (fun _ => 0)

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Bulk sequential byte write, installing a list of bytes beginning at address `a`. -/
def writeBytes (a : Address) (bytes : List Byte) (m : AArch64Memory) : AArch64Memory :=
  let rec loop (offset : Nat) : List Byte → AArch64Memory → AArch64Memory
    | [], m' => m'
    | b :: rest, m' => loop (offset + 1) rest (writeByte m' (a + offset.toUInt64) b)
  loop 0 bytes m

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that reading back a single byte at the written address yields the written value. -/
@[simp] theorem readByte_writeByte_same (m : AArch64Memory) (a : Address) (v : Byte) :
    readByte (writeByte m a v) a = v := by
  simp [readByte, writeByte]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that writing a single byte at address `a` does not disturb reading at a distinct address `a'`. -/
@[simp] theorem readByte_writeByte_diff (m : AArch64Memory) (a a' : Address) (v : Byte) (h : a' ≠ a) :
    readByte (writeByte m a v) a' = readByte m a' := by
  simp [readByte, writeByte, h]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that writing a width-`w` value at address `a` does not disturb reading any byte outside `[a, a + w.bytes)`. -/
theorem readByte_write_disjoint (w : MemWidth) (a : Address) (v : UInt64) (m : AArch64Memory) (a' : Address)
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

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that reading a byte from an initialized region returns the image function value. -/
theorem readByte_initRegion (f : Address → Byte) (a : Address) :
    readByte (initRegion f) a = f a := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that reading any byte of zero-initialized memory returns 0. -/
theorem readByte_zero (a : Address) : readByte zero a = 0 := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that reading any width at any address from zero-initialized memory returns 0. -/
@[simp] theorem read_zero (w : MemWidth) (a : Address) : read w a zero = 0 := by
  cases w <;> simp [read, readByte_zero]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Width decomposition congruence: reading width `w` is entirely determined by its constituent bytes. -/
theorem read_congr (w : MemWidth) (a : Address) (m1 m2 : AArch64Memory)
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

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Restates `read_congr` with an 8-bit read hypothesis for direct use in footprint frame lemmas. -/
theorem read_congr' (w : MemWidth) (a : Address) (m1 m2 : AArch64Memory)
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

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Bit-level extraction lemma for byte 0 (un-shifted) in a 64-bit word. -/
theorem byte0_bit (v : BitVec 64) (i : Nat) (hi : i < 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 8 v)).getLsbD i = (decide (i < 8) && v.getLsbD i) := by
  simp [BitVec.getLsbD_setWidth, hi]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Bit-level extraction lemma for byte slice shifted right by `shift` and shifted left by `shift`. -/
theorem slice_getLsbD (v : BitVec 64) (shift : Nat) (i : Nat) (hi : i < 64) :
    ((BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> shift))) <<< shift).getLsbD i =
      (!decide (i < shift) && decide (i < shift + 8) && v.getLsbD i) := by
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi]
  by_cases h1 : i < shift
  · simp [h1]
  · simp [h1]
    have h_add : shift + (i - shift) = i := by omega
    have h_iff : i - shift < 8 ↔ i < shift + 8 := by omega
    rw [h_add, BitVec.getLsbD_eq_getElem hi]
    simp [h_iff]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that 64-bit little-endian write is read back identically by a 64-bit read at the same address. -/
theorem read64_write64_same (a : Address) (v : UInt64) (m : AArch64Memory) :
    read .w64 a (write .w64 a v m) = v := by
  have h01 : a ≠ a + 1 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h02 : a ≠ a + 2 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h03 : a ≠ a + 3 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h04 : a ≠ a + 4 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h05 : a ≠ a + 5 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h06 : a ≠ a + 6 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h07 : a ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h12 : a + 1 ≠ a + 2 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h13 : a + 1 ≠ a + 3 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h14 : a + 1 ≠ a + 4 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h15 : a + 1 ≠ a + 5 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h16 : a + 1 ≠ a + 6 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h17 : a + 1 ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h23 : a + 2 ≠ a + 3 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h24 : a + 2 ≠ a + 4 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h25 : a + 2 ≠ a + 5 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h26 : a + 2 ≠ a + 6 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h27 : a + 2 ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h34 : a + 3 ≠ a + 4 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h35 : a + 3 ≠ a + 5 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h36 : a + 3 ≠ a + 6 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h37 : a + 3 ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h45 : a + 4 ≠ a + 5 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h46 : a + 4 ≠ a + 6 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h47 : a + 4 ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h56 : a + 5 ≠ a + 6 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h57 : a + 5 ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h67 : a + 6 ≠ a + 7 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h50 := Ne.symm h05
  have h60 := Ne.symm h06
  have h70 := Ne.symm h07
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h51 := Ne.symm h15
  have h61 := Ne.symm h16
  have h71 := Ne.symm h17
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h52 := Ne.symm h25
  have h62 := Ne.symm h26
  have h72 := Ne.symm h27
  have h43 := Ne.symm h34
  have h53 := Ne.symm h35
  have h63 := Ne.symm h36
  have h73 := Ne.symm h37
  have h54 := Ne.symm h45
  have h64 := Ne.symm h46
  have h74 := Ne.symm h47
  have h65 := Ne.symm h56
  have h75 := Ne.symm h57
  have h76 := Ne.symm h67
  simp only [read, write, readByte, beq_self_eq_true, if_true]
  simp only [beq_iff_eq, h10, h20, h30, h40, h50, h60, h70,
             h21, h31, h41, h51, h61, h71,
             h32, h42, h52, h62, h72,
             h43, h53, h63, h73,
             h54, h64, h74,
             h65, h75,
             h76, if_false]
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h_b0 : (v.toUInt8.toUInt64).toBitVec =
      BitVec.setWidth 64 (BitVec.setWidth 8 v.toBitVec) := by
    rw [UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  have h_b1 : ((v >>> 8).toUInt8.toUInt64 <<< 8).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 8))) <<< 8 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b2 : ((v >>> 16).toUInt8.toUInt64 <<< 16).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 16))) <<< 16 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b3 : ((v >>> 24).toUInt8.toUInt64 <<< 24).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 24))) <<< 24 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b4 : ((v >>> 32).toUInt8.toUInt64 <<< 32).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 32))) <<< 32 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b5 : ((v >>> 40).toUInt8.toUInt64 <<< 40).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 40))) <<< 40 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b6 : ((v >>> 48).toUInt8.toUInt64 <<< 48).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 48))) <<< 48 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b7 : ((v >>> 56).toUInt8.toUInt64 <<< 56).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toBitVec >>> 56))) <<< 56 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  repeat rw [UInt64.toBitVec_or]
  repeat rw [BitVec.getLsbD_or]
  rw [h_b0, h_b1, h_b2, h_b3, h_b4, h_b5, h_b6, h_b7]
  rw [byte0_bit v.toBitVec i hi]
  rw [slice_getLsbD v.toBitVec 8 i hi]
  rw [slice_getLsbD v.toBitVec 16 i hi]
  rw [slice_getLsbD v.toBitVec 24 i hi]
  rw [slice_getLsbD v.toBitVec 32 i hi]
  rw [slice_getLsbD v.toBitVec 40 i hi]
  rw [slice_getLsbD v.toBitVec 48 i hi]
  rw [slice_getLsbD v.toBitVec 56 i hi]
  have hcases : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
                (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases hcases with c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7
  · have : decide (i < 8) = true := decide_eq_true c0
    have : decide (i < 16) = true := decide_eq_true (by omega)
    have : decide (i < 24) = true := decide_eq_true (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    have : decide (i < 40) = true := decide_eq_true (by omega)
    have : decide (i < 48) = true := decide_eq_true (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = true := decide_eq_true (by omega)
    have : decide (i < 24) = true := decide_eq_true (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    have : decide (i < 40) = true := decide_eq_true (by omega)
    have : decide (i < 48) = true := decide_eq_true (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = true := decide_eq_true (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    have : decide (i < 40) = true := decide_eq_true (by omega)
    have : decide (i < 48) = true := decide_eq_true (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    have : decide (i < 40) = true := decide_eq_true (by omega)
    have : decide (i < 48) = true := decide_eq_true (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = false := decide_eq_false (by omega)
    have : decide (i < 40) = true := decide_eq_true (by omega)
    have : decide (i < 48) = true := decide_eq_true (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = false := decide_eq_false (by omega)
    have : decide (i < 40) = false := decide_eq_false (by omega)
    have : decide (i < 48) = true := decide_eq_true (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = false := decide_eq_false (by omega)
    have : decide (i < 40) = false := decide_eq_false (by omega)
    have : decide (i < 48) = false := decide_eq_false (by omega)
    have : decide (i < 56) = true := decide_eq_true (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = false := decide_eq_false (by omega)
    have : decide (i < 40) = false := decide_eq_false (by omega)
    have : decide (i < 48) = false := decide_eq_false (by omega)
    have : decide (i < 56) = false := decide_eq_false (by omega)
    have : decide (i < 64) = true := decide_eq_true hi
    simp [*]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that 32-bit little-endian write is read back identically by a 32-bit read at the same address. -/
theorem read32_write32_same (a : Address) (v : UInt32) (m : AArch64Memory) :
    read .w32 a (write .w32 a v.toUInt64 m) = v.toUInt64 := by
  have h01 : a ≠ a + 1 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h02 : a ≠ a + 2 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h03 : a ≠ a + 3 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h12 : a + 1 ≠ a + 2 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h13 : a + 1 ≠ a + 3 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h23 : a + 2 ≠ a + 3 := by intro he; have := congrArg UInt64.toNat he; simp [UInt64.toNat_add] at this; omega
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h32 := Ne.symm h23
  simp only [read, write, readByte, beq_self_eq_true, if_true]
  simp only [beq_iff_eq, h10, h20, h30, h21, h31, h32, if_false]
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h_b0 : (v.toUInt64.toUInt8.toUInt64).toBitVec =
      BitVec.setWidth 64 (BitVec.setWidth 8 v.toUInt64.toBitVec) := by
    rw [UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  have h_b1 : ((v.toUInt64 >>> 8).toUInt8.toUInt64 <<< 8).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toUInt64.toBitVec >>> 8))) <<< 8 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b2 : ((v.toUInt64 >>> 16).toUInt8.toUInt64 <<< 16).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toUInt64.toBitVec >>> 16))) <<< 16 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  have h_b3 : ((v.toUInt64 >>> 24).toUInt8.toUInt64 <<< 24).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toUInt64.toBitVec >>> 24))) <<< 24 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  repeat rw [UInt64.toBitVec_or]
  repeat rw [BitVec.getLsbD_or]
  rw [h_b0, h_b1, h_b2, h_b3]
  rw [byte0_bit v.toUInt64.toBitVec i hi]
  rw [slice_getLsbD v.toUInt64.toBitVec 8 i hi]
  rw [slice_getLsbD v.toUInt64.toBitVec 16 i hi]
  rw [slice_getLsbD v.toUInt64.toBitVec 24 i hi]
  have hv : ∀ j, 32 ≤ j → v.toUInt64.toBitVec.getLsbD j = false := by
    intro j hj
    rw [UInt32.toBitVec_toUInt64]
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge v.toBitVec j hj]
  have hcases : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ 32 ≤ i := by omega
  rcases hcases with c0 | c1 | c2 | c3 | c4
  · have : decide (i < 8) = true := decide_eq_true c0
    have : decide (i < 16) = true := decide_eq_true (by omega)
    have : decide (i < 24) = true := decide_eq_true (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = true := decide_eq_true (by omega)
    have : decide (i < 24) = true := decide_eq_true (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = true := decide_eq_true (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = true := decide_eq_true (by omega)
    simp [*]
  · have : decide (i < 8) = false := decide_eq_false (by omega)
    have : decide (i < 16) = false := decide_eq_false (by omega)
    have : decide (i < 24) = false := decide_eq_false (by omega)
    have : decide (i < 32) = false := decide_eq_false (by omega)
    have hval := hv i c4
    rw [hval]
    simp [*]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that 16-bit little-endian write is read back identically by a 16-bit read at the same address. -/
theorem read16_write16_same (a : Address) (v : UInt16) (m : AArch64Memory) :
    read .w16 a (write .w16 a v.toUInt64 m) = v.toUInt64 := by
  have h01 : a ≠ a + 1 := by
    intro he
    have := congrArg UInt64.toNat he
    simp [UInt64.toNat_add] at this
    omega
  have h10 : a + 1 ≠ a := Ne.symm h01
  simp only [read, write, readByte, beq_self_eq_true, if_true]
  simp only [beq_iff_eq, h10, if_false]
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h_b0 : (v.toUInt64.toUInt8.toUInt64).toBitVec =
      BitVec.setWidth 64 (BitVec.setWidth 8 v.toUInt64.toBitVec) := by
    rw [UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  have h_b1 : ((v.toUInt64 >>> 8).toUInt8.toUInt64 <<< 8).toBitVec =
      (BitVec.setWidth 64 (BitVec.setWidth 8 (v.toUInt64.toBitVec >>> 8))) <<< 8 := by
    rw [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
        UInt64.toBitVec_shiftRight]
    rfl
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, h_b0, h_b1]
  rw [byte0_bit v.toUInt64.toBitVec i hi]
  rw [slice_getLsbD v.toUInt64.toBitVec 8 i hi]
  have hv : ∀ j, 16 ≤ j → v.toUInt64.toBitVec.getLsbD j = false := by
    intro j hj
    rw [UInt16.toBitVec_toUInt64]
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge v.toBitVec j hj]
  by_cases h0 : i < 8
  · simp [h0]
  · by_cases h1 : i < 16
    · simp [h0, h1]
    · have hge : 16 ≤ i := by omega
      have hval := hv i hge
      rw [hval]
      simp [h0, h1]

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that 8-bit write is read back identically by an 8-bit read at the same address. -/
theorem read8_write8_same (a : Address) (v : UInt8) (m : AArch64Memory) :
    read .w8 a (write .w8 a v.toUInt64 m) = v.toUInt64 := by
  simp [read, write, writeByte, readByte]

end AArch64Mem

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Default Inhabited instance providing clean all-zero machine memory. -/
instance : Inhabited AArch64Memory where
  default := AArch64Mem.zero

end Gasm.Targets.AArch64

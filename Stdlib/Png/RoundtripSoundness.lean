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
import Stdlib.Zlib.ContainerRoundtrip
import Stdlib.Png.Streaming
import Stdlib.Png.Equivalence

/-
## PA16 L10/L11: PNG chunk framing and the universal encode/decode roundtrip

Everything below the chunk layer is already universal: the filter layer
(`filter_unfilter_soundness`, `Stdlib/Png/Equivalence.lean`) and the ZLIB container
(`Stdlib.Zlib.zlib_roundtrip_soundness`). This file adds the RFC 2083 chunk-framing
bookkeeping — `mkChunk`/`parseChunk` inversion with CRC-32 verification, IHDR field
roundtrip, the chunk-scan pass over the writer's exact three-chunk layout, and the
scanline reconstruction loop — and assembles `png_roundtrip_soundness`.
-/

namespace Stdlib.Png

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- `get!` on the left of an append. -/
theorem ByteArray.get!_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  have h2 : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [_root_.ByteArray.get!_eq_getElem _ i h2, _root_.ByteArray.get!_eq_getElem _ i h,
    ByteArray.getElem_append_left h]

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- `get!` on the right of an append. -/
theorem ByteArray.get!_append_right (a b : ByteArray) (i : Nat) (h : a.size ≤ i)
    (h2 : i < a.size + b.size) :
    (a ++ b).get! i = b.get! (i - a.size) := by
  have h3 : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [_root_.ByteArray.get!_eq_getElem _ i h3,
    _root_.ByteArray.get!_eq_getElem _ (i - a.size) (by omega),
    ByteArray.getElem_append_right h]

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- The byte-copy loop is exactly an append. -/
theorem byteArray_forIn_push_eq (src acc : ByteArray) :
    (forIn (m := Id) src acc (fun x o => pure (ForInStep.yield (o.push x)))) = acc ++ src := by
  obtain ⟨hsz, hpre, hmid⟩ := Stdlib.Zlib.byteArray_forIn_push_spec src acc
  apply _root_.ByteArray.ext_get!
  · rw [hsz, ByteArray.size_append]
  · intro i hi
    rw [hsz] at hi
    rcases Nat.lt_or_ge i acc.size with h | h
    · rw [hpre i h, ByteArray.get!_append_left _ _ _ h]
    · have hj : i = acc.size + (i - acc.size) := by omega
      rw [hj, hmid (i - acc.size) (by omega),
        ByteArray.get!_append_right _ _ _ (by omega) (by omega)]
      congr 1
      omega

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- Nothing before an empty prefix. -/
theorem ByteArray.empty_append (b : ByteArray) : ByteArray.empty ++ b = b := by
  apply _root_.ByteArray.ext_get!
  · rw [ByteArray.size_append]
    show ByteArray.empty.size + b.size = b.size
    rw [show ByteArray.empty.size = 0 from rfl]
    omega
  · intro i hi
    rw [ByteArray.size_append] at hi
    rw [ByteArray.get!_append_right _ _ _ (by exact Nat.zero_le i)
      (by rw [show ByteArray.empty.size = 0 from rfl] at hi ⊢; omega)]
    rfl

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- The four big-endian bytes of a 32-bit value, as `Nat`s. -/
theorem uint32_byte_toNat (x : UInt32) :
    (((x >>> 24) &&& 0xFF).toUInt8).toNat = x.toNat / 2 ^ 24 % 2 ^ 8 ∧
    (((x >>> 16) &&& 0xFF).toUInt8).toNat = x.toNat / 2 ^ 16 % 2 ^ 8 ∧
    (((x >>> 8) &&& 0xFF).toUInt8).toNat = x.toNat / 2 ^ 8 % 2 ^ 8 ∧
    ((x &&& 0xFF).toUInt8).toNat = x.toNat % 2 ^ 8 := by
  have hFF : (0xFF : UInt32).toNat = 255 := rfl
  have h255 : (255 : Nat) = 2 ^ 8 - 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((24 : UInt32).toNat % 32) = 24 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  · rw [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((16 : UInt32).toNat % 32) = 16 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  · rw [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((8 : UInt32).toNat % 32) = 8 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  · rw [UInt32.toNat_toUInt8, UInt32.toNat_and,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- A power of two divides any multiple of a deeper power. -/
theorem pow_dvd_mul_pow (y a b : Nat) (hba : b ≤ a) : (2:Nat) ^ b ∣ y * 2 ^ a := by
  refine ⟨y * 2 ^ (a - b), ?_⟩
  rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ b) y, Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  omega

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- A big-endian `Nat`-level or-chain of four bytes is positional notation. -/
theorem nat_be_or (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256)
    (h3 : b3 < 256) :
    (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
      = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3 := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have ho1 : b0 * 2 ^ 24 ||| b1 * 2 ^ 16 = b0 * 2 ^ 24 + b1 * 2 ^ 16 := by
    apply Stdlib.Zlib.nat_or_add (k := 24)
    · exact Nat.mod_eq_zero_of_dvd (pow_dvd_mul_pow b0 24 24 (by omega))
    · have hp : (2:Nat) ^ 8 * 2 ^ 16 = 2 ^ 24 := by decide
      have := (Nat.mul_lt_mul_right (Nat.two_pow_pos 16)).mpr (show b1 < 2 ^ 8 from h1)
      omega
  rw [ho1]
  have ho2 : b0 * 2 ^ 24 + b1 * 2 ^ 16 ||| b2 * 2 ^ 8
      = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 := by
    apply Stdlib.Zlib.nat_or_add (k := 16)
    · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add
        (pow_dvd_mul_pow b0 24 16 (by omega)) (pow_dvd_mul_pow b1 16 16 (by omega)))
    · have hp : (2:Nat) ^ 8 * 2 ^ 8 = 2 ^ 16 := by decide
      have := (Nat.mul_lt_mul_right (Nat.two_pow_pos 8)).mpr (show b2 < 2 ^ 8 from h2)
      omega
  rw [ho2]
  apply Stdlib.Zlib.nat_or_add (k := 8)
  · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_add
      (pow_dvd_mul_pow b0 24 8 (by omega)) (pow_dvd_mul_pow b1 16 8 (by omega)))
      (pow_dvd_mul_pow b2 8 8 (by omega)))
  · exact h3

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-critical-chunks -/
/-- Reassembling the four written big-endian bytes of `n.toUInt32` recovers `n`, at the
    `Nat` level the chunk parser works at. -/
theorem nat_be_roundtrip (n : Nat) (hn : n < 2 ^ 32) :
    ((((n.toUInt32 >>> 24) &&& 0xFF).toUInt8).toNat <<< 24) |||
    ((((n.toUInt32 >>> 16) &&& 0xFF).toUInt8).toNat <<< 16) |||
    ((((n.toUInt32 >>> 8) &&& 0xFF).toUInt8).toNat <<< 8) |||
    (((n.toUInt32 &&& 0xFF).toUInt8).toNat) = n := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := uint32_byte_toNat n.toUInt32
  have htn : n.toUInt32.toNat = n := by
    rw [Nat.toUInt32, UInt32.toNat_ofNat']
    omega
  rw [hb0, hb1, hb2, hb3, htn,
    nat_be_or _ _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  have e24 : (2:Nat) ^ 24 = 16777216 := by decide
  have e16 : (2:Nat) ^ 16 = 65536 := by decide
  have e8 : (2:Nat) ^ 8 = 256 := by decide
  have e32 : (2:Nat) ^ 32 = 4294967296 := by decide
  rw [e24, e16, e8]
  rw [e32] at hn
  omega

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- `mkChunk` in explicit byte-assembly form. -/
theorem mkChunk_eq (t : String) (d : ByteArray) :
    mkChunk t d =
      (((((((ByteArray.empty.push ((d.size.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
        ((d.size.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
        ((d.size.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
        (d.size.toUInt32 &&& 0xFF).toUInt8 ++ t.toUTF8 ++ d).push
        ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 24) &&& 0xFF).toUInt8).push
        ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 16) &&& 0xFF).toUInt8).push
        ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 8) &&& 0xFF).toUInt8).push
        (Stdlib.Zlib.crc32 (t.toUTF8 ++ d) &&& 0xFF).toUInt8 := by
  have idb : ∀ {α β : Type} (x : Id α) (f : α → Id β), (x >>= f) = f x := fun _ _ => rfl
  conv => lhs; unfold mkChunk
  simp only [Id.run, idb]
  rw [byteArray_forIn_push_eq, byteArray_forIn_push_eq, byteArray_forIn_push_eq,
    byteArray_forIn_push_eq, ByteArray.empty_append]

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- `mkChunk`'s byte layout: 4-byte big-endian length, 4-byte type, payload, 4-byte
    big-endian CRC-32 over type-plus-payload. -/
theorem mkChunk_spec (t : String) (d : ByteArray) (ht4 : t.toUTF8.size = 4) :
    (mkChunk t d).size = d.size + 12 ∧
    ((mkChunk t d).get! 0 = ((d.size.toUInt32 >>> 24) &&& 0xFF).toUInt8 ∧
     (mkChunk t d).get! 1 = ((d.size.toUInt32 >>> 16) &&& 0xFF).toUInt8 ∧
     (mkChunk t d).get! 2 = ((d.size.toUInt32 >>> 8) &&& 0xFF).toUInt8 ∧
     (mkChunk t d).get! 3 = (d.size.toUInt32 &&& 0xFF).toUInt8) ∧
    (∀ j, j < 4 → (mkChunk t d).get! (4 + j) = t.toUTF8.get! j) ∧
    (∀ j, j < d.size → (mkChunk t d).get! (8 + j) = d.get! j) ∧
    ((mkChunk t d).get! (8 + d.size) =
      ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 24) &&& 0xFF).toUInt8 ∧
     (mkChunk t d).get! (9 + d.size) =
      ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 16) &&& 0xFF).toUInt8 ∧
     (mkChunk t d).get! (10 + d.size) =
      ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 8) &&& 0xFF).toUInt8 ∧
     (mkChunk t d).get! (11 + d.size) =
      (Stdlib.Zlib.crc32 (t.toUTF8 ++ d) &&& 0xFF).toUInt8) := by
  rw [mkChunk_eq]
  have hlen4 : ((((ByteArray.empty.push ((d.size.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
      ((d.size.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
      ((d.size.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
      (d.size.toUInt32 &&& 0xFF).toUInt8).size = 4 := rfl
  have hbody : ((((ByteArray.empty.push ((d.size.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
      ((d.size.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
      ((d.size.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
      (d.size.toUInt32 &&& 0xFF).toUInt8 ++ t.toUTF8 ++ d).size = 8 + d.size := by
    rw [ByteArray.size_append, ByteArray.size_append, hlen4, ht4]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [ByteArray.size_push]
    have hb := hbody
    omega
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by rw [hbody]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [ByteArray.size_append, hlen4, ht4]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [hlen4]; omega)]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by rw [hbody]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [ByteArray.size_append, hlen4, ht4]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [hlen4]; omega)]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by rw [hbody]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [ByteArray.size_append, hlen4, ht4]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [hlen4]; omega)]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by rw [hbody]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [ByteArray.size_append, hlen4, ht4]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [hlen4]; omega)]
    rfl
  · intro j hj
    rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by rw [hbody]; omega),
      ByteArray.get!_append_left _ _ _ (by rw [ByteArray.size_append, hlen4, ht4]; omega),
      ByteArray.get!_append_right _ _ _ (by rw [hlen4]; omega)
        (by rw [hlen4, ht4]; omega)]
    congr 1
    rw [hlen4]
    omega
  · intro j hj
    rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by rw [hbody]; omega),
      ByteArray.get!_append_right _ _ _
        (by rw [ByteArray.size_append, hlen4, ht4]; omega)
        (by rw [ByteArray.size_append, hlen4, ht4]; omega)]
    congr 1
    rw [ByteArray.size_append, hlen4, ht4]
    omega
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_eq _ _ _ (by rw [hbody])]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega)]
  · rw [ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; rw [hbody]; omega)]

end Stdlib.Png

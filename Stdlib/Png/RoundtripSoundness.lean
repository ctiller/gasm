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

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- The `Except`-monad byte-copy loop mirrors the pure one. -/
theorem byteArray_forIn_loop_except {ε : Type} (src : ByteArray)
    : ∀ (i : Nat) (h : i ≤ src.size) (acc : ByteArray),
    ByteArray.forIn.loop (m := Except ε) src
        (fun x o => Except.ok (ForInStep.yield (o.push x))) i h acc =
      .ok (ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) i h acc) := by
  intro i
  induction i with
  | zero =>
    intro h acc
    rw [ByteArray.forIn.loop.eq_def, ByteArray.forIn.loop.eq_def]
    rfl
  | succ i ih =>
    intro h acc
    have hstepE : ByteArray.forIn.loop (m := Except ε) src
        (fun x o => Except.ok (ForInStep.yield (o.push x))) (i + 1) h acc =
      ByteArray.forIn.loop (m := Except ε) src
        (fun x o => Except.ok (ForInStep.yield (o.push x))) i (by omega)
        (acc.push src[src.size - 1 - i]) := by
      rw [ByteArray.forIn.loop.eq_def]
      rfl
    have hstepI : ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) (i + 1) h acc =
      ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) i (by omega)
        (acc.push src[src.size - 1 - i]) := by
      rw [ByteArray.forIn.loop.eq_def]
      rfl
    rw [hstepE, hstepI]
    exact ih (by omega) (acc.push src[src.size - 1 - i])

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- The `Except`-monad byte-copy loop is an append. -/
theorem byteArray_forIn_push_except {ε : Type} (src acc : ByteArray) :
    (forIn (m := Except ε) src acc (fun x o => Except.ok (ForInStep.yield (o.push x))))
      = .ok (acc ++ src) := by
  show ByteArray.forIn.loop (m := Except ε) src _ src.size _ acc = _
  rw [byteArray_forIn_loop_except src src.size (Nat.le_refl _) acc]
  congr 1
  exact byteArray_forIn_push_eq src acc

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- A four-literal `ByteArray` built from a 4-byte string's code units is that string's
    UTF-8 image. -/
theorem mk4_eq_toUTF8 (t : String) (ht4 : t.toUTF8.size = 4) :
    ByteArray.mk #[t.toUTF8.get! 0, t.toUTF8.get! 1, t.toUTF8.get! 2, t.toUTF8.get! 3]
      = t.toUTF8 := by
  apply _root_.ByteArray.ext_get!
  · rw [ht4]
    rfl
  · intro i hi
    have hi4 : i < 4 := by
      have h4 : (ByteArray.mk #[t.toUTF8.get! 0, t.toUTF8.get! 1, t.toUTF8.get! 2,
        t.toUTF8.get! 3]).size = 4 := rfl
      omega
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 from by omega) with h | h | h | h <;>
      subst h <;> rfl

open Stdlib.Zlib in
set_option maxHeartbeats 1000000 in
/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- **Chunk inversion**: parsing at the position of an embedded `mkChunk` image recovers
    exactly the chunk's type and payload, with the CRC verified, advancing past it. -/
theorem parseChunk_inv (bytes : ByteArray) (pos : Nat) (t : String) (d : ByteArray)
    (ht4 : t.toUTF8.size = 4)
    (htp : String.fromUTF8? t.toUTF8 = some t)
    (hd32 : d.size < 2 ^ 32)
    (hsz : pos + (d.size + 12) ≤ bytes.size)
    (hbytes : ∀ j, j < d.size + 12 → bytes.get! (pos + j) = (mkChunk t d).get! j) :
    parseChunk bytes pos = .ok (PngChunk.mk t d (Stdlib.Zlib.crc32 (t.toUTF8 ++ d)),
      pos + (d.size + 12)) := by
  obtain ⟨hcsz, ⟨hl0, hl1, hl2, hl3⟩, htyp, hdata, ⟨hc0, hc1, hc2, hc3⟩⟩ := mkChunk_spec t d ht4
  -- the four length bytes
  have hB0 : bytes.get! pos = ((d.size.toUInt32 >>> 24) &&& 0xFF).toUInt8 := by
    have h := hbytes 0 (by omega)
    rw [hl0] at h
    exact h
  have hB1 : bytes.get! (pos + 1) = ((d.size.toUInt32 >>> 16) &&& 0xFF).toUInt8 := by
    have h := hbytes 1 (by omega)
    rw [hl1] at h
    exact h
  have hB2 : bytes.get! (pos + 2) = ((d.size.toUInt32 >>> 8) &&& 0xFF).toUInt8 := by
    have h := hbytes 2 (by omega)
    rw [hl2] at h
    exact h
  have hB3 : bytes.get! (pos + 3) = (d.size.toUInt32 &&& 0xFF).toUInt8 := by
    have h := hbytes 3 (by omega)
    rw [hl3] at h
    exact h
  -- the four type bytes
  have hT0 : bytes.get! (pos + 4) = t.toUTF8.get! 0 := by
    have h := hbytes 4 (by omega)
    rw [show (mkChunk t d).get! 4 = (mkChunk t d).get! (4 + 0) from rfl,
      htyp 0 (by omega)] at h
    exact h
  have hT1 : bytes.get! (pos + 5) = t.toUTF8.get! 1 := by
    have h := hbytes 5 (by omega)
    rw [show (mkChunk t d).get! 5 = (mkChunk t d).get! (4 + 1) from rfl,
      htyp 1 (by omega)] at h
    exact h
  have hT2 : bytes.get! (pos + 6) = t.toUTF8.get! 2 := by
    have h := hbytes 6 (by omega)
    rw [show (mkChunk t d).get! 6 = (mkChunk t d).get! (4 + 2) from rfl,
      htyp 2 (by omega)] at h
    exact h
  have hT3 : bytes.get! (pos + 7) = t.toUTF8.get! 3 := by
    have h := hbytes 7 (by omega)
    rw [show (mkChunk t d).get! 7 = (mkChunk t d).get! (4 + 3) from rfl,
      htyp 3 (by omega)] at h
    exact h
  -- the four CRC bytes
  have hC0 : bytes.get! (pos + 8 + d.size) =
      ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 24) &&& 0xFF).toUInt8 := by
    rw [show pos + 8 + d.size = pos + (8 + d.size) from by omega,
      hbytes (8 + d.size) (by omega), hc0]
  have hC1 : bytes.get! (pos + 8 + d.size + 1) =
      ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 16) &&& 0xFF).toUInt8 := by
    rw [show pos + 8 + d.size + 1 = pos + (9 + d.size) from by omega,
      hbytes (9 + d.size) (by omega), hc1]
  have hC2 : bytes.get! (pos + 8 + d.size + 2) =
      ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 8) &&& 0xFF).toUInt8 := by
    rw [show pos + 8 + d.size + 2 = pos + (10 + d.size) from by omega,
      hbytes (10 + d.size) (by omega), hc2]
  have hC3 : bytes.get! (pos + 8 + d.size + 3) =
      (Stdlib.Zlib.crc32 (t.toUTF8 ++ d) &&& 0xFF).toUInt8 := by
    rw [show pos + 8 + d.size + 3 = pos + (11 + d.size) from by omega,
      hbytes (11 + d.size) (by omega), hc3]
  -- the data slice
  have hextract : bytes.extract (pos + 8) (pos + 8 + d.size) = d := by
    have hesz : (bytes.extract (pos + 8) (pos + 8 + d.size)).size = d.size := by
      rw [ByteArray.size_extract]
      omega
    apply _root_.ByteArray.ext_get!
    · exact hesz
    · intro i hi
      rw [hesz] at hi
      rw [_root_.ByteArray.get!_eq_getElem _ i (by rw [hesz]; exact hi),
        ByteArray.getElem_extract,
        ← _root_.ByteArray.get!_eq_getElem _ _ (by omega),
        show pos + 8 + i = pos + (8 + i) from by omega,
        hbytes (8 + i) (by omega), hdata i hi]
  -- choreograph the parse
  unfold parseChunk
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (show ¬ pos + 12 > bytes.size from by omega)]
  rw [hT0, hT1, hT2, hT3, mk4_eq_toUTF8 t ht4, htp]
  split
  case h_2 hs =>
    exact absurd hs (by simp)
  case h_1 s hs =>
    have hts : s = t := by
      have h := hs
      simp at h
      exact h.symm
    rw [hts]
    rw [hB0, hB1, hB2, hB3]
    rw [show ((((d.size.toUInt32 >>> 24) &&& 0xFF).toUInt8).toNat <<< 24 |||
        (((d.size.toUInt32 >>> 16) &&& 0xFF).toUInt8).toNat <<< 16 |||
        (((d.size.toUInt32 >>> 8) &&& 0xFF).toUInt8).toNat <<< 8 |||
        ((d.size.toUInt32 &&& 0xFF).toUInt8).toNat) = d.size from
      nat_be_roundtrip d.size hd32]
    rw [if_neg (show ¬ pos + 8 + d.size + 4 > bytes.size from by omega)]
    rw [hextract]
    rw [byteArray_forIn_push_except t.toUTF8 ByteArray.empty]
    split
    case h_1 err heq =>
      exact absurd heq (by simp)
    case h_2 v heq =>
    have hv : v = ByteArray.empty ++ t.toUTF8 := by
      simp at heq
      exact heq.symm
    rw [hv, ByteArray.empty_append, byteArray_forIn_push_except d t.toUTF8]
    split
    case h_1 err2 heq2 =>
      exact absurd heq2 (by simp)
    case h_2 v2 heq2 =>
    have hv2 : v2 = t.toUTF8 ++ d := by
      simp at heq2
      exact heq2.symm
    rw [hv2]
    rw [hC0, hC1, hC2, hC3]
    rw [show ((((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 24) &&& 0xFF).toUInt8.toUInt32 <<< 24) |||
        (((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 16) &&& 0xFF).toUInt8.toUInt32 <<< 16) |||
        (((Stdlib.Zlib.crc32 (t.toUTF8 ++ d) >>> 8) &&& 0xFF).toUInt8.toUInt32 <<< 8) |||
        ((Stdlib.Zlib.crc32 (t.toUTF8 ++ d)) &&& 0xFF).toUInt8.toUInt32)
        = Stdlib.Zlib.crc32 (t.toUTF8 ++ d) from
      Stdlib.Zlib.uint32_be_reassemble (Stdlib.Zlib.crc32 (t.toUTF8 ++ d))]
    rw [bne_self_eq_false]
    rw [if_neg (by simp)]
    show (Except.ok (PngChunk.mk t d (Stdlib.Zlib.crc32 (t.toUTF8 ++ d)),
        pos + 8 + d.size + 4) : Except PngError (PngChunk × Nat)) = _
    rw [show pos + 8 + d.size + 4 = pos + (d.size + 12) from by omega]

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- The 13-byte IHDR payload `endPng` assembles. -/
def ihdrPayload (h : PngHeader) : ByteArray :=
  ((((((((((((ByteArray.empty.push ((h.width.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
    ((h.width.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
    ((h.width.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
    (h.width.toUInt32 &&& 0xFF).toUInt8).push
    ((h.height.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
    ((h.height.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
    ((h.height.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
    (h.height.toUInt32 &&& 0xFF).toUInt8).push
    h.bitDepth.toUInt8).push
    h.colorType.toNat.toUInt8).push
    h.compressionMethod.toUInt8).push
    h.filterMethod.toUInt8).push
    h.interlaceMethod.toUInt8

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- `endPng`'s output is the signature and the three chunks, in order. -/
theorem endPng_eq (w : PngWriter) (hrow : w.currentRow = w.header.height) :
    endPng w = .ok (((pngSignature ++ mkChunk "IHDR" (ihdrPayload w.header)) ++
      mkChunk "IDAT" (Stdlib.Zlib.zlibCompress w.rawStream)) ++
      mkChunk "IEND" ByteArray.empty) := by
  unfold endPng
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [hrow, bne_self_eq_false, if_neg (by simp)]
  rw [byteArray_forIn_push_except pngSignature ByteArray.empty]
  split
  case h_1 err heq =>
    exact absurd heq (by simp)
  case h_2 v heq =>
  have hv : v = ByteArray.empty ++ pngSignature := by
    simp at heq
    exact heq.symm
  rw [hv, ByteArray.empty_append]
  rw [show mkChunk "IHDR"
      (((((((((((((ByteArray.empty.push ((w.header.width.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
        ((w.header.width.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
        ((w.header.width.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
        (w.header.width.toUInt32 &&& 0xFF).toUInt8).push
        ((w.header.height.toUInt32 >>> 24) &&& 0xFF).toUInt8).push
        ((w.header.height.toUInt32 >>> 16) &&& 0xFF).toUInt8).push
        ((w.header.height.toUInt32 >>> 8) &&& 0xFF).toUInt8).push
        (w.header.height.toUInt32 &&& 0xFF).toUInt8).push
        w.header.bitDepth.toUInt8).push
        w.header.colorType.toNat.toUInt8).push
        w.header.compressionMethod.toUInt8).push
        w.header.filterMethod.toUInt8).push
        w.header.interlaceMethod.toUInt8)
      = mkChunk "IHDR" (ihdrPayload w.header) from rfl]
  rw [byteArray_forIn_push_except (mkChunk "IHDR" (ihdrPayload w.header)) pngSignature]
  split
  case h_1 err heq =>
    exact absurd heq (by simp)
  case h_2 v2 heq2 =>
  have hv2 : v2 = pngSignature ++ mkChunk "IHDR" (ihdrPayload w.header) := by
    simp at heq2
    exact heq2.symm
  rw [hv2]
  rw [byteArray_forIn_push_except (mkChunk "IDAT" (Stdlib.Zlib.zlibCompress w.rawStream))
    (pngSignature ++ mkChunk "IHDR" (ihdrPayload w.header))]
  split
  case h_1 err heq =>
    exact absurd heq (by simp)
  case h_2 v3 heq3 =>
  have hv3 : v3 = (pngSignature ++ mkChunk "IHDR" (ihdrPayload w.header)) ++
      mkChunk "IDAT" (Stdlib.Zlib.zlibCompress w.rawStream) := by
    simp at heq3
    exact heq3.symm
  rw [hv3]
  rw [byteArray_forIn_push_except (mkChunk "IEND" ByteArray.empty)
    ((pngSignature ++ mkChunk "IHDR" (ihdrPayload w.header)) ++
      mkChunk "IDAT" (Stdlib.Zlib.zlibCompress w.rawStream))]

/- REF: docs/STDLIB_PNG.md#31-png-signature-critical-chunks -/
/-- **IHDR inversion**: parsing the payload `endPng` writes for a standard RGBA8 header
    recovers the header exactly. -/
theorem parseIhdr_ihdrPayload (h : PngHeader)
    (hbd : h.bitDepth = 8) (hct : h.colorType = .truecolorRgba)
    (hcm : h.compressionMethod = 0) (hfm : h.filterMethod = 0) (him : h.interlaceMethod = 0)
    (hw : 0 < h.width) (hh : 0 < h.height)
    (hw32 : h.width < 2 ^ 32) (hh32 : h.height < 2 ^ 32) :
    parseIhdr (ihdrPayload h) = .ok h := by
  obtain ⟨wd, htt, bd, ct, cm, fm, im⟩ := h
  dsimp only at hbd hct hcm hfm him hw hh hw32 hh32
  subst hbd hct hcm hfm him
  have hP : ihdrPayload ⟨wd, htt, 8, .truecolorRgba, 0, 0, 0⟩ =
      ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
        ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
        ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
        (wd.toUInt32 &&& 0xFF).toUInt8,
        ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
        ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
        ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
        (htt.toUInt32 &&& 0xFF).toUInt8,
        8, 6, 0, 0, 0] := rfl
  unfold parseIhdr
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [hP]
  have hsz : (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).size = 13 := rfl
  rw [if_neg (show ¬ (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).size < 13 from by rw [hsz]; omega)]
  rw [show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 0 = ((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 1 = ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 2 = ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 3 = (wd.toUInt32 &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 4 = ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 5 = ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 6 = ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8 from rfl,
    show (ByteArray.mk #[((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (wd.toUInt32 &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8,
      ((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      (htt.toUInt32 &&& 0xFF).toUInt8,
      8, 6, 0, 0, 0]).get! 7 = (htt.toUInt32 &&& 0xFF).toUInt8 from rfl]
  rw [show ((((wd.toUInt32 >>> 24) &&& 0xFF).toUInt8).toNat <<< 24 |||
      (((wd.toUInt32 >>> 16) &&& 0xFF).toUInt8).toNat <<< 16 |||
      (((wd.toUInt32 >>> 8) &&& 0xFF).toUInt8).toNat <<< 8 |||
      ((wd.toUInt32 &&& 0xFF).toUInt8).toNat) = wd from nat_be_roundtrip wd hw32]
  rw [show ((((htt.toUInt32 >>> 24) &&& 0xFF).toUInt8).toNat <<< 24 |||
      (((htt.toUInt32 >>> 16) &&& 0xFF).toUInt8).toNat <<< 16 |||
      (((htt.toUInt32 >>> 8) &&& 0xFF).toUInt8).toNat <<< 8 |||
      ((htt.toUInt32 &&& 0xFF).toUInt8).toNat) = htt from nat_be_roundtrip htt hh32]
  rw [if_neg (show ¬ (wd == 0 || htt == 0) = true from by simp; omega)]
  rfl

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- ByteArray append is associative. -/
theorem byteArray_append_assoc (a b c : ByteArray) : a ++ b ++ c = a ++ (b ++ c) := by
  refine _root_.ByteArray.ext_get! (by simp only [ByteArray.size_append]; omega) ?_
  intro i hi
  have hi' : i < a.size + b.size + c.size := by
    simp only [ByteArray.size_append] at hi; omega
  rcases Nat.lt_or_ge i a.size with h1 | h1
  · rw [ByteArray.get!_append_left (a ++ b) c i (by rw [ByteArray.size_append]; omega),
      ByteArray.get!_append_left a b i h1,
      ByteArray.get!_append_left a (b ++ c) i h1]
  · rcases Nat.lt_or_ge i (a.size + b.size) with h2 | h2
    · rw [ByteArray.get!_append_left (a ++ b) c i (by rw [ByteArray.size_append]; omega),
        ByteArray.get!_append_right a b i h1 (by omega),
        ByteArray.get!_append_right a (b ++ c) i h1
          (by rw [ByteArray.size_append]; omega),
        ByteArray.get!_append_left b c (i - a.size) (by omega)]
    · rw [ByteArray.get!_append_right (a ++ b) c i
          (by rw [ByteArray.size_append]; omega)
          (by rw [ByteArray.size_append]; omega),
        ByteArray.get!_append_right a (b ++ c) i h1
          (by rw [ByteArray.size_append]; omega),
        ByteArray.get!_append_right b c (i - a.size) (by omega)
          (by omega),
        ByteArray.size_append,
        show i - (a.size + b.size) = i - a.size - b.size from by omega]

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- `push` is append of a singleton. -/
theorem byteArray_push_eq_append (a : ByteArray) (x : UInt8) :
    a.push x = a ++ ByteArray.empty.push x := by
  refine _root_.ByteArray.ext_get!
    (by simp only [ByteArray.size_push, ByteArray.size_append, ByteArray.size_empty] <;> omega) ?_
  intro i hi
  have hi' : i < a.size + 1 := by simp only [ByteArray.size_push] at hi; omega
  rcases Nat.lt_or_ge i a.size with h1 | h1
  · rw [_root_.ByteArray.get!_push_lt a x i h1, ByteArray.get!_append_left a _ i h1]
  · have hieq : i = a.size := by omega
    subst hieq
    rw [_root_.ByteArray.get!_push_eq a x a.size rfl,
      ByteArray.get!_append_right a _ a.size (Nat.le_refl _)
        (by simp only [ByteArray.size_push, ByteArray.size_empty] <;> omega),
      Nat.sub_self]
    exact (_root_.ByteArray.get!_push_eq ByteArray.empty x 0 rfl).symm

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- Filtering preserves the scanline length. -/
theorem filterScanline_size (ft : FilterType) (raw prior : ByteArray) (bpp : Nat) :
    (filterScanline ft raw prior bpp).size = raw.size := by
  rw [filterScanline_eq_fold, filterFold_size]

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- The RGBA8 header `encodeImageRGBA8` builds for an image. -/
def rgbaHeader (img : ImageRGBA8) : PngHeader :=
  { width := img.width, height := img.height, bitDepth := 8,
    colorType := PngColorType.truecolorRgba }

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- Row `y` of the image's pixel buffer (RGBA8, stride `width * 4`). -/
def rowSliceOf (img : ImageRGBA8) (y : Nat) : ByteArray :=
  img.pixels.extract (y * (img.width * 4)) ((y + 1) * (img.width * 4))

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- The writer's `prevRow` after `y` scanlines have been written. -/
def prevRowOf (img : ImageRGBA8) : Nat → ByteArray
  | 0 => ByteArray.empty
  | y + 1 => rowSliceOf img y

/- REF: docs/STDLIB_PNG.md#41-the-five-standard-filter-types -/
/-- The filter `encodeImageRGBA8` selects for row `y` (explicit or adaptive). -/
def chosenFtOf (img : ImageRGBA8) (ftOpt : Option FilterType) (y : Nat) : FilterType :=
  match ftOpt with
  | some f => f
  | none => chooseBestFilter (rowSliceOf img y) (prevRowOf img y) 4

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- The filter-byte-prefixed filtered bytes `writeScanline` appends for row `y`. -/
def encRowOf (img : ImageRGBA8) (ftOpt : Option FilterType) (y : Nat) : ByteArray :=
  ByteArray.empty.push (chosenFtOf img ftOpt y).toNat.toUInt8 ++
    filterScanline (chosenFtOf img ftOpt y) (rowSliceOf img y) (prevRowOf img y) 4

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- The writer's raw (pre-compression) stream after `n` scanlines. -/
def rawStreamOf (img : ImageRGBA8) (ftOpt : Option FilterType) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 => rawStreamOf img ftOpt n ++ encRowOf img ftOpt n

/- REF: docs/STDLIB_PNG.md#22-pngwriter-push-state-machine -/
/-- `writeScanline` on an unfinished writer with rows remaining: appends the filter byte
    and the filtered scanline to the raw stream. -/
theorem writeScanline_ok (w : PngWriter) (row : ByteArray) (ft : FilterType)
    (hfin : w.isFinished = false) (hrow : w.currentRow < w.header.height) :
    writeScanline w row ft = .ok ⟨w.header, w.currentRow + 1, row,
      w.rawStream.push ft.toNat.toUInt8 ++
        filterScanline ft row w.prevRow (bytesPerPixel w.header), w.isFinished⟩ := by
  unfold writeScanline
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [hfin]
  rw [if_neg (show ¬ (false = true) from by simp)]
  rw [if_neg (show ¬ (w.currentRow ≥ w.header.height) from by omega)]
  rw [byteArray_forIn_push_except (filterScanline ft row w.prevRow (bytesPerPixel w.header))
    (w.rawStream.push ft.toNat.toUInt8)]

/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- The writer state after `encodeImageRGBA8`'s scanline fold over the first `n` rows. -/
theorem encode_fold (img : ImageRGBA8) (ftOpt : Option FilterType) :
    ∀ n, n ≤ img.height →
    List.foldl (fun (__s : PngWriter) (y : Nat) =>
        match writeScanline __s
            (img.pixels.extract (y * (img.width * 4)) ((y + 1) * (img.width * 4)))
            (match ftOpt with
             | some filter => filter
             | none => chooseBestFilter
                 (img.pixels.extract (y * (img.width * 4)) ((y + 1) * (img.width * 4)))
                 __s.prevRow 4) with
        | Except.ok nextWriter => nextWriter
        | Except.error _ => __s)
      (beginPng ⟨img.width, img.height, 8, PngColorType.truecolorRgba, 0, 0, 0⟩)
      (List.range' 0 n) =
    ⟨rgbaHeader img, n, prevRowOf img n, rawStreamOf img ftOpt n, false⟩ := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hle
    rw [List.range'_1_concat, List.foldl_append, ih (by omega)]
    simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil]
    clear ih
    rw [show img.pixels.extract (n * (img.width * 4)) ((n + 1) * (img.width * 4)) =
      rowSliceOf img n from rfl]
    have hft : (match ftOpt with
        | some filter => filter
        | none => chooseBestFilter (rowSliceOf img n) (prevRowOf img n) 4) =
        chosenFtOf img ftOpt n := by
      cases ftOpt <;> rfl
    rw [hft]
    have hrow' : (⟨rgbaHeader img, n, prevRowOf img n, rawStreamOf img ftOpt n, false⟩ :
        PngWriter).currentRow <
        (⟨rgbaHeader img, n, prevRowOf img n, rawStreamOf img ftOpt n, false⟩ :
        PngWriter).header.height := by
      show n < img.height
      omega
    rw [writeScanline_ok _ _ _ rfl hrow']
    dsimp only
    rw [show bytesPerPixel (rgbaHeader img) = 4 from by
      simp [bytesPerPixel, rgbaHeader, PngColorType.channels]]
    rw [byteArray_push_eq_append, byteArray_append_assoc]
    rfl

open Stdlib.Zlib in
/- REF: docs/STDLIB_PNG.md#23-monadic-pipeline-composition -/
/-- **Encoder characterization**: `encodeImageRGBA8` emits exactly the PNG signature
    followed by the IHDR, IDAT (zlib-compressed filtered raw stream), and IEND chunks. -/
theorem encodeImageRGBA8_eq (img : ImageRGBA8) (ftOpt : Option FilterType) :
    encodeImageRGBA8 img ftOpt =
      ((pngSignature ++ mkChunk "IHDR" (ihdrPayload (rgbaHeader img))) ++
        mkChunk "IDAT" (Stdlib.Zlib.zlibCompress (rawStreamOf img ftOpt img.height))) ++
        mkChunk "IEND" ByteArray.empty := by
  have idb : ∀ {α β : Type} (x : Id α) (f : α → Id β), (x >>= f) = f x := fun _ _ => rfl
  unfold encodeImageRGBA8
  simp only [Id.run, idb, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [Stdlib.Zlib.forIn_yield_eq_foldl _
    (fun (__s : PngWriter) (y : Nat) =>
      match writeScanline __s
          (img.pixels.extract (y * (img.width * 4)) ((y + 1) * (img.width * 4)))
          (match ftOpt with
           | some filter => filter
           | none => chooseBestFilter
               (img.pixels.extract (y * (img.width * 4)) ((y + 1) * (img.width * 4)))
               __s.prevRow 4) with
      | Except.ok nextWriter => nextWriter
      | Except.error _ => __s)
    (by
      intro a s
      cases writeScanline s
        (img.pixels.extract (a * (img.width * 4)) ((a + 1) * (img.width * 4)))
        (match ftOpt with
         | some filter => filter
         | none => chooseBestFilter
             (img.pixels.extract (a * (img.width * 4)) ((a + 1) * (img.width * 4)))
             s.prevRow 4) <;> rfl)]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [encode_fold img ftOpt img.height (Nat.le_refl _)]
  rw [endPng_eq _ rfl]
  rfl

end Stdlib.Png

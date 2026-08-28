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
import Stdlib.Zlib.RoundtripCorollaries
import Stdlib.Zlib.FixedBlockBridge

/-
## PA16 L8/L9: the RFC 1950/1952 container roundtrips, universal over the input

The containers wrap the now-proven DEFLATE payloads (`compress` for ZLIB,
`compressFixed` — via the Law 12 connection theorem — for GZIP) in fixed headers and
checksum/length trailers. This file proves, byte-bookkeeping only:

- `zlib_roundtrip_soundness : ∀ data, zlibDecompress (zlibCompress data) = .ok data`
- `gzip_roundtrip_soundness : ∀ data, gzipDecompress (gzipCompress data) = .ok data`
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- The byte-copy loop `for b in src do out := out.push b`, characterized pointwise:
    the accumulator keeps its prefix and gains exactly `src`'s bytes. -/
theorem byteArray_copy_loop (src : ByteArray) : ∀ (i : Nat) (h : i ≤ src.size) (acc : ByteArray),
    (ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) i h acc).size = acc.size + i ∧
    (∀ j, j < acc.size →
      (ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) i h acc).get! j = acc.get! j) ∧
    (∀ j, j < i →
      (ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) i h acc).get! (acc.size + j)
        = src.get! (src.size - i + j)) := by
  intro i
  induction i with
  | zero =>
    intro h acc
    rw [ByteArray.forIn.loop.eq_def]
    exact ⟨rfl, fun j _ => rfl, fun j hj => absurd hj (by omega)⟩
  | succ i ih =>
    intro h acc
    have hstep : ByteArray.forIn.loop (m := Id) src
        (fun x o => pure (ForInStep.yield (o.push x))) (i + 1) h acc =
      ByteArray.forIn.loop (m := Id) src (fun x o => pure (ForInStep.yield (o.push x))) i
        (by omega) (acc.push src[src.size - 1 - i]) := by
      rw [ByteArray.forIn.loop.eq_def]
      rfl
    rw [hstep]
    have hrec := ih (by omega) (acc.push src[src.size - 1 - i])
    have hpsize : (acc.push src[src.size - 1 - i]).size = acc.size + 1 :=
      ByteArray.size_push ..
    rw [hpsize] at hrec
    have hbyte : src[src.size - 1 - i] = src.get! (src.size - (i + 1)) := by
      rw [ByteArray.get!_eq_getElem src (src.size - (i + 1)) (by omega)]
      congr 1
      omega
    refine ⟨by rw [hrec.1]; omega, ?_, ?_⟩
    · intro j hj
      rw [hrec.2.1 j (by omega), ByteArray.get!_push_lt _ _ _ hj]
    · intro j hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        rw [Nat.add_zero, hrec.2.1 (acc.size) (by omega),
          ByteArray.get!_push_eq _ _ _ rfl, hbyte]
        simp
      · have he : acc.size + j = (acc.size + 1) + (j - 1) := by omega
        rw [he, hrec.2.2 (j - 1) (by omega)]
        congr 1
        omega

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- Bitwise-or is addition when the left side is clear below the right side's width. -/
theorem nat_or_add {a b k : Nat} (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) : a ||| b = a + b := by
  have hd : (a / 2 ^ k) * 2 ^ k = a := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ha)
  rw [← hd, Nat.or_comm, ← Nat.shiftLeft_eq, lor_shiftLeft_eq_add hb]
  omega

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- Big-endian byte split/reassembly for a 32-bit word: the four emitted bytes rebuild
    the word exactly, in the decoder's `(b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3`
    shape. -/
theorem uint32_be_reassemble (x : UInt32) :
    (((x >>> 24) &&& 0xFF).toUInt8.toUInt32 <<< 24) |||
    (((x >>> 16) &&& 0xFF).toUInt8.toUInt32 <<< 16) |||
    (((x >>> 8) &&& 0xFF).toUInt8.toUInt32 <<< 8) |||
    ((x &&& 0xFF).toUInt8.toUInt32) = x := by
  apply UInt32.toNat_inj.mp
  have hFF : (0xFF : UInt32).toNat = 255 := rfl
  have h255 : (255 : Nat) = 2 ^ 8 - 1 := by decide
  have hx := x.toNat_lt
  have hb0 : (((x >>> 24) &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat / 2 ^ 24 % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((24 : UInt32).toNat % 32) = 24 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hb1 : (((x >>> 16) &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat / 2 ^ 16 % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((16 : UInt32).toNat % 32) = 16 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hb2 : (((x >>> 8) &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat / 2 ^ 8 % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((8 : UInt32).toNat % 32) = 8 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hb3 : ((x &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hs24 : ∀ b : UInt32, b.toNat < 2 ^ 8 →
      (b <<< (24 : UInt32)).toNat = b.toNat * 2 ^ 24 := by
    intro b hb
    rw [UInt32.toNat_shiftLeft, show ((24 : UInt32).toNat % 32) = 24 from rfl,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    have h1 : b.toNat * 2 ^ 24 < 2 ^ 8 * 2 ^ 24 :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos 24)).mpr hb
    have h2 : (2:Nat) ^ 8 * 2 ^ 24 = 2 ^ 32 := by decide
    omega
  have hs16 : ∀ b : UInt32, b.toNat < 2 ^ 8 →
      (b <<< (16 : UInt32)).toNat = b.toNat * 2 ^ 16 := by
    intro b hb
    rw [UInt32.toNat_shiftLeft, show ((16 : UInt32).toNat % 32) = 16 from rfl,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    have h1 : b.toNat * 2 ^ 16 < 2 ^ 8 * 2 ^ 16 :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos 16)).mpr hb
    have h2 : (2:Nat) ^ 8 * 2 ^ 16 = 2 ^ 24 := by decide
    have h3 : (2:Nat) ^ 24 < 2 ^ 32 := by decide
    omega
  have hs8 : ∀ b : UInt32, b.toNat < 2 ^ 8 →
      (b <<< (8 : UInt32)).toNat = b.toNat * 2 ^ 8 := by
    intro b hb
    rw [UInt32.toNat_shiftLeft, show ((8 : UInt32).toNat % 32) = 8 from rfl,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    have h1 : b.toNat * 2 ^ 8 < 2 ^ 8 * 2 ^ 8 :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos 8)).mpr hb
    have h2 : (2:Nat) ^ 8 * 2 ^ 8 = 2 ^ 16 := by decide
    have h3 : (2:Nat) ^ 16 < 2 ^ 32 := by decide
    omega
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    hs24 _ (by rw [hb0]; exact Nat.mod_lt _ (by decide)),
    hs16 _ (by rw [hb1]; exact Nat.mod_lt _ (by decide)),
    hs8 _ (by rw [hb2]; exact Nat.mod_lt _ (by decide)),
    hb0, hb1, hb2, hb3]
  have hdvd_shift : ∀ (y a b : Nat), b ≤ a → (2:Nat) ^ b ∣ y * 2 ^ a := by
    intro y a b hba
    refine ⟨y * 2 ^ (a - b), ?_⟩
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ b) y, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hm0 : x.toNat / 2 ^ 24 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hm1 : x.toNat / 2 ^ 16 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hm2 : x.toNat / 2 ^ 8 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hm3 : x.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have ho1 : (x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 ||| (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16
      = (x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 + (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 := by
    apply nat_or_add (k := 24)
    · exact Nat.mod_eq_zero_of_dvd (hdvd_shift _ 24 24 (by omega))
    · have h2 : (2:Nat) ^ 8 * 2 ^ 16 = 2 ^ 24 := by decide
      have := (Nat.mul_lt_mul_right (Nat.two_pow_pos 16)).mpr hm1
      omega
  rw [ho1]
  have ho2 : ((x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 + (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16)
        ||| (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8
      = ((x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 + (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16)
        + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 := by
    apply nat_or_add (k := 16)
    · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add
        (hdvd_shift _ 24 16 (by omega)) (hdvd_shift _ 16 16 (by omega)))
    · have h2 : (2:Nat) ^ 8 * 2 ^ 8 = 2 ^ 16 := by decide
      have := (Nat.mul_lt_mul_right (Nat.two_pow_pos 8)).mpr hm2
      omega
  rw [ho2]
  have ho3 : ((x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 + (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16
        + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8) ||| (x.toNat % 2 ^ 8)
      = ((x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 + (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16
        + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8) + x.toNat % 2 ^ 8 := by
    apply nat_or_add (k := 8)
    · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_add
        (hdvd_shift _ 24 8 (by omega)) (hdvd_shift _ 16 8 (by omega)))
        (hdvd_shift _ 8 8 (by omega)))
    · exact hm3
  rw [ho3]
  -- pure Euclidean bookkeeping on constants
  have e24 : (2:Nat) ^ 24 = 16777216 := by decide
  have e16 : (2:Nat) ^ 16 = 65536 := by decide
  have e8 : (2:Nat) ^ 8 = 256 := by decide
  have e32 : (2:Nat) ^ 32 = 4294967296 := by decide
  rw [e24, e16, e8] at *
  omega

/-
## The ZLIB (RFC 1950) container roundtrip.
-/

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- The byte-copy `for` loop over a `ByteArray`, characterized pointwise. -/
theorem byteArray_forIn_push_spec (src acc : ByteArray) :
    (forIn (m := Id) src acc (fun x o => pure (ForInStep.yield (o.push x)))).size
      = acc.size + src.size ∧
    (∀ j, j < acc.size → (forIn (m := Id) src acc
      (fun x o => pure (ForInStep.yield (o.push x)))).get! j = acc.get! j) ∧
    (∀ j, j < src.size → (forIn (m := Id) src acc
      (fun x o => pure (ForInStep.yield (o.push x)))).get! (acc.size + j) = src.get! j) := by
  have h := byteArray_copy_loop src src.size (Nat.le_refl _) acc
  refine ⟨h.1, h.2.1, ?_⟩
  intro j hj
  have h3 := h.2.2 j hj
  rw [show src.size - src.size + j = j from by omega] at h3
  exact h3

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- `zlibCompress`'s output, byte by byte: the 2-byte header, the DEFLATE payload, and
    the four big-endian Adler-32 bytes. -/
theorem zlibCompress_spec (data : ByteArray) :
    (zlibCompress data).size = (compress data).size + 6 ∧
    (zlibCompress data).get! 0 = 0x78 ∧
    (zlibCompress data).get! 1 = 0x01 ∧
    (∀ j, j < (compress data).size →
      (zlibCompress data).get! (2 + j) = (compress data).get! j) ∧
    (zlibCompress data).get! ((compress data).size + 2) = ((adler32 data) >>> 24 &&& 0xFF).toUInt8 ∧
    (zlibCompress data).get! ((compress data).size + 3) = ((adler32 data) >>> 16 &&& 0xFF).toUInt8 ∧
    (zlibCompress data).get! ((compress data).size + 4) = ((adler32 data) >>> 8 &&& 0xFF).toUInt8 ∧
    (zlibCompress data).get! ((compress data).size + 5) = ((adler32 data) &&& 0xFF).toUInt8 := by
  have hzc : zlibCompress data =
      ((((forIn (m := Id) (compress data) ((ByteArray.empty.push 0x78).push 0x01)
          (fun b o => pure (ForInStep.yield (o.push b)))).push
            ((adler32 data) >>> 24 &&& 0xFF).toUInt8).push
            ((adler32 data) >>> 16 &&& 0xFF).toUInt8).push
            ((adler32 data) >>> 8 &&& 0xFF).toUInt8).push
            ((adler32 data) &&& 0xFF).toUInt8 := by
    conv => lhs; unfold zlibCompress
    simp only [Id.run, pure_bind, bind_pure]
    rfl
  have hspec := byteArray_forIn_push_spec (compress data) ((ByteArray.empty.push 0x78).push 0x01)
  have hhs : ((ByteArray.empty.push 0x78).push 0x01).size = 2 := rfl
  rw [hhs] at hspec
  obtain ⟨hsz, hpre, hmid⟩ := hspec
  -- name the loop result
  obtain ⟨body, hbody⟩ : ∃ b, forIn (m := Id) (compress data)
      ((ByteArray.empty.push 0x78).push 0x01)
      (fun b o => pure (ForInStep.yield (o.push b))) = b := ⟨_, rfl⟩
  rw [hbody] at hsz hpre hmid hzc
  have hn2 : body.size = 2 + (compress data).size := hsz
  rw [hzc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ByteArray.size_push]
    omega
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega)]
    have h := hpre 0 (by omega)
    rw [h]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega)]
    have h := hpre 1 (by omega)
    rw [h]
    rfl
  · intro j hj
    rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega)]
    exact hmid j hj
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- The DEFLATE slice of the container is exactly the payload. -/
theorem zlibCompress_extract (data : ByteArray) :
    (zlibCompress data).extract 2 ((zlibCompress data).size - 4) = compress data := by
  obtain ⟨hsz, h0, h1, hmid, _, _, _, _⟩ := zlibCompress_spec data
  have hsz_e : ((zlibCompress data).extract 2 ((zlibCompress data).size - 4)).size
      = (compress data).size := by
    rw [ByteArray.size_extract, hsz]
    omega
  apply ByteArray.ext_get! hsz_e
  intro i hi
  rw [hsz_e] at hi
  rw [ByteArray.get!_eq_getElem _ i (by rw [hsz_e]; exact hi),
    ByteArray.getElem_extract,
    ← ByteArray.get!_eq_getElem _ _ (by rw [hsz]; omega)]
  exact hmid i hi

/- REF: docs/STDLIB_ZLIB.md#51-zlib-format-rfc-1950 -/
/-- **L9 (ZLIB): RFC 1950 container roundtrip soundness, universal over the input.** -/
theorem zlib_roundtrip_soundness (data : ByteArray) :
    zlibDecompress (zlibCompress data) = .ok data := by
  obtain ⟨hsz, h0, h1, hmid, ha0, ha1, ha2, ha3⟩ := zlibCompress_spec data
  unfold zlibDecompress
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (show ¬ (zlibCompress data).size < 6 from by omega)]
  rw [h0, h1]
  rw [if_neg (show ¬ ((((0x78 : UInt8).toNat * 256 + (0x01 : UInt8).toNat) % 31 != 0) = true)
    from by decide)]
  rw [if_neg (show ¬ (((0x78 : UInt8).toNat &&& 15 != 8) = true) from by decide)]
  rw [show (if (((0x01 : UInt8).toNat >>> 5 &&& 1) == 1) = true then 6 else 2) = 2 from rfl]
  rw [if_neg (show ¬ (zlibCompress data).size < 2 + 4 from by omega)]
  rw [zlibCompress_extract data, deflate_roundtrip_soundness data]
  show (if ((((zlibCompress data).get! ((zlibCompress data).size - 4)).toUInt32 <<< 24 |||
        (((zlibCompress data).get! ((zlibCompress data).size - 3)).toUInt32 <<< 16) |||
        (((zlibCompress data).get! ((zlibCompress data).size - 2)).toUInt32 <<< 8) |||
        ((zlibCompress data).get! ((zlibCompress data).size - 1)).toUInt32) != adler32 data) = true
      then _ else _) = Except.ok data
  rw [hsz,
    show (compress data).size + 6 - 4 = (compress data).size + 2 from by omega,
    show (compress data).size + 6 - 3 = (compress data).size + 3 from by omega,
    show (compress data).size + 6 - 2 = (compress data).size + 4 from by omega,
    show (compress data).size + 6 - 1 = (compress data).size + 5 from by omega,
    ha0, ha1, ha2, ha3, uint32_be_reassemble (adler32 data), bne_self_eq_false]
  rw [if_neg (by simp)]

/-
## The GZIP (RFC 1952) container roundtrip.
-/

set_option maxHeartbeats 1000000 in
/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Little-endian byte split/reassembly for a 32-bit word, in the decoder's
    `c0 ||| (c1 <<< 8) ||| (c2 <<< 16) ||| (c3 <<< 24)` shape. -/
theorem uint32_le_reassemble (x : UInt32) :
    (x &&& 0xFF).toUInt8.toUInt32 |||
    (((x >>> 8) &&& 0xFF).toUInt8.toUInt32 <<< 8) |||
    (((x >>> 16) &&& 0xFF).toUInt8.toUInt32 <<< 16) |||
    (((x >>> 24) &&& 0xFF).toUInt8.toUInt32 <<< 24) = x := by
  apply UInt32.toNat_inj.mp
  have hFF : (0xFF : UInt32).toNat = 255 := rfl
  have h255 : (255 : Nat) = 2 ^ 8 - 1 := by decide
  have hx := x.toNat_lt
  have hb0 : (((x >>> 24) &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat / 2 ^ 24 % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((24 : UInt32).toNat % 32) = 24 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hb1 : (((x >>> 16) &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat / 2 ^ 16 % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((16 : UInt32).toNat % 32) = 16 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hb2 : (((x >>> 8) &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat / 2 ^ 8 % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    rw [show ((8 : UInt32).toNat % 32) = 8 from rfl,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hb3 : ((x &&& 0xFF).toUInt8.toUInt32).toNat = x.toNat % 2 ^ 8 := by
    rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_and,
      hFF, h255, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^8 ∣ 2^8)]
  have hs : ∀ (b : UInt32) (c : UInt32) (k : Nat), b.toNat < 2 ^ 8 → c.toNat % 32 = k →
      k ≤ 24 → (b <<< c).toNat = b.toNat * 2 ^ k := by
    intro b c k hb hc hk
    rw [UInt32.toNat_shiftLeft, hc, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    have h1 : b.toNat * 2 ^ k < 2 ^ 8 * 2 ^ k :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).mpr hb
    have h2 : (2:Nat) ^ 8 * 2 ^ k ≤ 2 ^ 8 * 2 ^ 24 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)
    have h3 : (2:Nat) ^ 8 * 2 ^ 24 = 2 ^ 32 := by decide
    omega
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    hs _ 8 8 (by rw [hb2]; exact Nat.mod_lt _ (by decide)) rfl (by omega),
    hs _ 16 16 (by rw [hb1]; exact Nat.mod_lt _ (by decide)) rfl (by omega),
    hs _ 24 24 (by rw [hb0]; exact Nat.mod_lt _ (by decide)) rfl (by omega),
    hb0, hb1, hb2, hb3]
  have hm0 : x.toNat / 2 ^ 24 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hm1 : x.toNat / 2 ^ 16 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hm2 : x.toNat / 2 ^ 8 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hm3 : x.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  -- fold the little-endian or-chain into a sum, low bits first
  have ho1 : (x.toNat % 2 ^ 8) ||| (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8
      = x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 := by
    conv => lhs; rw [show (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8
      = (x.toNat / 2 ^ 8 % 2 ^ 8) <<< 8 from by rw [Nat.shiftLeft_eq]]
    exact lor_shiftLeft_eq_add hm3
  rw [ho1]
  have ho2 : (x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8) |||
        (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16
      = (x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8) +
        (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 := by
    have hlt : x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 < 2 ^ 16 := by
      have h2 : (2:Nat) ^ 8 * 2 ^ 8 = 2 ^ 16 := by decide
      have := (Nat.mul_lt_mul_right (Nat.two_pow_pos 8)).mpr hm2
      omega
    conv => lhs; rw [show (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16
      = (x.toNat / 2 ^ 16 % 2 ^ 8) <<< 16 from by rw [Nat.shiftLeft_eq]]
    exact lor_shiftLeft_eq_add hlt
  rw [ho2]
  have ho3 : (x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 +
        (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16) ||| (x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24
      = (x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 +
        (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16) + (x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24 := by
    have hlt : x.toNat % 2 ^ 8 + (x.toNat / 2 ^ 8 % 2 ^ 8) * 2 ^ 8 +
        (x.toNat / 2 ^ 16 % 2 ^ 8) * 2 ^ 16 < 2 ^ 24 := by
      have h2 : (2:Nat) ^ 8 * 2 ^ 8 = 2 ^ 16 := by decide
      have h3 : (2:Nat) ^ 8 * 2 ^ 16 = 2 ^ 24 := by decide
      have hA := (Nat.mul_lt_mul_right (Nat.two_pow_pos 8)).mpr hm2
      have hB := (Nat.mul_lt_mul_right (Nat.two_pow_pos 16)).mpr hm1
      omega
    conv => lhs; rw [show (x.toNat / 2 ^ 24 % 2 ^ 8) * 2 ^ 24
      = (x.toNat / 2 ^ 24 % 2 ^ 8) <<< 24 from by rw [Nat.shiftLeft_eq]]
    exact lor_shiftLeft_eq_add hlt
  rw [ho3]
  have e24 : (2:Nat) ^ 24 = 16777216 := by decide
  have e16 : (2:Nat) ^ 16 = 65536 := by decide
  have e8 : (2:Nat) ^ 8 = 256 := by decide
  rw [e8] at hm0 hm1 hm2 hm3
  rw [e24, e16, e8]
  omega

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- `gzipCompress`'s output, byte by byte: the fixed 10-byte header, the fixed-Huffman
    DEFLATE payload, the little-endian CRC-32, and the little-endian ISIZE. -/
theorem gzipCompress_spec (data : ByteArray) :
    (gzipCompress data).size = (compressFixed data).size + 18 ∧
    ((gzipCompress data).get! 0 = 0x1F ∧ (gzipCompress data).get! 1 = 0x8B ∧
     (gzipCompress data).get! 2 = 0x08 ∧ (gzipCompress data).get! 3 = 0x00) ∧
    (∀ j, j < (compressFixed data).size →
      (gzipCompress data).get! (10 + j) = (compressFixed data).get! j) ∧
    ((gzipCompress data).get! ((compressFixed data).size + 10) = ((crc32 data) &&& 0xFF).toUInt8 ∧
     (gzipCompress data).get! ((compressFixed data).size + 11) = ((crc32 data) >>> 8 &&& 0xFF).toUInt8 ∧
     (gzipCompress data).get! ((compressFixed data).size + 12) = ((crc32 data) >>> 16 &&& 0xFF).toUInt8 ∧
     (gzipCompress data).get! ((compressFixed data).size + 13) = ((crc32 data) >>> 24 &&& 0xFF).toUInt8) ∧
    ((gzipCompress data).get! ((compressFixed data).size + 14) = (data.size.toUInt32 &&& 0xFF).toUInt8 ∧
     (gzipCompress data).get! ((compressFixed data).size + 15) = (data.size.toUInt32 >>> 8 &&& 0xFF).toUInt8 ∧
     (gzipCompress data).get! ((compressFixed data).size + 16) = (data.size.toUInt32 >>> 16 &&& 0xFF).toUInt8 ∧
     (gzipCompress data).get! ((compressFixed data).size + 17) = (data.size.toUInt32 >>> 24 &&& 0xFF).toUInt8) := by
  have hzc : gzipCompress data =
      ((((((((forIn (m := Id) (compressFixed data)
          ((((((((((ByteArray.empty.push 0x1F).push 0x8B).push 0x08).push 0x00).push
            0x00).push 0x00).push 0x00).push 0x00).push 0x02).push 0x03)
          (fun b o => pure (ForInStep.yield (o.push b)))).push
            ((crc32 data) &&& 0xFF).toUInt8).push
            ((crc32 data) >>> 8 &&& 0xFF).toUInt8).push
            ((crc32 data) >>> 16 &&& 0xFF).toUInt8).push
            ((crc32 data) >>> 24 &&& 0xFF).toUInt8).push
            (data.size.toUInt32 &&& 0xFF).toUInt8).push
            (data.size.toUInt32 >>> 8 &&& 0xFF).toUInt8).push
            (data.size.toUInt32 >>> 16 &&& 0xFF).toUInt8).push
            (data.size.toUInt32 >>> 24 &&& 0xFF).toUInt8 := by
    conv => lhs; unfold gzipCompress
    simp only [Id.run, pure_bind, bind_pure]
    rfl
  have hspec := byteArray_forIn_push_spec (compressFixed data)
    ((((((((((ByteArray.empty.push 0x1F).push 0x8B).push 0x08).push 0x00).push
      0x00).push 0x00).push 0x00).push 0x00).push 0x02).push 0x03)
  have hhs : ((((((((((ByteArray.empty.push 0x1F).push 0x8B).push 0x08).push 0x00).push
      (0x00 : UInt8)).push 0x00).push 0x00).push 0x00).push 0x02).push 0x03).size = 10 := rfl
  rw [hhs] at hspec
  obtain ⟨hsz, hpre, hmid⟩ := hspec
  obtain ⟨body, hbody⟩ : ∃ b, forIn (m := Id) (compressFixed data)
      ((((((((((ByteArray.empty.push 0x1F).push 0x8B).push 0x08).push 0x00).push
        0x00).push 0x00).push 0x00).push 0x00).push 0x02).push 0x03)
      (fun b o => pure (ForInStep.yield (o.push b))) = b := ⟨_, rfl⟩
  rw [hbody] at hsz hpre hmid hzc
  rw [hzc]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [ByteArray.size_push]
    omega
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega), hpre 0 (by omega)]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega), hpre 1 (by omega)]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega), hpre 2 (by omega)]
    rfl
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega), hpre 3 (by omega)]
    rfl
  · intro j hj
    rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by omega)]
    exact hmid j hj
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]
  · rw [ByteArray.get!_push_eq _ _ _ (by simp only [ByteArray.size_push]; omega)]

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- The DEFLATE slice of the GZIP container is exactly the fixed-Huffman payload. -/
theorem gzipCompress_extract (data : ByteArray) :
    (gzipCompress data).extract 10 ((gzipCompress data).size - 8) = compressFixed data := by
  obtain ⟨hsz, _, hmid, _, _⟩ := gzipCompress_spec data
  have hsz_e : ((gzipCompress data).extract 10 ((gzipCompress data).size - 8)).size
      = (compressFixed data).size := by
    rw [ByteArray.size_extract, hsz]
    omega
  apply ByteArray.ext_get! hsz_e
  intro i hi
  rw [hsz_e] at hi
  rw [ByteArray.get!_eq_getElem _ i (by rw [hsz_e]; exact hi),
    ByteArray.getElem_extract,
    ← ByteArray.get!_eq_getElem _ _ (by rw [hsz]; omega)]
  exact hmid i hi

set_option maxHeartbeats 1000000 in
/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- **L9 (GZIP): RFC 1952 container roundtrip soundness, universal over the input** —
    through the Law 12 connection theorem, since `gzipCompress` calls `compressFixed`. -/
theorem gzip_roundtrip_soundness (data : ByteArray) :
    gzipDecompress (gzipCompress data) = .ok data := by
  obtain ⟨hsz, ⟨h0, h1, h2, h3⟩, hmid, ⟨hc0, hc1, hc2, hc3⟩, ⟨hi0, hi1, hi2, hi3⟩⟩ :=
    gzipCompress_spec data
  unfold gzipDecompress
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (show ¬ (gzipCompress data).size < 18 from by omega)]
  rw [h0, h1]
  rw [if_neg (show ¬ (((0x1F : UInt8) != 31 || (0x8B : UInt8) != 139) = true) from by decide)]
  rw [h2]
  rw [if_neg (show ¬ (((0x08 : UInt8) != 8) = true) from by decide)]
  rw [h3]
  rw [if_neg (show ¬ (((0x00 : UInt8) &&& 4 != 0) = true) from by decide)]
  rw [if_neg (show ¬ (((0x00 : UInt8) &&& 8 != 0) = true) from by decide)]
  rw [if_neg (show ¬ (((0x00 : UInt8) &&& 16 != 0) = true) from by decide)]
  rw [if_neg (show ¬ (((0x00 : UInt8) &&& 2 != 0) = true) from by decide)]
  rw [if_neg (show ¬ 10 + 8 > (gzipCompress data).size from by omega)]
  rw [gzipCompress_extract data, compressFixed_roundtrip_soundness data]
  show (if ((((gzipCompress data).get! ((gzipCompress data).size - 8)).toUInt32 |||
        (((gzipCompress data).get! ((gzipCompress data).size - 7)).toUInt32 <<< 8) |||
        (((gzipCompress data).get! ((gzipCompress data).size - 6)).toUInt32 <<< 16) |||
        (((gzipCompress data).get! ((gzipCompress data).size - 5)).toUInt32 <<< 24)) !=
          crc32 data) = true
      then _ else _) = Except.ok data
  rw [hsz,
    show (compressFixed data).size + 18 - 8 = (compressFixed data).size + 10 from by omega,
    show (compressFixed data).size + 18 - 7 = (compressFixed data).size + 11 from by omega,
    show (compressFixed data).size + 18 - 6 = (compressFixed data).size + 12 from by omega,
    show (compressFixed data).size + 18 - 5 = (compressFixed data).size + 13 from by omega,
    show (compressFixed data).size + 18 - 4 = (compressFixed data).size + 14 from by omega,
    show (compressFixed data).size + 18 - 3 = (compressFixed data).size + 15 from by omega,
    show (compressFixed data).size + 18 - 2 = (compressFixed data).size + 16 from by omega,
    show (compressFixed data).size + 18 - 1 = (compressFixed data).size + 17 from by omega,
    hc0, hc1, hc2, hc3, hi0, hi1, hi2, hi3,
    uint32_le_reassemble (crc32 data), bne_self_eq_false]
  rw [if_neg (by simp)]
  rw [uint32_le_reassemble (data.size.toUInt32), bne_self_eq_false]
  rw [if_neg (by simp)]

/-
## PA16 retirement: the container `*_inst` checks as corollaries of the universal theorems

Statements are byte-for-byte the originals from `Stdlib/Zlib/Equivalence.lean`; only the
proofs changed — each is now a one-line instantiation of the universal container
roundtrip, with no `native_decide`.
-/

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- ZLIB container roundtrip at a literal: direct instance of `zlib_roundtrip_soundness`. -/
theorem zlib_roundtrip_soundness_inst :
    let data := "Testing ZLIB RFC 1950 container format roundtrip soundness.".toUTF8
    (match zlibDecompress (zlibCompress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  intro data
  rw [zlib_roundtrip_soundness]
  exact byteArray_beq_self _

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- GZIP container roundtrip at a literal: direct instance of `gzip_roundtrip_soundness`. -/
theorem gzip_roundtrip_soundness_inst :
    let data := "Testing GZIP RFC 1952 container format roundtrip soundness.".toUTF8
    (match gzipDecompress (gzipCompress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  intro data
  rw [gzip_roundtrip_soundness]
  exact byteArray_beq_self _

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Canonical 1.5-roundtrip for ZLIB: both decompressions instantiate
    `zlib_roundtrip_soundness`. -/
theorem zlib_idempotent_canonical_roundtrip_inst :
    let testStream := zlibCompress "Canonical ZLIB 1.5-roundtrip test.".toUTF8
    (match zlibDecompress testStream with
     | Except.error _ => false
     | Except.ok data =>
       match zlibDecompress (zlibCompress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  intro testStream
  rw [show testStream = zlibCompress "Canonical ZLIB 1.5-roundtrip test.".toUTF8 from rfl,
    zlib_roundtrip_soundness]
  show (match zlibDecompress (zlibCompress "Canonical ZLIB 1.5-roundtrip test.".toUTF8) with
    | Except.ok res => res == "Canonical ZLIB 1.5-roundtrip test.".toUTF8
    | Except.error _ => false) = true
  rw [zlib_roundtrip_soundness]
  exact byteArray_beq_self _

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Canonical 1.5-roundtrip for GZIP: both decompressions instantiate
    `gzip_roundtrip_soundness`. -/
theorem gzip_idempotent_canonical_roundtrip_inst :
    let testStream := gzipCompress "Canonical GZIP 1.5-roundtrip test.".toUTF8
    (match gzipDecompress testStream with
     | Except.error _ => false
     | Except.ok data =>
       match gzipDecompress (gzipCompress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  intro testStream
  rw [show testStream = gzipCompress "Canonical GZIP 1.5-roundtrip test.".toUTF8 from rfl,
    gzip_roundtrip_soundness]
  show (match gzipDecompress (gzipCompress "Canonical GZIP 1.5-roundtrip test.".toUTF8) with
    | Except.ok res => res == "Canonical GZIP 1.5-roundtrip test.".toUTF8
    | Except.error _ => false) = true
  rw [gzip_roundtrip_soundness]
  exact byteArray_beq_self _

end Stdlib.Zlib

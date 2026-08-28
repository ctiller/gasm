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
import Stdlib.Zlib.CRC32
import Stdlib.Zlib.Adler32
import Stdlib.Zlib.Deflate
import Stdlib.Zlib.Spec
import Stdlib.Zlib.Gzip

namespace Stdlib.Zlib

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Exact bit-reversal involution theorem verified across all 256 possible 8-bit quantities. -/
theorem reverse_bits_8_involutive_inst :
    (Id.run do
      let mut ok := true
      for b in [0:256] do
        if reverseBits (reverseBits b 8) 8 != b then ok := false
      ok) = true := by
  simp [Id.run, reverseBits]
  decide

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Exact length encoding bound preservation verified across all 256 valid length ranges (3..258). -/
theorem encode_length_bounds_inst :
    (Id.run do
      let mut ok := true
      for len in [3:259] do
        let (code, _, _) := encodeLength len
        if code < 257 || code > 285 then ok := false
      ok) = true := by
  simp [Id.run, encodeLength]
  decide

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- One-level unfolding lemma for a decidable-`ite` whose branches are conditionally bounded --
    used to peel `encodeDistance`'s ~26-deep threshold-band `if`/`else` chain one band at a
    time below. Cheap: unlike calling `split` directly on the fully nested chain (which drives
    an internal `simp` congruence pass over the *entire* remaining nested term and exceeds its
    step budget), applying this lemma repeatedly only ever unifies against one `ite` head at a
    time, leaving the (still nested) `else` branch as an opaque metavariable for the next
    application. -/
theorem ite_fst_le {c : Prop} [Decidable c] (a b : Nat × Nat × Nat) (n : Nat)
    (ha : c → a.1 ≤ n) (hb : ¬c → b.1 ≤ n) : (if c then a else b).1 ≤ n := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- `encodeDistance`'s code component never exceeds 29, for every `dist`, not just the
    32768-element sampled range below -- `encodeDistance` is a plain (non-recursive)
    if-then-else chain over ~26 fixed threshold bands, each branch returning a literal code
    in `[0,29]` (or `dist - 1`, when `dist ≤ 4`, itself `≤ 3`); `ite_fst_le` peels one band at
    a time and `omega` closes each resulting leaf, with no enumeration over any of the 32768
    concrete `dist` values. -/
theorem encodeDistance_code_le_29 (dist : Nat) : (encodeDistance dist).1 ≤ 29 := by
  unfold encodeDistance
  repeat' (apply ite_fst_le <;> intro h)
  all_goals omega

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- Exact distance encoding bound preservation verified across all 32768 valid distance ranges
    (1..32768). Proven structurally, not by enumeration: plain kernel `decide` on this loop
    times out (`whnf`/`isDefEq` heartbeat exhaustion observed at 32768 iterations, unlike the
    256-element `reverse_bits_8_involutive_inst`/`encode_length_bounds_inst` above, which
    `decide` closes directly). Instead, the `Id.run`/`for` loop is normalized to a plain
    `List.foldl` via Lean's own `forIn_eq_forIn_range'`/`forIn_pure_yield_eq_foldl` simp set
    (the same reformulation `Stdlib/Zlib/CRC32Equivalence.lean`'s `updateCrc32_eq_fold` uses),
    then `foldl_ite_false_of_forall` shows the flag can never flip given
    `encodeDistance_code_le_29` holds for every element -- an `O(1)`-size structural argument
    independent of how many of the 32768 concrete values are visited. -/
theorem encode_distance_bounds_inst :
    (Id.run do
      let mut ok := true
      for dist in [1:32769] do
        let (code, _, _) := encodeDistance dist
        if code > 29 then ok := false
      ok) = true := by
  have foldl_ite_false_of_forall : ∀ (l : List Nat) (p : Nat → Prop) [DecidablePred p],
      (∀ x ∈ l, ¬ p x) → l.foldl (fun ok x => if p x then false else ok) true = true := by
    intro l p _ h
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      have hhd : ¬ p hd := h hd (by simp)
      simp only [List.foldl_cons, if_neg hhd]
      exact ih (fun x hx => h x (by simp [hx]))
  have ite_pure_yield : ∀ {c : Prop} [Decidable c] (a b : Bool),
      (if c then (pure (ForInStep.yield a) : Id (ForInStep Bool)) else pure (ForInStep.yield b)) =
        pure (ForInStep.yield (if c then a else b)) := by
    intro c _ a b; split <;> rfl
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  exact foldl_ite_false_of_forall _ (fun dist => (encodeDistance dist).1 > 29)
    (fun dist _ => by have := encodeDistance_code_le_29 dist; omega)

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Empty data DEFLATE roundtrip soundness. -/
theorem deflate_roundtrip_empty_inst :
    (match decompress (compress ByteArray.empty) with
     | Except.ok res => res == ByteArray.empty
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: DEFLATE roundtrip soundness on hello world ASCII bytes. -/
theorem deflate_roundtrip_soundness_inst :
    let data := "Hello, World! Verified DEFLATE in Lean 4.".toUTF8
    (match decompress (compress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Repetitive run DEFLATE roundtrip soundness. -/
theorem deflate_roundtrip_repetitive_inst :
    let data := ByteArray.mk #[42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
    (match decompress (compress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: ZLIB RFC 1950 container roundtrip soundness with Adler-32 verification. -/
theorem zlib_roundtrip_soundness_inst :
    let data := "Testing ZLIB RFC 1950 container format roundtrip soundness.".toUTF8
    (match zlibDecompress (zlibCompress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: GZIP RFC 1952 container roundtrip soundness with CRC-32 & ISIZE verification. -/
theorem gzip_roundtrip_soundness_inst :
    let data := "Testing GZIP RFC 1952 container format roundtrip soundness.".toUTF8
    (match gzipDecompress (gzipCompress data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for DEFLATE on arbitrary streams.
    The outer `Except.error _ => false` is deliberate (2026-08-27, PA16 Phase 1 vacuity fix): the
    prior `=> true` here meant a `decompress` that always failed would still discharge this theorem,
    since `testStream` is a fixed, already-known-good literal and the check never required the
    initial decompress to actually succeed. This instance is still a single-ground-instance
    `native_decide` check (Law 9/10 non-compliant; tracked, not fixed, by
    docs/PA16_CODEC_SOUNDNESS.md), but it no longer has a branch that is vacuously satisfiable by a
    broken decompressor. The universal target this instance stands in for legitimately keeps
    `error => True` in its outer branch (see docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems
    and docs/PA16_CODEC_SOUNDNESS.md's opening finding) since not every `ByteArray` is a valid
    compressed stream; the vacuity concern applies only to a pointwise regression check over a
    literal already known to succeed. -/
theorem deflate_idempotent_canonical_roundtrip_inst :
    let testStream := compress "Canonical 1.5-roundtrip theorem test.".toUTF8
    (match decompress testStream with
     | Except.error _ => false
     | Except.ok data =>
       match decompress (compress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for ZLIB container streams.
    Outer `Except.error _ => false` per the 2026-08-27 PA16 Phase 1 vacuity fix -- see
    `deflate_idempotent_canonical_roundtrip_inst`'s doc comment above for the full rationale. -/
theorem zlib_idempotent_canonical_roundtrip_inst :
    let testStream := zlibCompress "Canonical ZLIB 1.5-roundtrip test.".toUTF8
    (match zlibDecompress testStream with
     | Except.error _ => false
     | Except.ok data =>
       match zlibDecompress (zlibCompress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for GZIP container streams.
    Outer `Except.error _ => false` per the 2026-08-27 PA16 Phase 1 vacuity fix -- see
    `deflate_idempotent_canonical_roundtrip_inst`'s doc comment above for the full rationale. -/
theorem gzip_idempotent_canonical_roundtrip_inst :
    let testStream := gzipCompress "Canonical GZIP 1.5-roundtrip test.".toUTF8
    (match gzipDecompress testStream with
     | Except.error _ => false
     | Except.ok data =>
       match gzipDecompress (gzipCompress data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

end Stdlib.Zlib

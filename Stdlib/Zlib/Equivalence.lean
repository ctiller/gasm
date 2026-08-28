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
import Stdlib.Zlib.ByteArrayBridge
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

/-
## PA16 token layer: L3 (match certificate) + L4 (self-overlap copy) + token-level L5

Universal, kernel-checked (rung 1, no `native_decide`/`decide` oracle) roundtrip soundness
for the LZ77 layer of DEFLATE — the layer of `decompress` below Huffman coding and
bitstream framing. `tokenize`'s greedy match emission relies only on the total certifying
predicate `matchValid` (the `findLongestMatch` search stays an untrusted heuristic), and
`expandTokens`'s copy loop is byte-for-byte the self-overlap semantics of
`decodeHuffmanStream`'s back-reference loop, so once PA16 P0 (the decoder's `partial def`
conversion) lands, `lz77_roundtrip_soundness` below is the L3/L4/L5 payload the full
`deflate_roundtrip_soundness` composes with the Huffman/bitstream layer (L1/L2).
-/

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- L3: unpacks a `matchValid` certificate into its propositional components — RFC 1951
    range bounds, window containment, and the per-position byte-agreement the copy
    induction (L4) consumes. -/
theorem matchValid_spec {data : ByteArray} {pos len dist : Nat}
    (h : matchValid data pos len dist = true) :
    3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768 ∧ dist ≤ pos ∧ pos + len ≤ data.size ∧
    ∀ j, j < len → data.get! (pos - dist + j) = data.get! (pos + j) := by
  simp only [matchValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- The reference copy loop grows the output by exactly the match length. -/
theorem lzCopy_size (dist : Nat) : ∀ (len : Nat) (out : ByteArray),
    (lzCopy dist len out).size = out.size + len := by
  intro len
  induction len with
  | zero => intro out; simp [lzCopy]
  | succ k ih =>
    intro out
    simp only [lzCopy, ih, ByteArray.size_push]
    omega

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- L4, the self-overlapping back-reference copy induction (PA16's hardest sub-lemma,
    `docs/PA16_CODEC_SOUNDNESS.md` §4 L4): if the output so far is exactly `data[0:pos]`
    and the match certificate holds at `pos`, then after copying `len` bytes from `dist`
    back the output is exactly `data[0:pos+len]`. The induction restructures the design
    doc's strong induction into a plain one: at every step the source index `pos - dist`
    lies strictly inside the already-correct prefix (`dist ≥ 1`), so the prefix invariant
    absorbs the `dist < len` self-overlap case with no separate case split — the
    certificate at offset 0 plus a one-position shift of the certificate re-establishes
    the invariant. -/
theorem lzCopy_prefix (data : ByteArray) (dist : Nat) :
    ∀ (len pos : Nat) (out : ByteArray),
      out.size = pos → 1 ≤ dist → dist ≤ pos →
      (∀ i, i < pos → out.get! i = data.get! i) →
      (∀ j, j < len → data.get! (pos - dist + j) = data.get! (pos + j)) →
      ∀ i, i < pos + len → (lzCopy dist len out).get! i = data.get! i := by
  intro len
  induction len with
  | zero =>
    intro pos out hsz _ _ hpref _ i hi
    simp only [lzCopy]
    exact hpref i (by omega)
  | succ k ih =>
    intro pos out hsz hd1 hdp hpref hmatch i hi
    have hsrc : out.get! (out.size - dist) = data.get! pos := by
      have h0 := hmatch 0 (by omega)
      have e1 : pos - dist + 0 = pos - dist := by omega
      have e2 : pos + 0 = pos := by omega
      rw [e1, e2] at h0
      have hlt : out.size - dist < pos := by omega
      rw [hpref _ hlt]
      have e3 : out.size - dist = pos - dist := by omega
      rw [e3, h0]
    simp only [lzCopy]
    rw [hsrc]
    refine ih (pos + 1) (out.push (data.get! pos)) ?_ hd1 (by omega) ?_ ?_ i (by omega)
    · rw [ByteArray.size_push]; omega
    · intro j hj
      rcases Nat.lt_or_ge j pos with hjlt | hjge
      · rw [ByteArray.get!_push_lt out _ j (by omega)]
        exact hpref j hjlt
      · have hjeq : j = pos := by omega
        rw [ByteArray.get!_push_eq out _ j (by omega), hjeq]
    · intro j hj
      have h1 := hmatch (j + 1) (by omega)
      have e1 : pos - dist + (j + 1) = pos + 1 - dist + j := by omega
      have e2 : pos + (j + 1) = pos + 1 + j := by omega
      rw [e1, e2] at h1
      exact h1

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- Token-level L5, the main induction: from any position whose expansion invariant holds,
    the tokenizer's remaining output expands to exactly `data`. Structural induction on the
    tokenizer's fuel; each literal step extends the prefix by one pushed byte, each
    certified match step extends it by `lzCopy_prefix` (L4). -/
theorem tokenizeAux_expand (data : ByteArray) :
    ∀ (fuel pos : Nat) (acc : Array LZToken),
      data.size ≤ pos + fuel → pos ≤ data.size →
      (acc.foldl expandToken ByteArray.empty).size = pos →
      (∀ i, i < pos → (acc.foldl expandToken ByteArray.empty).get! i = data.get! i) →
      (tokenizeAux data fuel pos acc).foldl expandToken ByteArray.empty = data := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos acc hfuel hpos hsz hpref
    simp only [tokenizeAux]
    have hpe : pos = data.size := by omega
    exact ByteArray.ext_get! (by omega) (fun i hi => hpref i (by omega))
  | succ k ih =>
    intro pos acc hfuel hpos hsz hpref
    simp only [tokenizeAux]
    by_cases hlt : pos < data.size
    · rw [if_pos hlt]
      by_cases hv : 3 ≤ (findLongestMatch data pos 32768 128).1 ∧
          matchValid data pos (findLongestMatch data pos 32768 128).1
            (findLongestMatch data pos 32768 128).2 = true
      · rw [if_pos hv]
        obtain ⟨hlen3, hmv⟩ := hv
        obtain ⟨_, _, hd1, _, hdp, hbound, hmatch⟩ := matchValid_spec hmv
        refine ih (pos + (findLongestMatch data pos 32768 128).1) _
          (by omega) (by omega) ?_ ?_
        · rw [Array.foldl_push]
          show (expandToken _ (.ref _ _)).size = _
          simp only [expandToken]
          rw [lzCopy_size, hsz]
        · intro i hi
          rw [Array.foldl_push]
          show (expandToken _ (.ref _ _)).get! i = _
          simp only [expandToken]
          exact lzCopy_prefix data _ _ pos _ hsz hd1 hdp hpref hmatch i hi
      · rw [if_neg hv]
        refine ih (pos + 1) _ (by omega) (by omega) ?_ ?_
        · rw [Array.foldl_push]
          show (expandToken _ (.lit _)).size = _
          simp only [expandToken]
          rw [ByteArray.size_push, hsz]
        · intro i hi
          rw [Array.foldl_push]
          show (expandToken _ (.lit _)).get! i = _
          simp only [expandToken]
          rcases Nat.lt_or_ge i pos with hilt | hige
          · rw [ByteArray.get!_push_lt _ _ i (by omega)]
            exact hpref i hilt
          · have hieq : i = pos := by omega
            rw [ByteArray.get!_push_eq _ _ i (by omega), hieq]
    · rw [if_neg hlt]
      exact ByteArray.ext_get! (by omega) (fun i hi => hpref i (by omega))

/- REF: docs/STDLIB_ZLIB.md#64-lz77-token-layer-roundtrip-soundness -/
/-- Universal LZ77 token-layer roundtrip soundness: for EVERY `ByteArray`, the greedy
    tokenizer's output — literals plus certified back-references, including
    self-overlapping RFC 1951 §3.2.3 matches — expands back to exactly the input.
    Kernel-checked structural proof (rung 1); no `native_decide`, no sampling. This is the
    L3+L4+token-level-L5 payload of the PA16 `deflate_roundtrip_soundness` decomposition;
    the Huffman/bitstream layer above it remains blocked on PA16 P0. -/
theorem lz77_roundtrip_soundness (data : ByteArray) :
    expandTokens (tokenize data) = data := by
  unfold expandTokens tokenize
  refine tokenizeAux_expand data data.size 0 #[] (by omega) (by omega) ?_ ?_
  · rfl
  · intro i hi
    omega

end Stdlib.Zlib

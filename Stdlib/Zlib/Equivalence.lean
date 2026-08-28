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

/-
## PA16 L1a: bitstream writer ghost algebra (write-append)

The `List Bool` ghost bit-sequence `docs/PA16_CODEC_SOUNDNESS.md` §4 L1 calls for, plus the
write-append law L1a: under the writer's operating invariant (pending bits fit the pending
count, pending count below a byte, no `UInt32` overflow), `writeBits` appends exactly the
`n` LSB-first bits of `v` to the emitted bit sequence — and re-establishes the invariant,
so consecutive `writeBits` calls compose. Kernel-checked structural proofs (rung 1).
-/

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- LSB-first list of the low `n` bits of `v` — the ghost denotation of `n` bits written
    with value `v`. -/
def natBits : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 == 1) :: natBits n (v / 2)

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost denotation of a finished byte buffer: each byte contributes its 8 bits LSB-first,
    bytes in order — exactly RFC 1951 §3.1.1's bit packing. -/
def bytesBits (bs : ByteArray) : List Bool :=
  bs.data.toList.flatMap fun b => natBits 8 b.toNat

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost denotation of a `BitWriter`: all fully emitted bytes followed by the pending
    sub-byte bits. -/
def writerBits (w : BitWriter) : List Bool :=
  bytesBits w.bytes ++ natBits w.bitCount w.bitBuf.toNat

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Splitting law for the ghost bit sequence: the low `m` bits of `a + b·2^m` (with `a`
    fitting in `m` bits) are the bits of `a`, followed by the bits of `b`. -/
theorem natBits_append (n : Nat) : ∀ (m a b : Nat), a < 2 ^ m →
    natBits (m + n) (a + b * 2 ^ m) = natBits m a ++ natBits n b := by
  intro m
  induction m with
  | zero =>
    intro a b ha
    have ha0 : a = 0 := by simp [Nat.pow_zero] at ha; omega
    subst ha0
    simp [natBits]
  | succ m ih =>
    intro a b ha
    have hc : b * 2 ^ (m + 1) = (b * 2 ^ m) * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
    have e : m + 1 + n = (m + n) + 1 := by omega
    rw [e]
    simp only [natBits]
    have hmod : (a + b * 2 ^ (m + 1)) % 2 = a % 2 := by
      rw [hc]; omega
    have hdiv : (a + b * 2 ^ (m + 1)) / 2 = a / 2 + b * 2 ^ m := by
      rw [hc]; omega
    rw [hmod, hdiv, ih (a / 2) b (by rw [hpow] at ha; omega)]
    rfl

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- The writer's `|||`-composition equals plain addition when the pending bits fit below
    the shift — the arithmetic form the ghost algebra computes with. -/
theorem lor_shiftLeft_eq_add {a v m : Nat} (ha : a < 2 ^ m) :
    a ||| v <<< m = a + v * 2 ^ m := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Pushing a byte appends its 8 bits to the buffer's ghost denotation. -/
theorem bytesBits_push (bs : ByteArray) (b : UInt8) :
    bytesBits (bs.push b) = bytesBits bs ++ natBits 8 b.toNat := by
  simp [bytesBits, ByteArray.data_push, Array.toList_push]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `flushBytes` invariant + ghost preservation: draining full bytes out of the pending
    buffer leaves fewer than 8 pending bits, keeps the pending value inside the pending
    count, and preserves the total emitted bit sequence exactly. -/
theorem flushBytes_spec : ∀ (cnt : Nat) (buf : UInt32) (acc : ByteArray),
    buf.toNat < 2 ^ cnt → cnt ≤ 32 →
    (writeBits.flushBytes buf cnt acc).2.1 < 8 ∧
    (writeBits.flushBytes buf cnt acc).1.toNat < 2 ^ (writeBits.flushBytes buf cnt acc).2.1 ∧
    bytesBits (writeBits.flushBytes buf cnt acc).2.2 ++
      natBits (writeBits.flushBytes buf cnt acc).2.1 (writeBits.flushBytes buf cnt acc).1.toNat
      = bytesBits acc ++ natBits cnt buf.toNat := by
  intro cnt
  induction cnt using Nat.strongRecOn with
  | ind cnt ih =>
    intro buf acc hbuf hcnt
    rw [writeBits.flushBytes]
    by_cases h8 : cnt ≥ 8
    · rw [if_pos h8]
      -- the recursive call's arguments
      have h256 : (2 : Nat) ^ 8 = 256 := by decide
      have hbyteNat : ((buf.toNat &&& 0xFF).toUInt8).toNat = buf.toNat % 256 := by
        have hmask : buf.toNat &&& 0xFF = buf.toNat % 256 := by
          have : (0xFF : Nat) = 2 ^ 8 - 1 := by decide
          rw [this, Nat.and_two_pow_sub_one_eq_mod, h256]
        simp [Nat.toUInt8, hmask, UInt8.toNat_ofNat']
      have hnewNat : ((buf.toNat >>> 8).toUInt32).toNat = buf.toNat / 256 := by
        have hshift : buf.toNat >>> 8 = buf.toNat / 256 := by
          rw [Nat.shiftRight_eq_div_pow, h256]
        have hlt : buf.toNat / 256 < 2 ^ 32 := by
          have h32 : (2 : Nat) ^ cnt ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hcnt
          omega
        simp [Nat.toUInt32, hshift, UInt32.toNat_ofNat']
        omega
      have hsplit : 2 ^ cnt = 2 ^ (cnt - 8) * 256 := by
        have : cnt = (cnt - 8) + 8 := by omega
        rw [this, Nat.pow_add, h256]
        have e2 : (cnt - 8) + 8 - 8 = cnt - 8 := by omega
        rw [e2]
      have hrec := ih (cnt - 8) (by omega) ((buf.toNat >>> 8).toUInt32)
        (acc.push (buf.toNat &&& 0xFF).toUInt8)
        (by rw [hnewNat]; rw [hsplit] at hbuf; omega)
        (by omega)
      refine ⟨hrec.1, hrec.2.1, ?_⟩
      rw [hrec.2.2, bytesBits_push, hbyteNat, hnewNat, List.append_assoc]
      congr 1
      have hdecomp : buf.toNat = buf.toNat % 256 + (buf.toNat / 256) * 2 ^ 8 := by
        rw [h256]; omega
      have happ := natBits_append (cnt - 8) 8 (buf.toNat % 256) (buf.toNat / 256)
        (by rw [h256]; omega)
      rw [← hdecomp] at happ
      have ecnt : 8 + (cnt - 8) = cnt := by omega
      rw [ecnt] at happ
      exact happ.symm
    · rw [if_neg h8]
      exact ⟨show cnt < 8 by omega, hbuf, rfl⟩

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- L1a, the write-append law (`docs/PA16_CODEC_SOUNDNESS.md` §4 L1): under the writer's
    operating invariant — pending value inside the pending count, pending count below a
    byte after any previous `writeBits` (`flushBytes_spec`), and no `UInt32` overflow
    (`bitCount + n ≤ 32`; every call site in `compress` writes ≤ 15 bits onto < 8 pending) —
    `writeBits w v n` with `v < 2^n` appends exactly the `n` LSB-first bits of `v` to the
    emitted ghost bit sequence, and re-establishes the invariant so calls compose. -/
theorem writerBits_writeBits (w : BitWriter) (v n : Nat)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount)
    (hv : v < 2 ^ n) (hcnt : w.bitCount + n ≤ 32) :
    writerBits (writeBits w v n) = writerBits w ++ natBits n v ∧
    (writeBits w v n).bitCount < 8 ∧
    (writeBits w v n).bitBuf.toNat < 2 ^ (writeBits w v n).bitCount := by
  unfold writeBits
  have hP1 : (1 : Nat) ≤ 2 ^ w.bitCount := Nat.one_le_two_pow
  have hQ1 : (1 : Nat) ≤ 2 ^ n := Nat.one_le_two_pow
  have hmul : v * 2 ^ w.bitCount ≤ (2 ^ n - 1) * 2 ^ w.bitCount :=
    Nat.mul_le_mul_right _ (by omega)
  have hsub : (2 ^ n - 1) * 2 ^ w.bitCount = 2 ^ n * 2 ^ w.bitCount - 2 ^ w.bitCount := by
    rw [Nat.sub_mul, Nat.one_mul]
  have hPQ : 2 ^ w.bitCount ≤ 2 ^ n * 2 ^ w.bitCount :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hpowadd : 2 ^ (w.bitCount + n) = 2 ^ n * 2 ^ w.bitCount := by
    rw [Nat.pow_add, Nat.mul_comm]
  have hsumlt : w.bitBuf.toNat + v * 2 ^ w.bitCount < 2 ^ (w.bitCount + n) := by
    rw [hpowadd]; omega
  have h32 : (2 : Nat) ^ (w.bitCount + n) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hcnt
  have hlor : w.bitBuf.toNat ||| v <<< w.bitCount =
      w.bitBuf.toNat + v * 2 ^ w.bitCount := lor_shiftLeft_eq_add hbuf
  have hnewNat : ((w.bitBuf.toNat ||| v <<< w.bitCount).toUInt32).toNat =
      w.bitBuf.toNat + v * 2 ^ w.bitCount := by
    simp [Nat.toUInt32, hlor, UInt32.toNat_ofNat']
    omega
  have hfb := flushBytes_spec (w.bitCount + n)
    ((w.bitBuf.toNat ||| v <<< w.bitCount).toUInt32) w.bytes
    (by rw [hnewNat]; exact hsumlt) hcnt
  refine ⟨?_, hfb.1, hfb.2.1⟩
  show bytesBits _ ++ natBits _ _ = _
  rw [hfb.2.2, hnewNat, natBits_append n w.bitCount w.bitBuf.toNat v hbuf,
    writerBits, List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Zero has all-false bits at every width. -/
theorem natBits_zero (n : Nat) : natBits n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natBits, ih, List.replicate_succ]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Writer half of L1c (`docs/PA16_CODEC_SOUNDNESS.md` §4 L1): byte-aligning flush emits
    exactly the writer's ghost bit sequence followed by sub-byte zero padding — the padding
    RFC 1951 decoding never reads, because it stops at the final block's EOB symbol. -/
theorem flushBitWriter_bits (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    bytesBits (flushBitWriter w) =
      writerBits w ++ List.replicate ((8 - w.bitCount) % 8) false := by
  unfold flushBitWriter writerBits
  by_cases h0 : w.bitCount > 0
  · rw [if_pos h0]
    have hsmall : w.bitBuf.toNat < 256 := by
      have : (2 : Nat) ^ w.bitCount ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      have h128 : (2 : Nat) ^ 7 = 128 := by decide
      omega
    have hbyteNat : ((w.bitBuf.toNat &&& 0xFF).toUInt8).toNat = w.bitBuf.toNat := by
      have hmask : w.bitBuf.toNat &&& 0xFF = w.bitBuf.toNat % 256 := by
        have : (0xFF : Nat) = 2 ^ 8 - 1 := by decide
        have h256 : (2 : Nat) ^ 8 = 256 := by decide
        rw [this, Nat.and_two_pow_sub_one_eq_mod, h256]
      simp [Nat.toUInt8, hmask, UInt8.toNat_ofNat']
      omega
    rw [bytesBits_push, hbyteNat]
    have happ := natBits_append (8 - w.bitCount) w.bitCount w.bitBuf.toNat 0 hbuf
    have e1 : w.bitBuf.toNat + 0 * 2 ^ w.bitCount = w.bitBuf.toNat := by omega
    have e2 : w.bitCount + (8 - w.bitCount) = 8 := by omega
    rw [e1, e2, natBits_zero] at happ
    have e3 : (8 - w.bitCount) % 8 = 8 - w.bitCount := by omega
    rw [happ, e3, List.append_assoc]
  · rw [if_neg h0]
    have e0 : w.bitCount = 0 := by omega
    simp [e0, natBits]

/-
## PA16 L1b: bitstream reader ghost algebra (read-consume)

Read-side dual of L1a above, unblocked by P0's conversion of `ensureBits` to well-founded
recursion. `readerBits` is the ghost sequence of unconsumed bits; `ensureBits` preserves it
(buffering moves bits, never consumes them), and a successful `readBits r n` returns exactly
the value whose LSB-first bits are the first `n` elements of the sequence, leaving the rest —
with the reader's operating invariant re-established so reads compose. All rung-1.
-/

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost denotation of a `BitReader`: the unconsumed bit sequence — buffered bits first
    (LSB-first), then the bits of every unread byte in stream order. -/
def readerBits (r : BitReader) : List Bool :=
  natBits r.bitCount r.bitBuf.toNat ++
    (r.bytes.data.toList.drop r.bytePos).flatMap fun b => natBits 8 b.toNat

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Every `natBits` window has exactly its stated width. -/
theorem natBits_length (n : Nat) : ∀ v, (natBits n v).length = n := by
  induction n with
  | zero => intro v; rfl
  | succ n ih => intro v; simp [natBits, ih]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- A value below `2^n` is recovered exactly from its `n`-bit LSB-first window — the
    injectivity half of the ghost encoding, used to transport a written value across the
    writer→reader correspondence. -/
theorem bitsVal_natBits_of_lt : ∀ (n v : Nat), v < 2 ^ n →
    (natBits n v).foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0 = v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    simp [Nat.pow_zero] at hv
    simp [natBits, hv]
  | succ n ih =>
    intro v hv
    have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
    simp only [natBits, List.foldr_cons]
    rw [ih (v / 2) (by rw [hpow] at hv; omega)]
    have hb : (if (v % 2 == 1) = true then 1 else 0) = v % 2 := by
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [hb]
    omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `natBits` windows are injective below `2^n`. -/
theorem natBits_inj {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : natBits n a = natBits n b) : a = b := by
  have h1 := bitsVal_natBits_of_lt n a ha
  have h2 := bitsVal_natBits_of_lt n b hb
  rw [← h1, ← h2, h]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Splits any bit window at position `m`: low `m` bits of the residue, then the shifted
    remainder. `natBits_append` specialized through Euclidean decomposition. -/
theorem natBits_split (m n v : Nat) :
    natBits (m + n) v = natBits m (v % 2 ^ m) ++ natBits n (v / 2 ^ m) := by
  have hdec : v = v % 2 ^ m + (v / 2 ^ m) * 2 ^ m := (Nat.mod_add_div' v (2 ^ m)).symm
  conv => lhs; rw [hdec]
  exact natBits_append n m (v % 2 ^ m) (v / 2 ^ m) (Nat.mod_lt v (Nat.two_pow_pos m))

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Disjoint-sum bound: a value below `2^m` plus a `k`-bit value shifted by `m` stays below
    `2^(m+k)` — the no-`UInt32`-overflow fact both bitstream directions rely on. -/
theorem add_mul_pow_lt {a v m k : Nat} (ha : a < 2 ^ m) (hv : v < 2 ^ k) :
    a + v * 2 ^ m < 2 ^ (m + k) := by
  have h1 : v * 2 ^ m ≤ (2 ^ k - 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 ^ k - 1) * 2 ^ m = 2 ^ k * 2 ^ m - 1 * 2 ^ m := by rw [Nat.sub_mul]
  have h3 : 2 ^ m ≤ 2 ^ k * 2 ^ m := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
  have h4 : 2 ^ (m + k) = 2 ^ k * 2 ^ m := by rw [Nat.pow_add, Nat.mul_comm]
  rw [h4]
  omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- The reader/writer `UInt32` buffer composition in `Nat` terms: given the operating
    invariant and no 32-bit overflow, `buf ||| v <<< cnt` round-trips through `UInt32`
    as the exact sum `buf + v * 2^cnt`. -/
theorem buf_or_shift_toNat {buf v cnt k : Nat} (hbuf : buf < 2 ^ cnt) (hv : v < 2 ^ k)
    (h32 : cnt + k ≤ 32) : ((buf ||| v <<< cnt).toUInt32).toNat = buf + v * 2 ^ cnt := by
  have hlor : buf ||| v <<< cnt = buf + v * 2 ^ cnt := lor_shiftLeft_eq_add hbuf
  have hlt : buf + v * 2 ^ cnt < 2 ^ 32 := by
    have h1 := add_mul_pow_lt hbuf hv
    have h2 : (2 : Nat) ^ (cnt + k) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) h32
    omega
  simp [Nat.toUInt32, hlor, UInt32.toNat_ofNat']
  omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `ensureBits.loop` ghost preservation + invariant maintenance: buffering never changes
    the unconsumed bit sequence, keeps the buffered value inside the buffered count, keeps
    the buffered count below `n + 8`, leaves the byte source untouched, and stops only with
    `n` bits buffered or the source exhausted. Requires `n ≤ 24` (RFC-1951-side truth: the
    largest single read is 13 extra bits; the buffer is 32 bits wide). -/
theorem ensureBits_loop_spec (n : Nat) (hn : n ≤ 24) (cur : BitReader) :
    cur.bitBuf.toNat < 2 ^ cur.bitCount → cur.bitCount < n + 8 →
    readerBits (ensureBits.loop n cur) = readerBits cur ∧
    (ensureBits.loop n cur).bitBuf.toNat < 2 ^ (ensureBits.loop n cur).bitCount ∧
    (ensureBits.loop n cur).bitCount < n + 8 ∧
    (ensureBits.loop n cur).bytes = cur.bytes ∧
    ((ensureBits.loop n cur).bitCount ≥ n ∨
      (ensureBits.loop n cur).bytePos ≥ (ensureBits.loop n cur).bytes.size) := by
  induction cur using ensureBits.loop.induct (n := n) with
  | case1 x hx =>
    intro hinv hcnt
    rw [ensureBits.loop.eq_1, if_pos hx]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
    exact ⟨rfl, hinv, hcnt, rfl, hx⟩
  | case2 x hx nextByte newBuf ih =>
    intro hinv hcnt
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hx
    have hxc : x.bitCount < n := by omega
    have hxp : x.bytePos < x.bytes.size := by omega
    have hbyte : nextByte.toNat < 2 ^ 8 := UInt8.toNat_lt nextByte
    have hnewNat : newBuf.toNat = x.bitBuf.toNat + nextByte.toNat * 2 ^ x.bitCount :=
      buf_or_shift_toNat hinv hbyte (by omega)
    have hinv' : newBuf.toNat < 2 ^ (x.bitCount + 8) := by
      rw [hnewNat]; exact add_mul_pow_lt hinv hbyte
    have ih' := ih hinv' (by show x.bitCount + 8 < n + 8; omega)
    rw [ensureBits.loop.eq_1, if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; omega)]
    refine ⟨?_, ih'.2.1, ih'.2.2.1, ih'.2.2.2.1, ?_⟩
    · rw [ih'.1]
      -- readerBits of the buffered-one-more-byte state equals readerBits x
      show natBits (x.bitCount + 8) newBuf.toNat ++
          (x.bytes.data.toList.drop (x.bytePos + 1)).flatMap (fun b => natBits 8 b.toNat) =
        natBits x.bitCount x.bitBuf.toNat ++
          (x.bytes.data.toList.drop x.bytePos).flatMap (fun b => natBits 8 b.toNat)
      have hlen : x.bytePos < x.bytes.data.toList.length := by
        rw [Array.length_toList]
        exact hxp
      have hdrop : x.bytes.data.toList.drop x.bytePos =
          x.bytes.data.toList[x.bytePos] :: x.bytes.data.toList.drop (x.bytePos + 1) :=
        List.drop_eq_getElem_cons hlen
      have hgetEq : x.bytes.data.toList[x.bytePos]'hlen = nextByte := by
        show x.bytes.data.toList[x.bytePos]'hlen = x.bytes.get! x.bytePos
        rw [ByteArray.get!_eq_getElem x.bytes x.bytePos hxp]
        rw [Array.getElem_toList]
        exact ByteArray.getElem_eq_getElem_data.symm
      rw [hdrop, hgetEq, List.flatMap_cons, hnewNat,
        natBits_append 8 x.bitCount x.bitBuf.toNat nextByte.toNat hinv,
        List.append_assoc]
    · rcases ih'.2.2.2.2 with h | h
      · exact Or.inl h
      · exact Or.inr h

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- L1b, the read-consume law (`docs/PA16_CODEC_SOUNDNESS.md` §4 L1): under the reader's
    operating invariant (buffered value inside the buffered count, fewer than 8 buffered
    bits — `mkBitReader`'s initial state, re-established by every successful read) and the
    format-honest width bound `n ≤ 24`, a reader holding at least `n` unconsumed bits
    successfully reads a value `v < 2^n` whose LSB-first window is exactly the first `n`
    ghost bits, leaving exactly the remaining ghost bits — with the invariant restored. -/
theorem readBits_spec (r : BitReader) (n : Nat)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8)
    (hn : n ≤ 24) (hlen : n ≤ (readerBits r).length) :
    ∃ r' v, readBits r n = .ok (r', v) ∧
      v < 2 ^ n ∧
      natBits n v = (readerBits r).take n ∧
      readerBits r' = (readerBits r).drop n ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hens : ensureBits r n = ensureBits.loop n r := ensureBits.eq_1 r n
  obtain ⟨hbits, einv, ecnt, ebytes, hexit⟩ := ensureBits_loop_spec n hn r hinv (by omega)
  rw [← hens] at hbits einv ecnt ebytes hexit
  -- the ensured reader holds at least n buffered bits
  have hbcnt : n ≤ (ensureBits r n).bitCount := by
    rcases hexit with h | h
    · exact h
    · have hdropnil :
          (ensureBits r n).bytes.data.toList.drop (ensureBits r n).bytePos = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]
        exact h
      have : (readerBits (ensureBits r n)).length = (ensureBits r n).bitCount := by
        simp [readerBits, hdropnil, natBits_length]
      rw [hbits] at this
      omega
  have hdivNat : (((ensureBits r n).bitBuf.toNat >>> n).toUInt32).toNat =
      (ensureBits r n).bitBuf.toNat / 2 ^ n := by
    have hshift : (ensureBits r n).bitBuf.toNat >>> n = (ensureBits r n).bitBuf.toNat / 2 ^ n :=
      Nat.shiftRight_eq_div_pow _ n
    have hlt : (ensureBits r n).bitBuf.toNat / 2 ^ n < 2 ^ 32 := by
      have h1 : (2 : Nat) ^ (ensureBits r n).bitCount ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (ensureBits r n).bitBuf.toNat / 2 ^ n ≤ (ensureBits r n).bitBuf.toNat :=
        Nat.div_le_self _ _
      omega
    simp [Nat.toUInt32, hshift, UInt32.toNat_ofNat']
    omega
  have hsplit := natBits_split n ((ensureBits r n).bitCount - n) (ensureBits r n).bitBuf.toNat
  rw [show n + ((ensureBits r n).bitCount - n) = (ensureBits r n).bitCount by omega] at hsplit
  have hread : readBits r n =
      .ok ({ ensureBits r n with
              bitBuf := ((ensureBits r n).bitBuf.toNat >>> n).toUInt32,
              bitCount := (ensureBits r n).bitCount - n },
        (ensureBits r n).bitBuf.toNat &&& ((1 <<< n) - 1)) := by
    simp only [readBits]
    rw [if_neg (by omega)]
  refine ⟨_, _, hread, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- value bound
    have h1n : (1 : Nat) <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h1n, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos n)
  · -- the value's window is the ghost prefix
    have h1n : (1 : Nat) <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h1n, Nat.and_two_pow_sub_one_eq_mod, ← hbits]
    show natBits n ((ensureBits r n).bitBuf.toNat % 2 ^ n) = (readerBits (ensureBits r n)).take n
    rw [readerBits, hsplit, List.append_assoc]
    rw [List.take_left' (by rw [natBits_length])]
  · -- the rest is the ghost suffix
    rw [← hbits]
    show natBits ((ensureBits r n).bitCount - n)
        (((ensureBits r n).bitBuf.toNat >>> n).toUInt32).toNat ++ _ =
      (readerBits (ensureBits r n)).drop n
    rw [hdivNat, readerBits, hsplit, List.append_assoc]
    rw [List.drop_left' (by rw [natBits_length])]
  · -- invariant: new buffered value inside new count
    show (((ensureBits r n).bitBuf.toNat >>> n).toUInt32).toNat <
      2 ^ ((ensureBits r n).bitCount - n)
    rw [hdivNat]
    have hdecomp : (2 : Nat) ^ (ensureBits r n).bitCount =
        2 ^ ((ensureBits r n).bitCount - n) * 2 ^ n := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
    rw [hdecomp] at einv
    exact einv
  · -- invariant: new count below 8
    show (ensureBits r n).bitCount - n < 8
    omega
  · -- bytes untouched
    show (ensureBits r n).bytes = r.bytes
    exact ebytes

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- `mkBitReader`'s ghost sequence is the byte buffer's bit sequence, and its operating
    invariant holds initially. -/
theorem readerBits_mkBitReader (bs : ByteArray) :
    readerBits (mkBitReader bs) = bytesBits bs ∧
    (mkBitReader bs).bitBuf.toNat < 2 ^ (mkBitReader bs).bitCount ∧
    (mkBitReader bs).bitCount < 8 := by
  refine ⟨?_, by simp [mkBitReader], by simp [mkBitReader]⟩
  simp [readerBits, mkBitReader, bytesBits, natBits]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- L1c, the writer↔reader correspondence: a reader over a flushed writer's bytes sees
    exactly the writer's ghost bit sequence followed by the byte-alignment zero padding —
    the composition point where L1a's write-append meets L1b's read-consume. -/
theorem readerBits_of_flushed (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    readerBits (mkBitReader (flushBitWriter w)) =
      writerBits w ++ List.replicate ((8 - w.bitCount) % 8) false := by
  rw [(readerBits_mkBitReader (flushBitWriter w)).1]
  exact flushBitWriter_bits w hbuf hcnt

/-
## PA16 L2 groundwork: Huffman decode-tree path semantics

`treeWalk` is the computable ghost semantics of a decode tree: follow a bit path from a
node to a leaf. `decodeHuffmanSymbol_spec` proves the general decode law — for ANY table
(fixed or dynamic): if some path through the tree reaches leaf `sym` and the reader's
unconsumed ghost bits start with that path, decoding succeeds with `sym`, consumes exactly
the path, and re-establishes the reader invariant. Per-table facts (which path each
symbol's canonical code takes) then plug in as closed hypotheses.
-/

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Follows a bit path from a decode-tree node; `some sym` iff the path ends exactly on a
    leaf carrying `sym`. -/
def treeWalk : HuffmanNode → List Bool → Option Nat
  | .leaf sym, [] => some sym
  | .branch l _, false :: p =>
    match l with
    | some n => treeWalk n p
    | none => none
  | .branch _ rr, true :: p =>
    match rr with
    | some n => treeWalk n p
    | none => none
  | _, _ => none

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- General Huffman decode law over the tree-path semantics: from any tree node, if the
    reader's ghost bits start with a path that `treeWalk` resolves to `sym`, then
    `decodeHuffmanSymbol.step` succeeds with `sym`, consumes exactly the path, keeps the
    byte source, and re-establishes the reader's operating invariant. -/
theorem decodeHuffmanSymbol_step_spec (path : List Bool) :
    ∀ (node : HuffmanNode) (sym : Nat) (r : BitReader) (rest : List Bool),
      treeWalk node path = some sym →
      readerBits r = path ++ rest →
      r.bitBuf.toNat < 2 ^ r.bitCount → r.bitCount < 8 →
      ∃ r', decodeHuffmanSymbol.step r node = .ok (r', sym) ∧
        readerBits r' = rest ∧
        r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  induction path with
  | nil =>
    intro node sym r rest hwalk hbits hinv hcnt
    match node with
    | .leaf s =>
      simp only [treeWalk, Option.some.injEq] at hwalk
      subst hwalk
      refine ⟨r, ?_, by simpa using hbits, hinv, hcnt, rfl⟩
      rw [decodeHuffmanSymbol.step.eq_def]
    | .branch _ _ => simp [treeWalk] at hwalk
  | cons b p ih =>
    intro node sym r rest hwalk hbits hinv hcnt
    match node with
    | .leaf s => simp [treeWalk] at hwalk
    | .branch l rr =>
      -- one bit is available: readerBits r = b :: (p ++ rest)
      have hlen : 1 ≤ (readerBits r).length := by
        rw [hbits]; simp
      obtain ⟨r1, v, hok, hv, hwin, hdrop, hinv1, hcnt1, hbytes1⟩ :=
        readBits_spec r 1 hinv hcnt (by omega) hlen
      -- the single-bit window determines v from b
      have hwin1 : natBits 1 v = [b] := by
        rw [hwin, hbits]
        rfl
      have hmod : (v % 2 == 1) = b := by
        simpa [natBits] using hwin1
      have hv2 : v < 2 := by
        simpa using hv
      have hdrop' : readerBits r1 = p ++ rest := by
        rw [hdrop, hbits]
        rfl
      rw [decodeHuffmanSymbol.step.eq_def]
      simp only [hok]
      rcases b with _ | _
      · -- b = false: v = 0, go left
        have hv0 : v = 0 := by
          have h' : ¬ v % 2 = 1 := by simpa using hmod
          omega
        subst hv0
        cases l with
        | some nl =>
          simp only [treeWalk] at hwalk
          obtain ⟨r', hstep, hbits', hinv', hcnt', hbytes'⟩ :=
            ih nl sym r1 rest hwalk hdrop' hinv1 hcnt1
          refine ⟨r', ?_, hbits', hinv', hcnt', by rw [hbytes', hbytes1]⟩
          simpa using hstep
        | none => simp [treeWalk] at hwalk
      · -- b = true: v = 1, go right
        have hv1 : v = 1 := by
          have h' : v % 2 = 1 := by simpa using hmod
          omega
        subst hv1
        cases rr with
        | some nr =>
          simp only [treeWalk] at hwalk
          obtain ⟨r', hstep, hbits', hinv', hcnt', hbytes'⟩ :=
            ih nr sym r1 rest hwalk hdrop' hinv1 hcnt1
          refine ⟨r', ?_, hbits', hinv', hcnt', by rw [hbytes', hbytes1]⟩
          simpa using hstep
        | none => simp [treeWalk] at hwalk

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Top-level form of the decode law, phrased over `decodeHuffmanSymbol` and a table. -/
theorem decodeHuffmanSymbol_spec (table : HuffmanTable) (path : List Bool) (sym : Nat)
    (r : BitReader) (rest : List Bool)
    (hwalk : treeWalk table.root path = some sym)
    (hbits : readerBits r = path ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r table = .ok (r', sym) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  rw [decodeHuffmanSymbol]
  exact decodeHuffmanSymbol_step_spec path table.root sym r rest hwalk hbits hinv hcnt

end Stdlib.Zlib

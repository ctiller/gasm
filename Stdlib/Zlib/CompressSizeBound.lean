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

import Stdlib.Zlib.ContainerRoundtrip

/-
## Output-size bounds for `compress` and `zlibCompress`

`compress` cannot be evaluated by the kernel (`List.mergeSort` inside
`packageMergeLengths` is well-founded recursion, and `compressPlan` forces it on every
input), so any fact about a *specific* compressed stream's size must come from a
propositional bound, not `decide`. This file bounds the emitted bit count of both
encoder branches through the ghost `writerBits` characterizations and converts it to a
byte bound: `(zlibCompress data).size <= 6 * data.size + 610`. The PNG chunk layer uses
this to discharge the 4-byte chunk-length precondition of `png_roundtrip_soundness`
without evaluating the compressor.
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Each finished byte contributes exactly 8 ghost bits. -/
theorem bytesBits_length (bs : ByteArray) : (bytesBits bs).length = 8 * bs.size := by
  unfold bytesBits
  have h : ∀ l : List UInt8, (l.flatMap fun b => natBits 8 b.toNat).length = 8 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, natBits_length, ih, List.length_cons]
      omega
  rw [h, Array.length_toList]
  rfl

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Ghost bit count of a writer state. -/
theorem writerBits_length (w : BitWriter) :
    (writerBits w).length = 8 * w.bytes.size + w.bitCount := by
  unfold writerBits
  rw [List.length_append, bytesBits_length, natBits_length]

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Flushing adds at most one padding byte. -/
theorem flushBitWriter_size (w : BitWriter) :
    (flushBitWriter w).size ≤ w.bytes.size + 1 := by
  unfold flushBitWriter
  split
  · rw [ByteArray.size_push]
    omega
  · omega

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Byte count of the flushed stream against the ghost bit count. -/
theorem flushed_size_le_bits (w : BitWriter) :
    8 * (flushBitWriter w).size ≤ (writerBits w).length + 8 := by
  have h1 := flushBitWriter_size w
  have h2 := writerBits_length w
  omega

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Fixed literal/length codes are at most 9 bits. -/
theorem symbolBits_fixedLit_length {sym : Nat} (h : sym < 288) :
    (symbolBits fixedLitLenTable sym).length ≤ 9 := by
  obtain ⟨code, len, hc, _, hlen, _, _⟩ := fixedLit_symbol_spec h
  rw [symbolBits_eq _ _ _ _ hc, natBits_length]
  exact hlen

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Fixed distance codes are at most 9 bits. -/
theorem symbolBits_fixedDist_length {sym : Nat} (h : sym < 32) :
    (symbolBits fixedDistTable sym).length ≤ 9 := by
  obtain ⟨code, len, hc, _, hlen, _, _⟩ := fixedDist_symbol_spec h
  rw [symbolBits_eq _ _ _ _ hc, natBits_length]
  exact hlen

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- One token costs at most 36 bits under the fixed tables. -/
theorem tokenBitsFixed_length (t : LZToken) (hok : tokenRangesOk t) :
    (tokenBitsFixed t).length ≤ 36 := by
  cases t with
  | lit b =>
    show (symbolBits fixedLitLenTable b.toNat).length ≤ 36
    have hb : b.toNat < 288 := by
      have := b.toNat_lt
      omega
    have := symbolBits_fixedLit_length hb
    omega
  | ref len dist =>
    obtain ⟨h3, h258, h1, h32768⟩ := hok
    show (symbolBits fixedLitLenTable (encodeLength len).1 ++
      natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
      symbolBits fixedDistTable (encodeDistance dist).1 ++
      natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2).length ≤ 36
    obtain ⟨_, hLc, hLe, _, _, _⟩ := encodeLength_spec len (by omega) h3
    obtain ⟨hDc, hDe, _, _, _⟩ := encodeDistance_spec' dist h1 h32768
    have hL := symbolBits_fixedLit_length
      (show (encodeLength len).1 < 288 from by omega)
    have hD := symbolBits_fixedDist_length
      (show (encodeDistance dist).1 < 32 from by omega)
    simp only [List.length_append, natBits_length]
    omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A fixed-table token stream costs at most 36 bits per token. -/
theorem tokensBitsFixed_length : ∀ l : List LZToken, (∀ t ∈ l, tokenRangesOk t) →
    (tokensBitsFixed l).length ≤ 36 * l.length := by
  intro l
  induction l with
  | nil => intro _; simp [tokensBitsFixed]
  | cons t ts ih =>
    intro h
    show (tokenBitsFixed t ++ tokensBitsFixed ts).length ≤ _
    rw [List.length_append]
    have h1 := tokenBitsFixed_length t (h t (by simp))
    have h2 := ih (fun t' ht' => h t' (by simp [ht']))
    simp only [List.length_cons]
    omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- One token costs at most 48 bits under 15-bit-bounded dynamic tables. -/
theorem tokenBitsDyn_length (litL distL : Array Nat) (t : LZToken)
    (hok : dynTokenOk litL distL t) : (tokenBitsDyn litL distL t).length ≤ 48 := by
  cases t with
  | lit b =>
    obtain ⟨hpos, hle⟩ := hok
    show (codeBits (canonicalCode litL 15 b.toNat) litL[b.toNat]!).length ≤ 48
    rw [codeBits_length]
    omega
  | ref len dist =>
    obtain ⟨⟨h3, h258, h1, h32768⟩, ⟨hl1, hl2⟩, ⟨hd1, hd2⟩⟩ := hok
    show (codeBits (canonicalCode litL 15 (encodeLength len).1)
        litL[(encodeLength len).1]! ++
      natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
      codeBits (canonicalCode distL 15 (encodeDistance dist).1)
        distL[(encodeDistance dist).1]! ++
      natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2).length ≤ 48
    obtain ⟨_, _, hLe, _, _, _⟩ := encodeLength_spec len (by omega) h3
    obtain ⟨_, hDe, _, _, _⟩ := encodeDistance_spec' dist h1 h32768
    simp only [List.length_append, codeBits_length, natBits_length]
    omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A dynamic-table token stream costs at most 48 bits per token. -/
theorem tokensBitsDyn_length (litL distL : Array Nat) : ∀ l : List LZToken,
    (∀ t ∈ l, dynTokenOk litL distL t) →
    (tokensBitsDyn litL distL l).length ≤ 48 * l.length := by
  intro l
  induction l with
  | nil => intro _; simp [tokensBitsDyn]
  | cons t ts ih =>
    intro h
    show (tokenBitsDyn litL distL t ++ tokensBitsDyn litL distL ts).length ≤ _
    rw [List.length_append]
    have h1 := tokenBitsDyn_length litL distL t (h t (by simp))
    have h2 := ih (fun t' ht' => h t' (by simp [ht']))
    simp only [List.length_cons]
    omega

/- REF: rfc1951#section-3.2.7 -/
/-- The code-length-order header is at most 57 bits. -/
theorem clenHeaderBits_length (plan : DynPlan) (h : plan.hclen ≤ 19) :
    (clenHeaderBits plan).length ≤ 57 := by
  unfold clenHeaderBits
  have hflat : ∀ l : List Nat,
      ((l.flatMap fun i => natBits 3 plan.clenLengths[clenOrder[i]!]!).length) =
        3 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, natBits_length, ih, List.length_cons]
      omega
  rw [hflat, List.length_range]
  omega

/- REF: rfc1951#section-3.2.7 -/
/-- The RLE'd code-length stream costs at most 14 bits per RLE token. -/
theorem rleBitsF_length (cl : Array Nat) : ∀ ts : List (Nat × Nat × Nat),
    (∀ t ∈ ts, t.2.1 ≤ 7 ∧ cl[t.1]! ≤ 7) →
    (rleBitsF cl ts).length ≤ 14 * ts.length := by
  intro ts
  induction ts with
  | nil => intro _; simp [rleBitsF]
  | cons t ts ih =>
    intro h
    show ((codeBits (canonicalCode cl 7 t.1) cl[t.1]! ++ natBits t.2.1 t.2.2) ++
      rleBitsF cl ts).length ≤ _
    rw [List.length_append, List.length_append, codeBits_length, natBits_length]
    have h1 := h t (by simp)
    have h2 := ih (fun t' ht' => h t' (by simp [ht']))
    simp only [List.length_cons]
    omega

/- REF: rfc1951#section-3.2.7 -/
/-- Every RLE token expands at least one code length, so the stream has at most as many
    tokens as there are lengths to transmit. -/
theorem rleOk_count : ∀ (ts : List (Nat × Nat × Nat)) (done full : List Nat),
    rleOk ts done full → ts.length + done.length ≤ full.length := by
  intro ts
  induction ts with
  | nil =>
    intro done full hok
    rw [show done = full from hok]
    simp
  | cons hd ts ih =>
    intro done full hok
    obtain ⟨sym, eb, ev⟩ := hd
    rcases hok with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
      (have hc := ih _ _ h
       simp only [List.length_append, List.length_replicate, List.length_cons,
         List.length_nil] at hc ⊢
       omega)

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- The tokenizer emits at most one token per unit of fuel. -/
theorem tokenizeAux_length (data : ByteArray) : ∀ fuel pos acc,
    (tokenizeAux data fuel pos acc).size ≤ acc.size + fuel := by
  intro fuel
  induction fuel with
  | zero => intro pos acc; simp [tokenizeAux]
  | succ fuel ih =>
    intro pos acc
    simp only [tokenizeAux]
    split
    · split
      · refine Nat.le_trans (ih _ _) ?_
        rw [Array.size_push]
        omega
      · refine Nat.le_trans (ih _ _) ?_
        rw [Array.size_push]
        omega
    · omega

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- The tokenizer emits at most one token per input byte. -/
theorem tokenize_length (data : ByteArray) : (tokenize data).size ≤ data.size := by
  have h := tokenizeAux_length data data.size 0 #[]
  have h0 : (#[] : Array LZToken).size = 0 := rfl
  unfold tokenize
  omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bit count of the fixed-Huffman branch. -/
theorem emitFixedBlock_length (tokens : Array LZToken)
    (hok : ∀ t ∈ tokens.toList, tokenRangesOk t) :
    (writerBits (emitFixedBlock tokens)).length ≤ 36 * tokens.toList.length + 12 := by
  have hw := writerBits_emitFixedBlock tokens hok
  rw [hw.1]
  simp only [List.length_cons, List.length_append]
  have h1 := tokensBitsFixed_length tokens.toList hok
  have h2 := symbolBits_fixedLit_length (show 256 < 288 from by omega)
  omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bit count of the dynamic-Huffman branch: header at most 4513 bits, tokens at
    most 48 bits each. -/
theorem emitDynamicBlock_length (tokens : Array LZToken)
    (hwf : tokensWF tokens.toList 0) :
    (writerBits (emitDynamicBlock (buildDynPlan tokens) tokens)).length ≤
      48 * tokens.toList.length + 4600 := by
  have hok : ∀ t ∈ tokens.toList, tokenRangesOk t := tokensWF_rangesOk _ 0 hwf
  -- ------------------------------------------------------------------
  -- Plan facts
  -- ------------------------------------------------------------------
  have tfs := tokenFrequencies_spec tokens hok
  obtain ⟨htf1, htf2, htf256, htflit, htfref⟩ := tfs
  -- literal/length side
  have plsL := padFrequencies_spec (tokenFrequencies tokens).1 (by omega)
  have hpadszL : (padFrequencies (tokenFrequencies tokens).1).size
      = (tokenFrequencies tokens).1.size := plsL.1
  have pmL := packageMergeLengths_spec (padFrequencies (tokenFrequencies tokens).1) 15
    (by omega)
    (by rw [hpadszL]; exact plsL.2.2)
    (by
      have h1 := List.countP_le_length
        (p := fun s => decide (0 < (padFrequencies (tokenFrequencies tokens).1)[s]!))
        (l := List.range (padFrequencies (tokenFrequencies tokens).1).size)
      rw [List.length_range] at h1
      have h2 : (padFrequencies (tokenFrequencies tokens).1).size = 286 := by
        rw [hpadszL, htf1]
      have h3 : (2 : Nat) ^ (15 - 1) = 16384 := by decide
      omega)
  have hlitL : (buildDynPlan tokens).litLengths =
      packageMergeLengths (padFrequencies (tokenFrequencies tokens).1) 15 :=
    buildDynPlan_litLengths tokens
  have hlitsize : (buildDynPlan tokens).litLengths.size = 286 := by
    rw [hlitL, pmL.1, hpadszL, htf1]
  have hlit15 : ∀ i : Nat, (buildDynPlan tokens).litLengths[i]! ≤ 15 := by
    intro i
    by_cases hi : i < (buildDynPlan tokens).litLengths.size
    · rw [hlitL]
      apply pmL.2.2.1
      rw [← pmL.1, ← hlitL]
      omega
    · rw [getElem!_oob _ _ hi]
      show (0 : Nat) ≤ 15
      omega
  have hkl : kraftOk (buildDynPlan tokens).litLengths 15 := by
    rw [hlitL]
    apply kraftOk_of_symbol_sum
    · intro s hs
      rw [← hlitL]
      exact hlit15 s
    · rw [pmL.1]
      exact pmL.2.2.2.2
  have hlitcov : ∀ s : Nat, s < 286 → 0 < (tokenFrequencies tokens).1[s]! →
      0 < (buildDynPlan tokens).litLengths[s]! := by
    intro s hs hpos
    rw [hlitL]
    have hs' : s < (padFrequencies (tokenFrequencies tokens).1).size := by
      rw [hpadszL, htf1]
      omega
    apply pmL.2.1 s hs'
    have := plsL.2.1 s
    omega
  -- distance side
  have plsD := padFrequencies_spec (tokenFrequencies tokens).2 (by omega)
  have hpadszD : (padFrequencies (tokenFrequencies tokens).2).size
      = (tokenFrequencies tokens).2.size := plsD.1
  have pmD := packageMergeLengths_spec (padFrequencies (tokenFrequencies tokens).2) 15
    (by omega)
    (by rw [hpadszD]; exact plsD.2.2)
    (by
      have h1 := List.countP_le_length
        (p := fun s => decide (0 < (padFrequencies (tokenFrequencies tokens).2)[s]!))
        (l := List.range (padFrequencies (tokenFrequencies tokens).2).size)
      rw [List.length_range] at h1
      have h2 : (padFrequencies (tokenFrequencies tokens).2).size = 30 := by
        rw [hpadszD, htf2]
      have h3 : (2 : Nat) ^ (15 - 1) = 16384 := by decide
      omega)
  have hdistL : (buildDynPlan tokens).distLengths =
      packageMergeLengths (padFrequencies (tokenFrequencies tokens).2) 15 :=
    buildDynPlan_distLengths tokens
  have hdistsize : (buildDynPlan tokens).distLengths.size = 30 := by
    rw [hdistL, pmD.1, hpadszD, htf2]
  have hdist15 : ∀ i : Nat, (buildDynPlan tokens).distLengths[i]! ≤ 15 := by
    intro i
    by_cases hi : i < (buildDynPlan tokens).distLengths.size
    · rw [hdistL]
      apply pmD.2.2.1
      rw [← pmD.1, ← hdistL]
      omega
    · rw [getElem!_oob _ _ hi]
      show (0 : Nat) ≤ 15
      omega
  have hkd : kraftOk (buildDynPlan tokens).distLengths 15 := by
    rw [hdistL]
    apply kraftOk_of_symbol_sum
    · intro s hs
      rw [← hdistL]
      exact hdist15 s
    · rw [pmD.1]
      exact pmD.2.2.2.2
  have hdistcov : ∀ s : Nat, s < 30 → 0 < (tokenFrequencies tokens).2[s]! →
      0 < (buildDynPlan tokens).distLengths[s]! := by
    intro s hs hpos
    rw [hdistL]
    have hs' : s < (padFrequencies (tokenFrequencies tokens).2).size := by
      rw [hpadszD, htf2]
      omega
    apply pmD.2.1 s hs'
    have := plsD.2.1 s
    omega
  -- HLIT / HDIST and their trims
  have htrimL := trimmedSize_spec (buildDynPlan tokens).litLengths 257
  have hhlit : 257 ≤ (buildDynPlan tokens).hlit ∧ (buildDynPlan tokens).hlit ≤ 286 := by
    rw [buildDynPlan_hlit]
    refine ⟨htrimL.1, ?_⟩
    have := htrimL.2.1
    rw [hlitsize] at this
    omega
  have hlitzero : ∀ i : Nat, (buildDynPlan tokens).hlit ≤ i →
      (buildDynPlan tokens).litLengths[i]! = 0 := by
    intro i hi
    rw [buildDynPlan_hlit] at hi
    exact htrimL.2.2 i hi
  have htrimD := trimmedSize_spec (buildDynPlan tokens).distLengths 1
  have hhdist : 1 ≤ (buildDynPlan tokens).hdist ∧ (buildDynPlan tokens).hdist ≤ 30 := by
    rw [buildDynPlan_hdist]
    refine ⟨htrimD.1, ?_⟩
    have := htrimD.2.1
    rw [hdistsize] at this
    omega
  have hdistzero : ∀ i : Nat, (buildDynPlan tokens).hdist ≤ i →
      (buildDynPlan tokens).distLengths[i]! = 0 := by
    intro i hi
    rw [buildDynPlan_hdist] at hi
    exact htrimD.2.2 i hi
  -- the RLE stream and its certificate
  have hfullval : ∀ v ∈ ((buildDynPlan tokens).litLengths.toList.take
      (buildDynPlan tokens).hlit ++ (buildDynPlan tokens).distLengths.toList.take
      (buildDynPlan tokens).hdist), v ≤ 15 := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · have hmem := List.mem_of_mem_take h
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hmem
      rw [← hie]
      have : (buildDynPlan tokens).litLengths.toList[i] =
          (buildDynPlan tokens).litLengths.toList.getD i 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        rfl
      rw [this, ← getElem!_eq_toList_getD]
      exact hlit15 i
    · have hmem := List.mem_of_mem_take h
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hmem
      rw [← hie]
      have : (buildDynPlan tokens).distLengths.toList[i] =
          (buildDynPlan tokens).distLengths.toList.getD i 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        rfl
      rw [this, ← getElem!_eq_toList_getD]
      exact hdist15 i
  have hrleok : rleOk (buildDynPlan tokens).rleTokens []
      ((buildDynPlan tokens).litLengths.toList.take (buildDynPlan tokens).hlit ++
       (buildDynPlan tokens).distLengths.toList.take (buildDynPlan tokens).hdist) := by
    rw [buildDynPlan_rleTokens]
    exact rleCodeLengths_ok _ hfullval
  have hrlebounds := rleOk_bounds _ _ _ hrleok
  -- the code-length code
  have hclL : (buildDynPlan tokens).clenLengths =
      packageMergeLengths (padFrequencies (clenFreqF (buildDynPlan tokens).rleTokens)) 7 :=
    buildDynPlan_clenLengths tokens
  have hcfsize := clenFreqF_size (buildDynPlan tokens).rleTokens
  have plsC := padFrequencies_spec (clenFreqF (buildDynPlan tokens).rleTokens)
    (by rw [hcfsize]; omega)
  have hpadszC : (padFrequencies (clenFreqF (buildDynPlan tokens).rleTokens)).size
      = (clenFreqF (buildDynPlan tokens).rleTokens).size := plsC.1
  have pmC := packageMergeLengths_spec
    (padFrequencies (clenFreqF (buildDynPlan tokens).rleTokens)) 7 (by omega)
    (by rw [hpadszC]; exact plsC.2.2)
    (by
      have h1 := List.countP_le_length
        (p := fun s => decide (0 < (padFrequencies (clenFreqF
          (buildDynPlan tokens).rleTokens))[s]!))
        (l := List.range (padFrequencies (clenFreqF
          (buildDynPlan tokens).rleTokens)).size)
      rw [List.length_range] at h1
      have h2 : (padFrequencies (clenFreqF (buildDynPlan tokens).rleTokens)).size = 19 := by
        rw [hpadszC, hcfsize]
      have h3 : (2 : Nat) ^ (7 - 1) = 64 := by decide
      omega)
  have hclsize : (buildDynPlan tokens).clenLengths.size = 19 := by
    rw [hclL, pmC.1, hpadszC, hcfsize]
  have hcl7 : ∀ i : Nat, (buildDynPlan tokens).clenLengths[i]! ≤ 7 := by
    intro i
    by_cases hi : i < (buildDynPlan tokens).clenLengths.size
    · rw [hclL]
      apply pmC.2.2.1
      rw [← pmC.1, ← hclL]
      omega
    · rw [getElem!_oob _ _ hi]
      show (0 : Nat) ≤ 7
      omega
  have hkc : kraftOk (buildDynPlan tokens).clenLengths 7 := by
    rw [hclL]
    apply kraftOk_of_symbol_sum
    · intro s hs
      rw [← hclL]
      exact hcl7 s
    · rw [pmC.1]
      exact pmC.2.2.2.2
  have hrlesyms : ∀ t ∈ (buildDynPlan tokens).rleTokens,
      0 < (buildDynPlan tokens).clenLengths[t.1]! ∧
      (buildDynPlan tokens).clenLengths[t.1]! ≤ 7 := by
    intro t ht
    refine ⟨?_, hcl7 t.1⟩
    have h19 : t.1 < 19 := by
      have := (hrlebounds t ht).1
      omega
    have hcf := clenFreqF_covers (buildDynPlan tokens).rleTokens
      (fun t' ht' => by have := (hrlebounds t' ht').1; omega) t ht
    rw [hclL]
    have ht19 : t.1 < (padFrequencies (clenFreqF (buildDynPlan tokens).rleTokens)).size := by
      rw [hpadszC, hcfsize]
      omega
    apply pmC.2.1 t.1 ht19
    have := plsC.2.1 t.1
    omega
  have hhclen := buildDynPlan_hclen tokens
  have hhcb := hclenF_bounds (buildDynPlan tokens).clenLengths
  -- per-token coverage
  have htoks : ∀ t ∈ tokens.toList,
      dynTokenOk (buildDynPlan tokens).litLengths (buildDynPlan tokens).distLengths t := by
    intro t ht
    cases t with
    | lit b =>
      show 0 < (buildDynPlan tokens).litLengths[b.toNat]! ∧
        (buildDynPlan tokens).litLengths[b.toNat]! ≤ 15
      have hb : b.toNat < 286 := by
        have := b.toNat_lt
        omega
      exact ⟨hlitcov b.toNat hb (htflit b ht), hlit15 _⟩
    | ref len dist =>
      have hr := hok _ ht
      obtain ⟨h3, h258, h1d, h32768⟩ := hr
      have hL := encodeLength_spec len (by omega) h3
      have hD := encodeDistance_spec' dist h1d h32768
      have hcov := htfref len dist ht
      exact ⟨⟨h3, h258, h1d, h32768⟩,
        ⟨hlitcov _ (by omega) hcov.1, hlit15 _⟩,
        ⟨hdistcov _ (by omega) hcov.2, hdist15 _⟩⟩
  have heob : 0 < (buildDynPlan tokens).litLengths[256]! ∧
      (buildDynPlan tokens).litLengths[256]! ≤ 15 :=
    ⟨hlitcov 256 (by omega) htf256, hlit15 _⟩
  -- ------------------------------------------------------------------
  -- Writer side
  -- ------------------------------------------------------------------
  have hw := writerBits_emitDynamicBlock (buildDynPlan tokens) tokens hkc hkl hkd
    ⟨hhlit.1, by omega⟩ ⟨hhdist.1, by omega⟩ (by rw [hhclen]; exact ⟨hhcb.1, hhcb.2⟩)
    (fun i _ => by have := hcl7 clenOrder[i]!; omega)
    (fun t ht => ⟨(hrlebounds t ht).2.2, (hrlebounds t ht).2.1, hrlesyms t ht⟩)
    htoks heob
  rw [hw.1]
  simp only [List.length_append, List.length_cons, List.length_nil, natBits_length,
    codeBits_length]
  have hch : (clenHeaderBits (buildDynPlan tokens)).length ≤ 57 :=
    clenHeaderBits_length _ (by rw [hhclen]; exact hhcb.2)
  have hrlecount : (buildDynPlan tokens).rleTokens.length ≤ 316 := by
    have hc := rleOk_count _ _ _ hrleok
    have hlt : (buildDynPlan tokens).litLengths.toList.length = 286 := by
      rw [Array.length_toList, hlitsize]
    have hdt : (buildDynPlan tokens).distLengths.toList.length = 30 := by
      rw [Array.length_toList, hdistsize]
    simp only [List.length_append, List.length_take, List.length_nil, hlt, hdt] at hc
    have m1 : min (buildDynPlan tokens).hlit 286 ≤ 286 := Nat.min_le_right _ _
    have m2 : min (buildDynPlan tokens).hdist 30 ≤ 30 := Nat.min_le_right _ _
    omega
  have hrb := rleBitsF_length (buildDynPlan tokens).clenLengths
    (buildDynPlan tokens).rleTokens
    (fun t ht => ⟨(hrlebounds t ht).2.1, hcl7 t.1⟩)
  have htb := tokensBitsDyn_length _ _ tokens.toList htoks
  have heobl : (buildDynPlan tokens).litLengths[256]! ≤ 15 := heob.2
  omega

/- REF: docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951 -/
/-- **Compressor output-size bound**: whichever branch the exact bit-cost comparison
    selects, the DEFLATE stream is at most `6 * |data| + 600` bytes. Propositional -- the
    kernel cannot evaluate `compress` (the `List.mergeSort` in `packageMergeLengths` is
    well-founded recursion), so this is the only route to size facts about concrete
    compressed streams. -/
theorem compress_size_bound (data : ByteArray) :
    (compress data).size ≤ 6 * data.size + 600 := by
  have hwf := tokenize_wf data
  have hok := tokensWF_rangesOk _ 0 hwf
  have htl : (tokenize data).toList.length ≤ data.size := by
    rw [Array.length_toList]
    exact tokenize_length data
  unfold compress compressPlan
  dsimp only
  split
  · dsimp only
    have hb := emitDynamicBlock_length (tokenize data) hwf
    have hf := flushed_size_le_bits
      (emitDynamicBlock (buildDynPlan (tokenize data)) (tokenize data))
    omega
  · dsimp only
    have hb := emitFixedBlock_length (tokenize data) hok
    have hf := flushed_size_le_bits (emitFixedBlock (tokenize data))
    omega

/- REF: docs/STDLIB_ZLIB.md#5-zlib-container-rfc-1950 -/
/-- **ZLIB container output-size bound**: header and checksum add six bytes. -/
theorem zlibCompress_size_bound (data : ByteArray) :
    (zlibCompress data).size ≤ 6 * data.size + 610 := by
  have h1 := (zlibCompress_spec data).1
  have h2 := compress_size_bound data
  omega

end Stdlib.Zlib

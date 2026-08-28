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
import Stdlib.Zlib.DynamicBlockSpec

/-
## PA16 dynamic branch, the roundtrip itself: the emitted dynamic block's ghost bits, the
## decoder's reconstruction of them, and `deflate_roundtrip_soundness`.
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bits of the HCLEN-permuted code-length-length header. -/
def clenHeaderBits (plan : DynPlan) : List Bool :=
  (List.range plan.hclen).flatMap (fun i => natBits 3 plan.clenLengths[clenOrder[i]!]!)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bits of the RLE'd code-length stream under the code-length code. -/
def rleBitsF (cl : Array Nat) (ts : List (Nat × Nat × Nat)) : List Bool :=
  ts.flatMap (fun t => codeBits (canonicalCode cl 7 t.1) cl[t.1]! ++ natBits t.2.1 t.2.2)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bits one token contributes under the dynamic tables. -/
def tokenBitsDyn (litL distL : Array Nat) : LZToken → List Bool
  | .lit b => codeBits (canonicalCode litL 15 b.toNat) litL[b.toNat]!
  | .ref len dist =>
      codeBits (canonicalCode litL 15 (encodeLength len).1) litL[(encodeLength len).1]! ++
      natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
      codeBits (canonicalCode distL 15 (encodeDistance dist).1) distL[(encodeDistance dist).1]! ++
      natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Ghost bits of a token list under the dynamic tables. -/
def tokensBitsDyn (litL distL : Array Nat) : List LZToken → List Bool
  | [] => []
  | t :: ts => tokenBitsDyn litL distL t ++ tokensBitsDyn litL distL ts

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- What one token needs of the dynamic tables: RFC ranges and coded symbols. -/
def dynTokenOk (litL distL : Array Nat) : LZToken → Prop
  | .lit b => 0 < litL[b.toNat]! ∧ litL[b.toNat]! ≤ 15
  | .ref len dist =>
      (3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
      (0 < litL[(encodeLength len).1]! ∧ litL[(encodeLength len).1]! ≤ 15) ∧
      (0 < distL[(encodeDistance dist).1]! ∧ distL[(encodeDistance dist).1]! ≤ 15)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting the permuted 3-bit code-length lengths appends their ghost windows. -/
theorem writerBits_clenFold (cl : Array Nat) :
    ∀ (l : List Nat) (w : BitWriter),
    (∀ i ∈ l, cl[clenOrder[i]!]! < 8) →
    w.bitBuf.toNat < 2 ^ w.bitCount → w.bitCount < 8 →
    writerBits (l.foldl (fun w i => writeBits w cl[clenOrder[i]!]! 3) w) =
      writerBits w ++ l.flatMap (fun i => natBits 3 cl[clenOrder[i]!]!) ∧
    (l.foldl (fun w i => writeBits w cl[clenOrder[i]!]! 3) w).bitCount < 8 ∧
    (l.foldl (fun w i => writeBits w cl[clenOrder[i]!]! 3) w).bitBuf.toNat <
      2 ^ (l.foldl (fun w i => writeBits w cl[clenOrder[i]!]! 3) w).bitCount := by
  intro l
  induction l with
  | nil =>
    intro w _ hbuf hcnt
    exact ⟨by simp, hcnt, hbuf⟩
  | cons i l ih =>
    intro w hall hbuf hcnt
    have hstep := writerBits_writeBits w cl[clenOrder[i]!]! 3 hbuf
      (by have := hall i (by simp); omega) (by omega)
    have hrec := ih (writeBits w cl[clenOrder[i]!]! 3)
      (fun j hj => hall j (by simp [hj])) hstep.2.2 hstep.2.1
    rw [List.foldl_cons]
    refine ⟨?_, hrec.2.1, hrec.2.2⟩
    rw [hrec.1, hstep.1, List.flatMap_cons, List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting one RLE token appends its code path and extra window. -/
theorem writerBits_rleToken (cl : Array Nat) (hkc : kraftOk cl 7)
    (t : Nat × Nat × Nat) (hev : t.2.2 < 2 ^ t.2.1) (heb : t.2.1 ≤ 7)
    (hlen : 0 < cl[t.1]!) (hle : cl[t.1]! ≤ 7) (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (if t.2.1 > 0 then
        writeBits (emitHuffSymbol w (buildHuffmanTable cl 7) t.1) t.2.2 t.2.1
      else emitHuffSymbol w (buildHuffmanTable cl 7) t.1) =
      writerBits w ++ (codeBits (canonicalCode cl 7 t.1) cl[t.1]! ++ natBits t.2.1 t.2.2) ∧
    (if t.2.1 > 0 then
        writeBits (emitHuffSymbol w (buildHuffmanTable cl 7) t.1) t.2.2 t.2.1
      else emitHuffSymbol w (buildHuffmanTable cl 7) t.1).bitCount < 8 ∧
    (if t.2.1 > 0 then
        writeBits (emitHuffSymbol w (buildHuffmanTable cl 7) t.1) t.2.2 t.2.1
      else emitHuffSymbol w (buildHuffmanTable cl 7) t.1).bitBuf.toNat <
      2 ^ (if t.2.1 > 0 then
        writeBits (emitHuffSymbol w (buildHuffmanTable cl 7) t.1) t.2.2 t.2.1
      else emitHuffSymbol w (buildHuffmanTable cl 7) t.1).bitCount := by
  have h1 := writerBits_emitHuffSymbol_canonical cl 7 (by omega) hkc hlen hle w hbuf hcnt
  have h2 := writerBits_writeExtra (emitHuffSymbol w (buildHuffmanTable cl 7) t.1)
    t.2.2 t.2.1 hev (by omega) h1.2.2 h1.2.1
  refine ⟨?_, h2.2.1, h2.2.2⟩
  rw [h2.1, h1.1, List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting the RLE stream appends its ghost bits. -/
theorem writerBits_rleFold (cl : Array Nat) (hkc : kraftOk cl 7) :
    ∀ (ts : List (Nat × Nat × Nat)) (w : BitWriter),
    (∀ t ∈ ts, t.2.2 < 2 ^ t.2.1 ∧ t.2.1 ≤ 7 ∧ 0 < cl[t.1]! ∧ cl[t.1]! ≤ 7) →
    w.bitBuf.toNat < 2 ^ w.bitCount → w.bitCount < 8 →
    writerBits (ts.foldl (fun w t =>
        let w' := emitHuffSymbol w (buildHuffmanTable cl 7) t.1
        if t.2.1 > 0 then writeBits w' t.2.2 t.2.1 else w') w) =
      writerBits w ++ rleBitsF cl ts ∧
    (ts.foldl (fun w t =>
        let w' := emitHuffSymbol w (buildHuffmanTable cl 7) t.1
        if t.2.1 > 0 then writeBits w' t.2.2 t.2.1 else w') w).bitCount < 8 ∧
    (ts.foldl (fun w t =>
        let w' := emitHuffSymbol w (buildHuffmanTable cl 7) t.1
        if t.2.1 > 0 then writeBits w' t.2.2 t.2.1 else w') w).bitBuf.toNat <
      2 ^ (ts.foldl (fun w t =>
        let w' := emitHuffSymbol w (buildHuffmanTable cl 7) t.1
        if t.2.1 > 0 then writeBits w' t.2.2 t.2.1 else w') w).bitCount := by
  intro ts
  induction ts with
  | nil =>
    intro w _ hbuf hcnt
    refine ⟨by simp [rleBitsF], hcnt, hbuf⟩
  | cons t ts ih =>
    intro w hall hbuf hcnt
    have ht := hall t (by simp)
    have hstep := writerBits_rleToken cl hkc t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 w hbuf hcnt
    rw [List.foldl_cons]
    have hrec := ih _ (fun t' ht' => hall t' (by simp [ht'])) hstep.2.2 hstep.2.1
    refine ⟨?_, hrec.2.1, hrec.2.2⟩
    rw [hrec.1, hstep.1]
    show _ = writerBits w ++ rleBitsF cl (t :: ts)
    unfold rleBitsF
    rw [List.flatMap_cons, List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting one range-valid, coded token under the dynamic tables appends its ghost bits. -/
theorem writerBits_emitToken_dyn (litL distL : Array Nat)
    (hkl : kraftOk litL 15) (hkd : kraftOk distL 15) (t : LZToken)
    (hok : dynTokenOk litL distL t) (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15) w t) =
      writerBits w ++ tokenBitsDyn litL distL t ∧
    (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15) w t).bitCount < 8 ∧
    (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15) w t).bitBuf.toNat <
      2 ^ (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15) w t).bitCount := by
  cases t with
  | lit b =>
    have h := writerBits_emitHuffSymbol_canonical litL 15 (by omega) hkl hok.1 hok.2 w hbuf hcnt
    exact ⟨h.1, h.2.1, h.2.2⟩
  | ref len dist =>
    obtain ⟨⟨h3, h258, h1d, h32768⟩, hlit, hdist⟩ := hok
    have hL := encodeLength_spec len (by omega) h3
    have hD := encodeDistance_spec' dist h1d h32768
    have s1 := writerBits_emitHuffSymbol_canonical litL 15 (by omega) hkl hlit.1 hlit.2
      w hbuf hcnt
    have s2 := writerBits_writeExtra (emitHuffSymbol w (buildHuffmanTable litL 15)
      (encodeLength len).1) (encodeLength len).2.2 (encodeLength len).2.1
      hL.2.2.2.1 (by omega) s1.2.2 s1.2.1
    have s3 := writerBits_emitHuffSymbol_canonical distL 15 (by omega) hkd hdist.1 hdist.2
      _ s2.2.2 s2.2.1
    have s4 := writerBits_writeExtra _ (encodeDistance dist).2.2 (encodeDistance dist).2.1
      hD.2.2.1 (by omega) s3.2.2 s3.2.1
    refine ⟨?_, s4.2.1, s4.2.2⟩
    show writerBits _ = _
    rw [show emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15) w
        (.ref len dist) =
      (if (encodeDistance dist).2.1 > 0 then
        writeBits
          (emitHuffSymbol
            (if (encodeLength len).2.1 > 0 then
              writeBits (emitHuffSymbol w (buildHuffmanTable litL 15) (encodeLength len).1)
                (encodeLength len).2.2 (encodeLength len).2.1
             else emitHuffSymbol w (buildHuffmanTable litL 15) (encodeLength len).1)
            (buildHuffmanTable distL 15) (encodeDistance dist).1)
          (encodeDistance dist).2.2 (encodeDistance dist).2.1
       else
        emitHuffSymbol
          (if (encodeLength len).2.1 > 0 then
            writeBits (emitHuffSymbol w (buildHuffmanTable litL 15) (encodeLength len).1)
              (encodeLength len).2.2 (encodeLength len).2.1
           else emitHuffSymbol w (buildHuffmanTable litL 15) (encodeLength len).1)
          (buildHuffmanTable distL 15) (encodeDistance dist).1) from rfl]
    rw [s4.1, s3.1, s2.1, s1.1]
    show _ = writerBits w ++ tokenBitsDyn litL distL (.ref len dist)
    unfold tokenBitsDyn
    simp [List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Emitting a coded token list under the dynamic tables. -/
theorem writerBits_foldl_emitToken_dyn (litL distL : Array Nat)
    (hkl : kraftOk litL 15) (hkd : kraftOk distL 15) :
    ∀ (ts : List LZToken) (w : BitWriter),
    (∀ t ∈ ts, dynTokenOk litL distL t) →
    w.bitBuf.toNat < 2 ^ w.bitCount → w.bitCount < 8 →
    writerBits (ts.foldl (emitToken (buildHuffmanTable litL 15)
        (buildHuffmanTable distL 15)) w) =
      writerBits w ++ tokensBitsDyn litL distL ts ∧
    (ts.foldl (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15)) w).bitCount < 8 ∧
    (ts.foldl (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15)) w).bitBuf.toNat <
      2 ^ (ts.foldl (emitToken (buildHuffmanTable litL 15) (buildHuffmanTable distL 15)) w).bitCount := by
  intro ts
  induction ts with
  | nil =>
    intro w _ hbuf hcnt
    exact ⟨by simp [tokensBitsDyn], hcnt, hbuf⟩
  | cons t ts ih =>
    intro w hall hbuf hcnt
    have hstep := writerBits_emitToken_dyn litL distL hkl hkd t (hall t (by simp)) w hbuf hcnt
    have hrec := ih _ (fun t' ht' => hall t' (by simp [ht'])) hstep.2.2 hstep.2.1
    rw [List.foldl_cons]
    refine ⟨?_, hrec.2.1, hrec.2.2⟩
    rw [hrec.1, hstep.1]
    show _ = writerBits w ++ (tokenBitsDyn litL distL t ++ tokensBitsDyn litL distL ts)
    simp [List.append_assoc]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **The dynamic block's ghost bits**: `emitDynamicBlock` writes exactly the 3 header
    bits `BFINAL=1, BTYPE=10`, the three counts, the permuted 3-bit code-length lengths,
    the RLE stream, the token payload, and the end-of-block code. -/
theorem writerBits_emitDynamicBlock (plan : DynPlan) (tokens : Array LZToken)
    (hkc : kraftOk plan.clenLengths 7) (hkl : kraftOk plan.litLengths 15)
    (hkd : kraftOk plan.distLengths 15)
    (hhlit : 257 ≤ plan.hlit ∧ plan.hlit ≤ 288)
    (hhdist : 1 ≤ plan.hdist ∧ plan.hdist ≤ 32)
    (hhclen : 4 ≤ plan.hclen ∧ plan.hclen ≤ 19)
    (hclens : ∀ i, i < plan.hclen → plan.clenLengths[clenOrder[i]!]! < 8)
    (hrle : ∀ t ∈ plan.rleTokens, t.2.2 < 2 ^ t.2.1 ∧ t.2.1 ≤ 7 ∧
      0 < plan.clenLengths[t.1]! ∧ plan.clenLengths[t.1]! ≤ 7)
    (htoks : ∀ t ∈ tokens.toList, dynTokenOk plan.litLengths plan.distLengths t)
    (heob : 0 < plan.litLengths[256]! ∧ plan.litLengths[256]! ≤ 15) :
    writerBits (emitDynamicBlock plan tokens) =
      [true, false, true] ++ natBits 5 (plan.hlit - 257) ++ natBits 5 (plan.hdist - 1) ++
      natBits 4 (plan.hclen - 4) ++ clenHeaderBits plan ++
      rleBitsF plan.clenLengths plan.rleTokens ++
      tokensBitsDyn plan.litLengths plan.distLengths tokens.toList ++
      codeBits (canonicalCode plan.litLengths 15 256) plan.litLengths[256]! ∧
    (emitDynamicBlock plan tokens).bitCount < 8 ∧
    (emitDynamicBlock plan tokens).bitBuf.toNat < 2 ^ (emitDynamicBlock plan tokens).bitCount := by
  have he := writerBits_empty
  have h1 := writerBits_writeBits ({} : BitWriter) 1 1 he.2.1 (by omega) (by simp)
  have h2 := writerBits_writeBits (writeBits {} 1 1) 2 2 h1.2.2 (by omega) (by omega)
  have h3 := writerBits_writeBits _ (plan.hlit - 257) 5 h2.2.2
    (by show plan.hlit - 257 < 2 ^ 5; omega) (by omega)
  have h4 := writerBits_writeBits _ (plan.hdist - 1) 5 h3.2.2
    (by show plan.hdist - 1 < 2 ^ 5; omega) (by omega)
  have h5 := writerBits_writeBits _ (plan.hclen - 4) 4 h4.2.2
    (by show plan.hclen - 4 < 2 ^ 4; omega) (by omega)
  have h6 := writerBits_clenFold plan.clenLengths (List.range plan.hclen) _
    (fun i hi => hclens i (List.mem_range.mp hi)) h5.2.2 h5.2.1
  have h7 := writerBits_rleFold plan.clenLengths hkc plan.rleTokens _ hrle h6.2.2 h6.2.1
  -- the token payload plus end-of-block
  have h8 := writerBits_foldl_emitToken_dyn plan.litLengths plan.distLengths hkl hkd
    tokens.toList _ htoks h7.2.2 h7.2.1
  have h9 := writerBits_emitHuffSymbol_canonical plan.litLengths 15 (by omega) hkl
    heob.1 heob.2 _ h8.2.2 h8.2.1
  have hfold : ∀ w, emitTokens (buildHuffmanTable plan.litLengths 15)
      (buildHuffmanTable plan.distLengths 15) w tokens =
      emitHuffSymbol (tokens.toList.foldl (emitToken (buildHuffmanTable plan.litLengths 15)
        (buildHuffmanTable plan.distLengths 15)) w) (buildHuffmanTable plan.litLengths 15) 256 := by
    intro w
    unfold emitTokens
    rw [Array.foldl_toList]
  have hshape : emitDynamicBlock plan tokens =
      emitTokens (buildHuffmanTable plan.litLengths 15) (buildHuffmanTable plan.distLengths 15)
        (plan.rleTokens.foldl (fun w t =>
            let w' := emitHuffSymbol w (buildHuffmanTable plan.clenLengths 7) t.1
            if t.2.1 > 0 then writeBits w' t.2.2 t.2.1 else w')
          ((List.range plan.hclen).foldl
            (fun w i => writeBits w plan.clenLengths[clenOrder[i]!]! 3)
            (writeBits (writeBits (writeBits (writeBits (writeBits {} 1 1) 2 2)
              (plan.hlit - 257) 5) (plan.hdist - 1) 5) (plan.hclen - 4) 4))) tokens := rfl
  rw [hshape, hfold]
  refine ⟨?_, h9.2.1, h9.2.2⟩
  rw [h9.1, h8.1, h7.1, h6.1, h5.1, h4.1, h3.1, h2.1, h1.1, he.1]
  unfold clenHeaderBits
  simp [natBits, List.append_assoc]

/-
## Reader-side groundwork: exact-window reads, array/list bridges, and the HCLEN header
## array reconstruction.
-/

/- REF: docs/STDLIB_ZLIB.md#41-bitstream-reader-writer -/
/-- Reading an exact `n`-bit window recovers the written value. -/
theorem readBits_exact (r : BitReader) (n v : Nat) (rest : List Bool)
    (hv : v < 2 ^ n) (hn : n ≤ 24)
    (hbits : readerBits r = natBits n v ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', readBits r n = .ok (r', v) ∧ readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hlen : n ≤ (readerBits r).length := by
    rw [hbits, List.length_append, natBits_length]
    omega
  obtain ⟨r', v', hok, hv', hwin, hdrop, hinv', hcnt', hbytes'⟩ :=
    readBits_spec r n hinv hcnt hn hlen
  have htake : (readerBits r).take n = natBits n v := by
    rw [hbits, List.take_append_of_le_length (by simp [natBits_length]),
      List.take_of_length_le (by simp [natBits_length])]
  have hveq : v' = v := natBits_inj hv' hv (by rw [hwin, htake])
  have hrest : readerBits r' = rest := by
    rw [hdrop, hbits, List.drop_left' (by rw [natBits_length])]
  subst hveq
  exact ⟨r', hok, hrest, hinv', hcnt', hbytes'⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `get!` through `toList`. -/
theorem getElem!_eq_toList_getD (arr : Array Nat) (i : Nat) :
    arr[i]! = arr.toList.getD i 0 := by
  by_cases hi : i < arr.size
  · have hl : i < arr.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    show arr[i]! = arr.toList[i]
    rw [Array.getElem_toList hl, Array.getElem!_eq_getD, Array.getD, dif_pos hi]
    rfl
  · rw [getElem!_oob arr i hi, List.getD_eq_getElem?_getD]
    have hl : ¬ i < arr.toList.length := by rw [Array.length_toList]; exact hi
    rw [List.getElem?_eq_none (by omega)]
    rfl

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The default-last of a nonempty list is its last index read. -/
theorem getLastD_eq_getD (d : Nat) : ∀ (l : List Nat), l ≠ [] →
    l.getLastD d = l.getD (l.length - 1) d := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    cases l with
    | nil => rfl
    | cons b l' =>
      show (b :: l').getLastD d = (a :: b :: l').getD ((a :: b :: l').length - 1) d
      have he : (a :: b :: l').getD ((a :: b :: l').length - 1) d
          = (b :: l').getD ((b :: l').length - 1) d := by
        show (a :: b :: l').getD ((b :: l').length - 1 + 1) d = _
        rfl
      rw [he]
      exact ih (by simp)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `pushRepeated` appends a replicate at the list level. -/
theorem pushRepeated_toList (val : Nat) : ∀ (n : Nat) (arr : Array Nat),
    (pushRepeated arr val n).toList = arr.toList ++ List.replicate n val := by
  intro n
  induction n with
  | zero => intro arr; simp [pushRepeated]
  | succ n ih =>
    intro arr
    show (pushRepeated (arr.push val) val n).toList = _
    rw [ih, Array.toList_push, List.append_assoc]
    congr 1

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- One 3-bit read per `decodeClenArray` step reconstructs the permuted length array:
    processed positions carry the plan's lengths, untouched positions stay zero. -/
theorem decodeClenArray_spec (cl : Array Nat) (hcl : ∀ i, i < 19 → cl[clenOrder[i]!]! < 8)
    (hclen : Nat) (hhc : hclen ≤ 19) :
    ∀ (fuel pos : Nat) (r : BitReader) (arr : Array Nat) (rest : List Bool),
    pos + fuel = hclen →
    arr.size = 19 →
    (∀ j, j < 19 → ((∃ i, i < pos ∧ clenOrder[i]! = j) → arr[j]! = cl[j]!) ∧
      ((¬ ∃ i, i < pos ∧ clenOrder[i]! = j) → arr[j]! = 0)) →
    readerBits r = (List.range' pos fuel).flatMap
      (fun i => natBits 3 cl[clenOrder[i]!]!) ++ rest →
    r.bitBuf.toNat < 2 ^ r.bitCount → r.bitCount < 8 →
    ∃ r' arr', decodeClenArray hclen fuel pos r arr = .ok (r', arr') ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes ∧
      arr'.size = 19 ∧
      (∀ j, j < 19 → ((∃ i, i < hclen ∧ clenOrder[i]! = j) → arr'[j]! = cl[j]!) ∧
        ((¬ ∃ i, i < hclen ∧ clenOrder[i]! = j) → arr'[j]! = 0)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos r arr rest htot hsz hinvj hbits hinv hcnt
    refine ⟨r, arr, rfl, by simpa using hbits, hinv, hcnt, rfl, hsz, ?_⟩
    have hpe : pos = hclen := by omega
    subst hpe
    exact hinvj
  | succ fuel ih =>
    intro pos r arr rest htot hsz hinvj hbits hinv hcnt
    have hpos19 : pos < 19 := by omega
    have hj19 : clenOrder[pos]! < 19 := clenOrder_lt pos hpos19
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc] at hbits
    obtain ⟨r1, hok1, hrest1, hinv1, hcnt1, hbytes1⟩ :=
      readBits_exact r 3 cl[clenOrder[pos]!]! _
        (by show _ < 2 ^ 3; have := hcl pos hpos19; omega) (by omega) hbits hinv hcnt
    have harr' : ∀ j, j < 19 →
        ((∃ i, i < pos + 1 ∧ clenOrder[i]! = j) →
          (arr.set! clenOrder[pos]! cl[clenOrder[pos]!]!)[j]! = cl[j]!) ∧
        ((¬ ∃ i, i < pos + 1 ∧ clenOrder[i]! = j) →
          (arr.set! clenOrder[pos]! cl[clenOrder[pos]!]!)[j]! = 0) := by
      intro j hj
      by_cases hje : clenOrder[pos]! = j
      · subst hje
        constructor
        · intro _
          rw [getElem!_set!_eq _ _ _ (by omega)]
        · intro hcon
          exact absurd ⟨pos, by omega, rfl⟩ hcon
      · constructor
        · intro ⟨i, hi, hie⟩
          rw [getElem!_set!_ne _ _ _ _ hje]
          refine (hinvj j hj).1 ⟨i, ?_, hie⟩
          rcases Nat.lt_or_ge i pos with h | h
          · exact h
          · exfalso
            have hip : i = pos := by omega
            subst hip
            exact hje hie
        · intro hcon
          rw [getElem!_set!_ne _ _ _ _ hje]
          exact (hinvj j hj).2 (fun ⟨i, hi, hie⟩ => hcon ⟨i, by omega, hie⟩)
    have hrec := ih (pos + 1) r1 (arr.set! clenOrder[pos]! cl[clenOrder[pos]!]!) rest
      (by omega) (by rw [size_set!]; exact hsz) harr' hrest1 hinv1 hcnt1
    obtain ⟨r', arr', hok', hrest', hinv', hcnt', hbytes', hsz', hspec'⟩ := hrec
    refine ⟨r', arr', ?_, hrest', hinv', hcnt', ?_, hsz', hspec'⟩
    · rw [decodeClenArray, hok1]
      exact hok'
    · rw [hbytes', hbytes1]

/-
## L2h, decoder side: the code-length parsing loop reconstructs exactly the RLE'd
## sequence, and `decodeDynamicTables` rebuilds the plan's tables.
-/

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A nonempty backing list means a nonempty array. -/
theorem isEmpty_false_of_toList {arr : Array Nat} {done : List Nat}
    (h : arr.toList = done) (hne : done ≠ []) : arr.isEmpty = false := by
  have hlen : 0 < done.length := List.length_pos_iff.mpr hne
  have hsz : arr.size = done.length := by
    rw [← Array.length_toList, h]
  have hz : ¬ arr.size = 0 := by omega
  simp [Array.isEmpty, hz]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **L2h decoder loop**: fed exactly the RLE stream's bits, `decodeDynamicTables.go`
    reconstructs the full code-length sequence, consuming exactly those bits. The decode
    table may be built from any `get!`-pointwise-equal copy of the encoder's clen array. -/
theorem decodeDynamicTables_go_spec (clA clB : Array Nat)
    (hpt : ∀ i : Nat, clA[i]! = clB[i]!) (hkc : kraftOk clA 7)
    (totalLengths : Nat) (full : List Nat) (hfull : full.length = totalLengths) :
    ∀ (ts : List (Nat × Nat × Nat)) (done : List Nat) (br : BitReader)
      (arr : Array Nat) (rest : List Bool),
    rleOk ts done full →
    arr.toList = done →
    (∀ t ∈ ts, 0 < clA[t.1]! ∧ clA[t.1]! ≤ 7) →
    readerBits br = rleBitsF clA ts ++ rest →
    br.bitBuf.toNat < 2 ^ br.bitCount → br.bitCount < 8 →
    ∃ br' arr',
      decodeDynamicTables.go (buildHuffmanTable clB 7) totalLengths br arr = .ok (br', arr') ∧
      arr'.toList = full ∧ readerBits br' = rest ∧
      br'.bitBuf.toNat < 2 ^ br'.bitCount ∧ br'.bitCount < 8 ∧ br'.bytes = br.bytes := by
  intro ts
  induction ts with
  | nil =>
    intro done br arr rest hok htl _ hbits hinv hcnt
    have hdone : done = full := hok
    have hsz : ¬ arr.size < totalLengths := by
      rw [← Array.length_toList, htl, hdone, hfull]
      omega
    refine ⟨br, arr, ?_, by rw [htl, hdone], by simpa [rleBitsF] using hbits, hinv, hcnt, rfl⟩
    rw [decodeDynamicTables.go.eq_def, if_neg hsz]
  | cons t ts ih =>
    intro done br arr rest hok htl hsyms hbits hinv hcnt
    obtain ⟨sym, eb, ev⟩ := t
    have hsymA := hsyms (sym, eb, ev) (by simp)
    have hlen := rleOk_length _ _ _ hok
    have hguard : arr.size < totalLengths := by
      rw [← Array.length_toList, htl, ← hfull]
      exact hlen.2 (by simp)
    -- the clen symbol decode
    have hbits1 : readerBits br = codeBits (canonicalCode clA 7 sym) clA[sym]! ++
        (natBits eb ev ++ (rleBitsF clA ts ++ rest)) := by
      rw [hbits]
      unfold rleBitsF
      rw [List.flatMap_cons]
      simp [List.append_assoc]
    obtain ⟨r1, hok1, hrest1, hinv1, hcnt1, hbytes1⟩ :=
      decodeHuffmanSymbol_canonical clA clB 7 hpt hkc hsymA.1 hsymA.2 br _ hbits1 hinv hcnt
    rw [decodeDynamicTables.go.eq_def, if_pos hguard]
    -- reduce the symbol-decode match
    rcases hok with ⟨h15, heb, hev, hrec⟩ | ⟨h16, heb, hev, hne, hrec⟩ |
      ⟨h17, heb, hev, hrec⟩ | ⟨h18, heb, hev, hrec⟩
    · -- literal length 0–15
      subst heb
      subst hev
      have hrest1' : readerBits r1 = rleBitsF clA ts ++ rest := by
        rw [hrest1]
        simp [natBits]
      have hstep := ih (done ++ [sym]) r1 (arr.push sym) rest hrec
        (by rw [Array.toList_push, htl])
        (fun t' ht' => hsyms t' (by simp [ht'])) hrest1' hinv1 hcnt1
      obtain ⟨br', arr', hgo, htl', hrest', hinv', hcnt', hbytes'⟩ := hstep
      refine ⟨br', arr', ?_, htl', hrest', hinv', hcnt', by rw [hbytes', hbytes1]⟩
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym' heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨hh1, hh2⟩ := hok1
        subst hh1
        rw [hh2, if_pos (by omega : sym ≤ 15)]
        exact hgo
    · -- 16: repeat previous
      subst h16
      subst heb
      have hne' : arr.isEmpty = false := isEmpty_false_of_toList htl hne
      obtain ⟨r2, hok2, hrest2, hinv2, hcnt2, hbytes2⟩ :=
        readBits_exact r1 2 ev (rleBitsF clA ts ++ rest)
          (by show ev < 2 ^ 2; omega) (by omega) (by rw [hrest1]) hinv1 hcnt1
      have hlast : arr[arr.size - 1]! = done.getLastD 0 := by
        rw [getElem!_eq_toList_getD, htl, ← Array.length_toList, htl,
          getLastD_eq_getD 0 done hne]
      have hstep := ih (done ++ List.replicate (ev + 3) (done.getLastD 0)) r2
        (pushRepeated arr (arr[arr.size - 1]!) (ev + 3)) rest hrec
        (by rw [pushRepeated_toList, htl, hlast])
        (fun t' ht' => hsyms t' (by simp [ht'])) hrest2 hinv2 hcnt2
      obtain ⟨br', arr', hgo, htl', hrest', hinv', hcnt', hbytes'⟩ := hstep
      refine ⟨br', arr', ?_, htl', hrest', hinv', hcnt',
        by rw [hbytes', hbytes2, hbytes1]⟩
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym' heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨hh1, hh2⟩ := hok1
        subst hh1
        subst hh2
        rw [if_neg (by omega : ¬ (16 : Nat) ≤ 15),
          if_pos (by decide : ((16 : Nat) == 16) = true),
          if_neg (by rw [Array.isEmpty] at hne' ⊢; simp at hne' ⊢; omega)]
        split
        · rename_i e heq2
          rw [heq2] at hok2
          exact absurd hok2 (by simp)
        · rename_i rRepeat extra heq2
          rw [heq2] at hok2
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok2
          obtain ⟨hh1, hh2⟩ := hok2
          subst hh1
          subst hh2
          exact hgo
    · -- 17: short zero run
      subst h17
      subst heb
      obtain ⟨r2, hok2, hrest2, hinv2, hcnt2, hbytes2⟩ :=
        readBits_exact r1 3 ev (rleBitsF clA ts ++ rest)
          (by show ev < 2 ^ 3; omega) (by omega) (by rw [hrest1]) hinv1 hcnt1
      have hstep := ih (done ++ List.replicate (ev + 3) 0) r2
        (pushRepeated arr 0 (ev + 3)) rest hrec
        (by rw [pushRepeated_toList, htl])
        (fun t' ht' => hsyms t' (by simp [ht'])) hrest2 hinv2 hcnt2
      obtain ⟨br', arr', hgo, htl', hrest', hinv', hcnt', hbytes'⟩ := hstep
      refine ⟨br', arr', ?_, htl', hrest', hinv', hcnt',
        by rw [hbytes', hbytes2, hbytes1]⟩
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym' heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨hh1, hh2⟩ := hok1
        subst hh1
        subst hh2
        rw [if_neg (by omega : ¬ (17 : Nat) ≤ 15),
          if_neg (by decide : ¬ ((17 : Nat) == 16) = true),
          if_pos (by decide : ((17 : Nat) == 17) = true)]
        split
        · rename_i e heq2
          rw [heq2] at hok2
          exact absurd hok2 (by simp)
        · rename_i rRepeat extra heq2
          rw [heq2] at hok2
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok2
          obtain ⟨hh1, hh2⟩ := hok2
          subst hh1
          subst hh2
          exact hgo
    · -- 18: long zero run
      subst h18
      subst heb
      obtain ⟨r2, hok2, hrest2, hinv2, hcnt2, hbytes2⟩ :=
        readBits_exact r1 7 ev (rleBitsF clA ts ++ rest)
          (by show ev < 2 ^ 7; omega) (by omega) (by rw [hrest1]) hinv1 hcnt1
      have hstep := ih (done ++ List.replicate (ev + 11) 0) r2
        (pushRepeated arr 0 (ev + 11)) rest hrec
        (by rw [pushRepeated_toList, htl])
        (fun t' ht' => hsyms t' (by simp [ht'])) hrest2 hinv2 hcnt2
      obtain ⟨br', arr', hgo, htl', hrest', hinv', hcnt', hbytes'⟩ := hstep
      refine ⟨br', arr', ?_, htl', hrest', hinv', hcnt',
        by rw [hbytes', hbytes2, hbytes1]⟩
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym' heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨hh1, hh2⟩ := hok1
        subst hh1
        subst hh2
        rw [if_neg (by omega : ¬ (18 : Nat) ≤ 15),
          if_neg (by decide : ¬ ((18 : Nat) == 16) = true),
          if_neg (by decide : ¬ ((18 : Nat) == 17) = true),
          if_pos (by decide : ((18 : Nat) == 18) = true)]
        split
        · rename_i e heq2
          rw [heq2] at hok2
          exact absurd hok2 (by simp)
        · rename_i rRepeat extra heq2
          rw [heq2] at hok2
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok2
          obtain ⟨hh1, hh2⟩ := hok2
          subst hh1
          subst hh2
          exact hgo

/-
## `decodeDynamicTables` reconstructs the plan's tables from the emitted header bits.
-/

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `getD` through a truncating `take`. -/
theorem getD_take_of_lt (l : List Nat) (n i : Nat) (h : i < n) :
    (l.take n).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt h]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **The dynamic-table header roundtrip**: fed exactly the bits `emitDynamicBlock` wrote
    for the counts, the permuted clen lengths, and the RLE stream, `decodeDynamicTables`
    succeeds with tables built from `get!`-pointwise copies of the plan's length arrays,
    consuming exactly those bits. -/
theorem decodeDynamicTables_spec (plan : DynPlan) (r : BitReader) (rest : List Bool)
    (hclsize : plan.clenLengths.size = 19)
    (hkc : kraftOk plan.clenLengths 7)
    (hcl7 : ∀ i : Nat, plan.clenLengths[i]! ≤ 7)
    (hhlit : 257 ≤ plan.hlit ∧ plan.hlit ≤ 286)
    (hhdist : 1 ≤ plan.hdist ∧ plan.hdist ≤ 30)
    (hhclen : plan.hclen = hclenF plan.clenLengths)
    (hlitsize : plan.litLengths.size = 286)
    (hdistsize : plan.distLengths.size = 30)
    (hlitzero : ∀ i : Nat, plan.hlit ≤ i → plan.litLengths[i]! = 0)
    (hdistzero : ∀ i : Nat, plan.hdist ≤ i → plan.distLengths[i]! = 0)
    (hrleok : rleOk plan.rleTokens []
      (plan.litLengths.toList.take plan.hlit ++ plan.distLengths.toList.take plan.hdist))
    (hrlesyms : ∀ t ∈ plan.rleTokens,
      0 < plan.clenLengths[t.1]! ∧ plan.clenLengths[t.1]! ≤ 7)
    (hbits : readerBits r = natBits 5 (plan.hlit - 257) ++ (natBits 5 (plan.hdist - 1) ++
      (natBits 4 (plan.hclen - 4) ++ (clenHeaderBits plan ++
      (rleBitsF plan.clenLengths plan.rleTokens ++ rest)))))
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r' litB distB,
      decodeDynamicTables r = .ok (r', buildHuffmanTable litB 15, buildHuffmanTable distB 15) ∧
      (∀ i : Nat, litB[i]! = plan.litLengths[i]!) ∧
      (∀ i : Nat, distB[i]! = plan.distLengths[i]!) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hhc := hclenF_bounds plan.clenLengths
  rw [← hhclen] at hhc
  -- the three count reads
  obtain ⟨r1, hok1, hrest1, hinv1, hcnt1, hbytes1⟩ :=
    readBits_exact r 5 (plan.hlit - 257) _ (by show _ < 2 ^ 5; omega) (by omega)
      hbits hinv hcnt
  obtain ⟨r2, hok2, hrest2, hinv2, hcnt2, hbytes2⟩ :=
    readBits_exact r1 5 (plan.hdist - 1) _ (by show _ < 2 ^ 5; omega) (by omega)
      hrest1 hinv1 hcnt1
  obtain ⟨r3, hok3, hrest3, hinv3, hcnt3, hbytes3⟩ :=
    readBits_exact r2 4 (plan.hclen - 4) _ (by show _ < 2 ^ 4; omega) (by omega)
      hrest2 hinv2 hcnt2
  -- the permuted clen length reads
  have hclbits : readerBits r3 = (List.range' 0 plan.hclen).flatMap
      (fun i => natBits 3 plan.clenLengths[clenOrder[i]!]!) ++
      (rleBitsF plan.clenLengths plan.rleTokens ++ rest) := by
    rw [hrest3]
    unfold clenHeaderBits
    rw [List.range_eq_range']
  have hcl8 : ∀ i, i < 19 → plan.clenLengths[clenOrder[i]!]! < 8 := by
    intro i _
    have := hcl7 clenOrder[i]!
    omega
  obtain ⟨r4, clenArr, hok4, hrest4, hinv4, hcnt4, hbytes4, hclsz, hclspec⟩ :=
    decodeClenArray_spec plan.clenLengths hcl8 plan.hclen (by omega) plan.hclen 0 r3
      (Array.replicate 19 0) _ (by omega) (by rw [Array.size_replicate])
      (by
        intro j hj
        refine ⟨fun ⟨i, hi, _⟩ => absurd hi (by omega), fun _ => ?_⟩
        exact getElem!_replicate 19 0 j hj)
      hclbits hinv3 hcnt3
  -- the reconstructed clen array reads back the plan's, at every index
  have hptC : ∀ i : Nat, plan.clenLengths[i]! = clenArr[i]! := by
    intro j
    by_cases hj : j < 19
    · obtain ⟨i, hi19, hie⟩ := clenOrder_surj j hj
      rcases Nat.lt_or_ge i plan.hclen with hilt | hige
      · exact ((hclspec j hj).1 ⟨i, hilt, hie⟩).symm
      · have hzero : plan.clenLengths[j]! = 0 := by
          rw [← hie]
          exact hclenF_covers plan.clenLengths i hi19 (by omega)
        have hnone : ¬ ∃ i', i' < plan.hclen ∧ clenOrder[i']! = j := by
          intro ⟨i', hi', hie'⟩
          have : i' = i := clenOrder_inj i' (by omega) i hi19 (by rw [hie', hie])
          omega
        rw [hzero, (hclspec j hj).2 hnone]
    · rw [getElem!_oob plan.clenLengths j (by omega),
        getElem!_oob clenArr j (by rw [hclsz]; omega)]
  -- the code-length parsing loop
  have hfull_len : (plan.litLengths.toList.take plan.hlit ++
      plan.distLengths.toList.take plan.hdist).length = plan.hlit + plan.hdist := by
    rw [List.length_append, List.length_take, List.length_take,
      Array.length_toList, Array.length_toList, hlitsize, hdistsize]
    omega
  obtain ⟨r5, lenArr, hok5, hltl, hrest5, hinv5, hcnt5, hbytes5⟩ :=
    decodeDynamicTables_go_spec plan.clenLengths clenArr hptC hkc
      (plan.hlit + plan.hdist) _ hfull_len plan.rleTokens [] r4 (Array.mkEmpty _) rest
      hrleok rfl hrlesyms hrest4 hinv4 hcnt4
  -- name the two trimmed arrays the decoder builds
  refine ⟨r5, lenArr.extract 0 plan.hlit, lenArr.extract plan.hlit (plan.hlit + plan.hdist),
    ?_, ?_, ?_, hrest5, hinv5, hcnt5,
    by rw [hbytes5, hbytes4, hbytes3, hbytes2, hbytes1]⟩
  · -- assemble the do-chain
    unfold decodeDynamicTables
    rw [hok1]
    simp only [Bind.bind, Except.bind]
    rw [hok2]
    simp only [Bind.bind, Except.bind]
    rw [hok3]
    simp only [Bind.bind, Except.bind]
    rw [show plan.hlit - 257 + 257 = plan.hlit from by omega,
      show plan.hdist - 1 + 1 = plan.hdist from by omega,
      show plan.hclen - 4 + 4 = plan.hclen from by omega]
    rw [hok4]
    simp only [Bind.bind, Except.bind]
    rw [hok5]
  · -- literal lengths read back pointwise
    intro i
    have hA_len : (plan.litLengths.toList.take plan.hlit).length = plan.hlit := by
      rw [List.length_take, Array.length_toList, hlitsize]
      omega
    have hextl : (lenArr.extract 0 plan.hlit).toList =
        plan.litLengths.toList.take plan.hlit := by
      rw [Array.toList_extract, hltl]
      show ((plan.litLengths.toList.take plan.hlit ++
        plan.distLengths.toList.take plan.hdist).drop 0).take (plan.hlit - 0) = _
      rw [List.drop_zero, Nat.sub_zero,
        List.take_append_of_le_length (by simp [hA_len]),
        List.take_of_length_le (by simp [hA_len])]
    rw [getElem!_eq_toList_getD, hextl]
    by_cases hi : i < plan.hlit
    · rw [getD_take_of_lt _ _ _ hi, ← getElem!_eq_toList_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hA_len]; omega)]
      show (0 : Nat) = plan.litLengths[i]!
      rw [hlitzero i (by omega)]
  · -- distance lengths read back pointwise
    intro i
    have hA_len : (plan.litLengths.toList.take plan.hlit).length = plan.hlit := by
      rw [List.length_take, Array.length_toList, hlitsize]
      omega
    have hB_len : (plan.distLengths.toList.take plan.hdist).length = plan.hdist := by
      rw [List.length_take, Array.length_toList, hdistsize]
      omega
    have hextl : (lenArr.extract plan.hlit (plan.hlit + plan.hdist)).toList =
        plan.distLengths.toList.take plan.hdist := by
      rw [Array.toList_extract, hltl]
      show ((plan.litLengths.toList.take plan.hlit ++
        plan.distLengths.toList.take plan.hdist).drop plan.hlit).take
          (plan.hlit + plan.hdist - plan.hlit) = _
      rw [show plan.hlit + plan.hdist - plan.hlit = plan.hdist from by omega,
        show (plan.litLengths.toList.take plan.hlit ++
          plan.distLengths.toList.take plan.hdist).drop plan.hlit =
          (plan.litLengths.toList.take plan.hlit ++
            plan.distLengths.toList.take plan.hdist).drop
              (plan.litLengths.toList.take plan.hlit).length from by rw [hA_len],
        List.drop_left, List.take_of_length_le (by simp [hB_len])]
    rw [getElem!_eq_toList_getD, hextl]
    by_cases hi : i < plan.hdist
    · rw [getD_take_of_lt _ _ _ hi, ← getElem!_eq_toList_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hB_len]; omega)]
      show (0 : Nat) = plan.distLengths[i]!
      rw [hdistzero i (by omega)]

/-
## The dynamic instance of the L5 stream induction: per-token decode lemmas and the
## `decodeHuffmanStream.go` induction under the transmitted tables.
-/

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decoding one literal token's bits under the dynamic tables. -/
theorem decode_lit_dyn (litA litB : Array Nat) (hptL : ∀ i : Nat, litA[i]! = litB[i]!)
    (hkl : kraftOk litA 15) (b : UInt8) (hok : 0 < litA[b.toNat]! ∧ litA[b.toNat]! ≤ 15)
    (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = tokenBitsDyn litA litA (.lit b) ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r (buildHuffmanTable litB 15) = .ok (r', b.toNat) ∧
      b.toNat < 256 ∧ readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hb : b.toNat < 256 := b.toNat_lt
  obtain ⟨r', hok', hrest, hinv', hcnt', hbytes'⟩ :=
    decodeHuffmanSymbol_canonical litA litB 15 hptL hkl hok.1 hok.2 r rest
      (by simpa [tokenBitsDyn] using hbits) hinv hcnt
  exact ⟨r', hok', hb, hrest, hinv', hcnt', hbytes'⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decoding the end-of-block symbol's bits under the dynamic tables. -/
theorem decode_eob_dyn (litA litB : Array Nat) (hptL : ∀ i : Nat, litA[i]! = litB[i]!)
    (hkl : kraftOk litA 15) (heob : 0 < litA[256]! ∧ litA[256]! ≤ 15)
    (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = codeBits (canonicalCode litA 15 256) litA[256]! ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r (buildHuffmanTable litB 15) = .ok (r', 256) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes :=
  decodeHuffmanSymbol_canonical litA litB 15 hptL hkl heob.1 heob.2 r rest hbits hinv hcnt

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Decoding one back-reference token's bits under the dynamic tables: all four reads
    succeed with the encoder's values and the decoder's table lookups reconstruct the
    token exactly. -/
theorem decode_ref_dyn (litA litB distA distB : Array Nat)
    (hptL : ∀ i : Nat, litA[i]! = litB[i]!) (hptD : ∀ i : Nat, distA[i]! = distB[i]!)
    (hkl : kraftOk litA 15) (hkd : kraftOk distA 15)
    (len dist : Nat) (h3 : 3 ≤ len) (h258 : len ≤ 258)
    (h1d : 1 ≤ dist) (h32768 : dist ≤ 32768)
    (hlsym : 0 < litA[(encodeLength len).1]! ∧ litA[(encodeLength len).1]! ≤ 15)
    (hdsym : 0 < distA[(encodeDistance dist).1]! ∧ distA[(encodeDistance dist).1]! ≤ 15)
    (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = tokenBitsDyn litA distA (.ref len dist) ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r1 r2 r3 r4 extraL extraD,
      decodeHuffmanSymbol r (buildHuffmanTable litB 15) = .ok (r1, (encodeLength len).1) ∧
      257 ≤ (encodeLength len).1 ∧ (encodeLength len).1 ≤ 285 ∧
      (if lengthTable[(encodeLength len).1 - 257]!.2 > 0
        then readBits r1 lengthTable[(encodeLength len).1 - 257]!.2
        else (pure (r1, 0) : Except ZlibError (BitReader × Nat))) = .ok (r2, extraL) ∧
      lengthTable[(encodeLength len).1 - 257]!.1 + extraL = len ∧
      decodeHuffmanSymbol r2 (buildHuffmanTable distB 15) = .ok (r3, (encodeDistance dist).1) ∧
      (encodeDistance dist).1 < 30 ∧
      (if distanceTable[(encodeDistance dist).1]!.2 > 0
        then readBits r3 distanceTable[(encodeDistance dist).1]!.2
        else (pure (r3, 0) : Except ZlibError (BitReader × Nat))) = .ok (r4, extraD) ∧
      distanceTable[(encodeDistance dist).1]!.1 + extraD = dist ∧
      readerBits r4 = rest ∧
      r4.bitBuf.toNat < 2 ^ r4.bitCount ∧ r4.bitCount < 8 ∧ r4.bytes = r.bytes := by
  obtain ⟨hL257, hL285, hLeb, hLev, hLbase, hLtbl⟩ := encodeLength_spec len (by omega) h3
  obtain ⟨hDc, hDeb, hDev, hDbase, hDtbl⟩ := encodeDistance_spec' dist h1d h32768
  have hbits' : readerBits r =
      codeBits (canonicalCode litA 15 (encodeLength len).1) litA[(encodeLength len).1]! ++
        (natBits (encodeLength len).2.1 (encodeLength len).2.2 ++
          (codeBits (canonicalCode distA 15 (encodeDistance dist).1)
              distA[(encodeDistance dist).1]! ++
            (natBits (encodeDistance dist).2.1 (encodeDistance dist).2.2 ++ rest))) := by
    rw [hbits]
    unfold tokenBitsDyn
    simp [List.append_assoc]
  obtain ⟨r1, hok1, hrest1, hinv1, hcnt1, hbytes1⟩ :=
    decodeHuffmanSymbol_canonical litA litB 15 hptL hkl hlsym.1 hlsym.2 r _ hbits' hinv hcnt
  obtain ⟨r2, hok2, hrest2, hinv2, hcnt2, hbytes2⟩ :=
    readBits_extra r1 (encodeLength len).2.1 (encodeLength len).2.2 _ hLev (by omega)
      hrest1 hinv1 hcnt1
  obtain ⟨r3, hok3, hrest3, hinv3, hcnt3, hbytes3⟩ :=
    decodeHuffmanSymbol_canonical distA distB 15 hptD hkd hdsym.1 hdsym.2 r2 _
      hrest2 hinv2 hcnt2
  obtain ⟨r4, hok4, hrest4, hinv4, hcnt4, hbytes4⟩ :=
    readBits_extra r3 (encodeDistance dist).2.1 (encodeDistance dist).2.2 rest hDev (by omega)
      hrest3 hinv3 hcnt3
  refine ⟨r1, r2, r3, r4, (encodeLength len).2.2, (encodeDistance dist).2.2,
    hok1, hL257, hL285, ?_, ?_, hok3, by omega, ?_, ?_, hrest4, hinv4, hcnt4, ?_⟩
  · rw [hLtbl]; exact hok2
  · rw [hLbase]
  · rw [hDtbl]; exact hok4
  · rw [hDbase]
  · rw [hbytes4, hbytes3, hbytes2, hbytes1]

set_option maxHeartbeats 1000000 in
/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **L5 (dynamic path)**: the decoder's stream loop, fed exactly the bits `emitTokens`
    wrote under the transmitted tables for a positionally well-formed token list,
    terminates at the end-of-block symbol having expanded exactly those tokens. -/
theorem decodeHuffmanStream_go_dyn (litA litB distA distB : Array Nat)
    (hptL : ∀ i : Nat, litA[i]! = litB[i]!) (hptD : ∀ i : Nat, distA[i]! = distB[i]!)
    (hkl : kraftOk litA 15) (hkd : kraftOk distA 15)
    (heob : 0 < litA[256]! ∧ litA[256]! ≤ 15)
    (hL : ∃ l rr, (buildHuffmanTable litB 15).root = HuffmanNode.branch l rr)
    (hD : ∃ l rr, (buildHuffmanTable distB 15).root = HuffmanNode.branch l rr) :
    ∀ (ts : List LZToken) (r : BitReader) (curOut : ByteArray) (rest : List Bool),
      tokensWF ts curOut.size →
      (∀ t ∈ ts, dynTokenOk litA distA t) →
      readerBits r = tokensBitsDyn litA distA ts ++
        (codeBits (canonicalCode litA 15 256) litA[256]! ++ rest) →
      r.bitBuf.toNat < 2 ^ r.bitCount → r.bitCount < 8 →
      ∃ r', decodeHuffmanStream.go (buildHuffmanTable litB 15) (buildHuffmanTable distB 15)
          r curOut hL hD = .ok (r', ts.foldl expandToken curOut) ∧
        readerBits r' = rest ∧
        r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  intro ts
  induction ts with
  | nil =>
    intro r curOut rest hwf _ hbits hinv hcnt
    obtain ⟨rE, hokE, hrestE, hinvE, hcntE, hbytesE⟩ :=
      decode_eob_dyn litA litB hptL hkl heob r rest
        (by simpa [tokensBitsDyn] using hbits) hinv hcnt
    refine ⟨rE, ?_, hrestE, hinvE, hcntE, hbytesE⟩
    rw [decodeHuffmanStream.go.eq_def]
    split
    · rename_i e heq
      rw [heq] at hokE
      exact absurd hokE (by simp)
    · rename_i nextR sym heq
      rw [heq] at hokE
      simp only [Except.ok.injEq, Prod.mk.injEq] at hokE
      obtain ⟨h1, h2⟩ := hokE
      subst h1
      subst h2
      rw [if_neg (by omega : ¬ (256 : Nat) < 256), if_pos (by decide : ((256:Nat) == 256) = true)]
      rfl
  | cons t ts ih =>
    intro r curOut rest hwf hok hbits hinv hcnt
    cases t with
    | lit b =>
      have hbits1 : readerBits r = tokenBitsDyn litA litA (.lit b) ++
          (tokensBitsDyn litA distA ts ++
            (codeBits (canonicalCode litA 15 256) litA[256]! ++ rest)) := by
        rw [hbits]
        show tokenBitsDyn litA distA (.lit b) ++ tokensBitsDyn litA distA ts ++ _ = _
        have he : tokenBitsDyn litA distA (.lit b) = tokenBitsDyn litA litA (.lit b) := rfl
        rw [he, List.append_assoc]
      obtain ⟨r1, hok1, hb256, hrest1, hinv1, hcnt1, hbytes1⟩ :=
        decode_lit_dyn litA litB hptL hkl b
          (show 0 < litA[b.toNat]! ∧ litA[b.toNat]! ≤ 15 from hok (LZToken.lit b) (by simp))
          r _ hbits1 hinv hcnt
      have hwf' : tokensWF ts (curOut.push b).size := by
        rw [ByteArray.size_push]
        exact hwf
      obtain ⟨r', hok', hrest', hinv', hcnt', hbytes'⟩ :=
        ih r1 (curOut.push b) rest hwf' (fun t' ht' => hok t' (by simp [ht'])) hrest1
          hinv1 hcnt1
      refine ⟨r', ?_, hrest', hinv', hcnt', by rw [hbytes', hbytes1]⟩
      rw [decodeHuffmanStream.go.eq_def]
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨h1, h2⟩ := hok1
        subst h1
        subst h2
        rw [if_pos hb256, List.foldl_cons]
        have hpush : b.toNat.toUInt8 = b := UInt8.ofNat_toNat
        rw [hpush]
        exact hok'
    | ref len dist =>
      obtain ⟨h3, h258, h1d, h32768, hdlepos, hwfrest⟩ := hwf
      have htok : (3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) ∧
          (0 < litA[(encodeLength len).1]! ∧ litA[(encodeLength len).1]! ≤ 15) ∧
          (0 < distA[(encodeDistance dist).1]! ∧ distA[(encodeDistance dist).1]! ≤ 15) :=
        hok (LZToken.ref len dist) (by simp)
      obtain ⟨_, hlsym, hdsym⟩ := htok
      have hbits1 : readerBits r = tokenBitsDyn litA distA (.ref len dist) ++
          (tokensBitsDyn litA distA ts ++
            (codeBits (canonicalCode litA 15 256) litA[256]! ++ rest)) := by
        rw [hbits]
        show tokenBitsDyn litA distA (.ref len dist) ++ tokensBitsDyn litA distA ts ++ _ = _
        rw [List.append_assoc]
      obtain ⟨r1, r2, r3, r4, extraL, extraD, hok1, hs257, hs285, hok2, hbase, hok3,
        hd30, hok4, hdbase, hrest4, hinv4, hcnt4, hbytes4⟩ :=
        decode_ref_dyn litA litB distA distB hptL hptD hkl hkd len dist h3 h258 h1d h32768
          hlsym hdsym r _ hbits1 hinv hcnt
      have hwf' : tokensWF ts (lzCopy dist len curOut).size := by
        rw [lzCopy_size]
        exact hwfrest
      obtain ⟨r', hok', hrest', hinv', hcnt', hbytes'⟩ :=
        ih r4 (lzCopy dist len curOut) rest hwf' (fun t' ht' => hok t' (by simp [ht']))
          hrest4 hinv4 hcnt4
      refine ⟨r', ?_, hrest', hinv', hcnt', by rw [hbytes', hbytes4]⟩
      rw [decodeHuffmanStream.go.eq_def]
      split
      · rename_i e heq
        rw [heq] at hok1
        exact absurd hok1 (by simp)
      · rename_i nextR sym heq
        rw [heq] at hok1
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok1
        obtain ⟨h1, h2⟩ := hok1
        subst h1
        subst h2
        rw [if_neg (by omega : ¬ (encodeLength len).1 < 256),
          if_neg (by simp; omega), if_pos (by omega : (encodeLength len).1 ≤ 285)]
        dsimp only
        split
        · rename_i e heq2
          rw [heq2] at hok2
          exact absurd hok2 (by simp)
        · rename_i rLen extraVal heq2
          rw [heq2] at hok2
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok2
          obtain ⟨h1, h2⟩ := hok2
          subst h1
          subst h2
          split
          · rename_i e heq3
            rw [heq3] at hok3
            exact absurd hok3 (by simp)
          · rename_i rDistSym distSym heq3
            rw [heq3] at hok3
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok3
            obtain ⟨h1, h2⟩ := hok3
            subst h1
            subst h2
            rw [if_neg (by omega : ¬ (encodeDistance dist).1 ≥ 30)]
            split
            · rename_i e heq4
              rw [heq4] at hok4
              exact absurd hok4 (by simp)
            · rename_i rDist distExtraVal heq4
              rw [heq4] at hok4
              simp only [Except.ok.injEq, Prod.mk.injEq] at hok4
              obtain ⟨h1, h2⟩ := hok4
              subst h1
              subst h2
              rw [hdbase, hbase]
              rw [if_neg (by simp; omega)]
              rw [idrun_copy_eq_lzCopy, List.foldl_cons]
              exact hok'

/-
## The dynamic-block roundtrip and `deflate_roundtrip_soundness`.
-/

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `decodeHuffmanStream` (top-level) on a dynamic-table stream, from `go`'s induction. -/
theorem decodeHuffmanStream_dyn (litA litB distA distB : Array Nat)
    (hptL : ∀ i : Nat, litA[i]! = litB[i]!) (hptD : ∀ i : Nat, distA[i]! = distB[i]!)
    (hkl : kraftOk litA 15) (hkd : kraftOk distA 15)
    (heob : 0 < litA[256]! ∧ litA[256]! ≤ 15)
    (hL : ∃ l rr, (buildHuffmanTable litB 15).root = HuffmanNode.branch l rr)
    (hD : ∃ l rr, (buildHuffmanTable distB 15).root = HuffmanNode.branch l rr)
    (ts : List LZToken) (r : BitReader) (curOut : ByteArray) (rest : List Bool)
    (hwf : tokensWF ts curOut.size)
    (hok : ∀ t ∈ ts, dynTokenOk litA distA t)
    (hbits : readerBits r = tokensBitsDyn litA distA ts ++
      (codeBits (canonicalCode litA 15 256) litA[256]! ++ rest))
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanStream r (buildHuffmanTable litB 15) (buildHuffmanTable distB 15)
        hL hD curOut = .ok (r', ts.foldl expandToken curOut) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  unfold decodeHuffmanStream
  exact decodeHuffmanStream_go_dyn litA litB distA distB hptL hptD hkl hkd heob hL hD
    ts r curOut rest hwf hok hbits hinv hcnt

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- **L7 (dynamic block)**: `decompress` of a flushed `emitDynamicBlock` — under the plan
    `buildDynPlan` computes for the same tokens — recovers exactly the expansion of the
    emitted tokens. -/
theorem decompress_dynamicBlock (tokens : Array LZToken)
    (hwf : tokensWF tokens.toList 0) :
    decompress (flushBitWriter (emitDynamicBlock (buildDynPlan tokens) tokens))
      = .ok (expandTokens tokens) := by
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
  have hr := readerBits_of_flushed _ hw.2.2 hw.2.1
  rw [hw.1] at hr
  have hm := readerBits_mkBitReader (flushBitWriter (emitDynamicBlock (buildDynPlan tokens) tokens))
  -- ------------------------------------------------------------------
  -- Reader side
  -- ------------------------------------------------------------------
  unfold decompress
  rw [decompress.go.eq_def]
  -- BFINAL = 1
  have hbits0 : readerBits (mkBitReader (flushBitWriter
      (emitDynamicBlock (buildDynPlan tokens) tokens))) =
      natBits 1 1 ++ (natBits 2 2 ++
        (natBits 5 ((buildDynPlan tokens).hlit - 257) ++
          (natBits 5 ((buildDynPlan tokens).hdist - 1) ++
            (natBits 4 ((buildDynPlan tokens).hclen - 4) ++
              (clenHeaderBits (buildDynPlan tokens) ++
                (rleBitsF (buildDynPlan tokens).clenLengths (buildDynPlan tokens).rleTokens ++
                  (tokensBitsDyn (buildDynPlan tokens).litLengths
                      (buildDynPlan tokens).distLengths tokens.toList ++
                    (codeBits (canonicalCode (buildDynPlan tokens).litLengths 15 256)
                        (buildDynPlan tokens).litLengths[256]! ++
                      List.replicate ((8 - (emitDynamicBlock (buildDynPlan tokens)
                        tokens).bitCount) % 8) false)))))))) := by
    rw [hr]
    simp [List.append_assoc]
    rfl
  obtain ⟨rB, hokB, hrestB, hinvB, hcntB, _⟩ :=
    readBits_exact _ 1 1 _ (by omega) (by omega) hbits0 hm.2.1 hm.2.2
  obtain ⟨rT, hokT, hrestT, hinvT, hcntT, _⟩ :=
    readBits_exact rB 2 2 _ (by omega) (by omega) hrestB hinvB hcntB
  -- the dynamic tables
  obtain ⟨rTab, litB, distB, hokTab, hptL, hptD, hrestTab, hinvTab, hcntTab, _⟩ :=
    decodeDynamicTables_spec (buildDynPlan tokens) rT _ hclsize hkc hcl7
      hhlit hhdist hhclen hlitsize hdistsize hlitzero hdistzero hrleok hrlesyms
      hrestT hinvT hcntT
  have hptL' : ∀ i : Nat, (buildDynPlan tokens).litLengths[i]! = litB[i]! :=
    fun i => (hptL i).symm
  have hptD' : ∀ i : Nat, (buildDynPlan tokens).distLengths[i]! = distB[i]! :=
    fun i => (hptD i).symm
  -- the payload
  obtain ⟨rS, hokS, hrestS, hinvS, hcntS, _⟩ :=
    decodeHuffmanStream_dyn (buildDynPlan tokens).litLengths litB
      (buildDynPlan tokens).distLengths distB hptL' hptD' hkl hkd heob
      (buildHuffmanTable_isBranch litB 15) (buildHuffmanTable_isBranch distB 15)
      tokens.toList rTab ByteArray.empty _ (by simpa using hwf) htoks hrestTab
      hinvTab hcntTab
  -- ------------------------------------------------------------------
  -- Choreography: reduce decompress.go's match chain
  -- ------------------------------------------------------------------
  split
  · rename_i e heq
    rw [heq] at hokB
    exact absurd hokB (by simp)
  · rename_i rBfinal bfinal heq
    rw [heq] at hokB
    simp only [Except.ok.injEq, Prod.mk.injEq] at hokB
    obtain ⟨hh1, hh2⟩ := hokB
    subst hh1
    subst hh2
    split
    · rename_i e heq2
      rw [heq2] at hokT
      exact absurd hokT (by simp)
    · rename_i rBtype btype heq2
      rw [heq2] at hokT
      simp only [Except.ok.injEq, Prod.mk.injEq] at hokT
      obtain ⟨hh1, hh2⟩ := hokT
      subst hh1
      subst hh2
      split
      · rename_i heqb hx
        exact absurd heqb (by decide)
      · rename_i heqb hx
        exact absurd heqb (by decide)
      · -- btype = 2: the dynamic branch
        split
        · rename_i e heq3
          rw [heq3] at hokTab
          exact absurd hokTab (by simp)
        · rename_i rTables litTbl distTbl heq3
          rw [heq3] at hokTab
          simp only [Except.ok.injEq, Prod.mk.injEq] at hokTab
          obtain ⟨hh1, hh2, hh3⟩ := hokTab
          subst hh1
          subst hh2
          subst hh3
          split
          · rename_i e heq4
            have hcontra : (Except.ok (rS, tokens.toList.foldl expandToken ByteArray.empty) :
                Except ZlibError (BitReader × ByteArray)) = .error e := by
              rw [← hokS]
              exact heq4
            exact absurd hcontra (by simp)
          · rename_i nextR nextOut heq4
            have hcomb : (Except.ok (rS, tokens.toList.foldl expandToken ByteArray.empty) :
                Except ZlibError (BitReader × ByteArray)) = .ok (nextR, nextOut) := by
              rw [← hokS]
              exact heq4
            simp only [Except.ok.injEq, Prod.mk.injEq] at hcomb
            obtain ⟨hh1, hh2⟩ := hcomb
            rw [if_pos (by decide : ((1:Nat) == 1) = true)]
            rw [← hh2]
            unfold expandTokens
            rw [Array.foldl_toList]
      · rename_i h0 h1 h2
        exact (h2 heq2 rfl HEq.rfl).elim

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `compress` takes the dynamic branch exactly when it wins the bit-cost comparison. -/
theorem compress_dynamic_branch (data : ByteArray)
    (h : dynPlanBitCost (buildDynPlan (tokenize data)) (tokenize data) <
        fixedBitCost (tokenize data)) :
    compress data = flushBitWriter (emitDynamicBlock (buildDynPlan (tokenize data))
      (tokenize data)) := by
  unfold compress compressPlan
  rw [if_pos h]

/- REF: docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems -/
/-- **DEFLATE roundtrip soundness, universal over the input** (PA16 L7, both encoder
    branches): for EVERY `ByteArray`, inflating `compress`'s output — whichever of the
    fixed-Huffman and dynamic-Huffman final blocks the exact bit-cost comparison selected —
    returns exactly the original bytes. Kernel-checked, structural; no oracles. -/
theorem deflate_roundtrip_soundness (data : ByteArray) :
    decompress (compress data) = .ok data := by
  by_cases h : dynPlanBitCost (buildDynPlan (tokenize data)) (tokenize data) <
      fixedBitCost (tokenize data)
  · rw [compress_dynamic_branch data h,
      decompress_dynamicBlock (tokenize data) (tokenize_wf data),
      lz77_roundtrip_soundness data]
  · exact compress_roundtrip_of_fixed_choice data h

end Stdlib.Zlib

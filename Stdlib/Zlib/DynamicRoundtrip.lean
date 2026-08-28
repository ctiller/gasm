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

end Stdlib.Zlib

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
import Stdlib.Zlib.PackageMergeSpec

/-
## PA16 dynamic branch: from package-merge validity to table invertibility, plus the
## §3.2.7 header machinery (L2h) and the dynamic-table instance of the L5 induction.

This file connects the two structural results already landed —
`packageMergeLengths_spec` (L2v: every used symbol coded within `maxBits`, Kraft
inequality) and `buildHuffmanTable_symbol_spec` (L2d: under `kraftOk`, the canonical
table decodes every valid symbol's emitted path back to itself) — and builds the
remaining dynamic-block obligations on top of them.
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Sums over a rectangle commute. -/
theorem sum_map_swap {α β : Type} (A : List α) (B : List β) (f : α → β → Nat) :
    (A.map (fun a => (B.map (f a)).sum)).sum = (B.map (fun b => (A.map (fun a => f a b)).sum)).sum := by
  induction A with
  | nil =>
    rw [List.map_nil, List.sum_nil]
    symm
    apply sum_map_zero
    intro b _
    rw [List.map_nil, List.sum_nil]
  | cons a A ih =>
    rw [List.map_cons, List.sum_cons, ih, ← sum_map_add]
    apply sum_map_congr
    intro b _
    rw [List.map_cons, List.sum_cons]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The canonical block-end at depth `l`, expanded as the histogram sum over `[1, l]`. -/
theorem blockEnd_eq_hist_sum (lengths : Array Nat) (W : Nat) : ∀ l, l ≤ W →
    (startCodeF lengths W l + blCountF lengths W l) * 2 ^ (W - l) =
      ((List.range' 1 l).map (fun j => blCountF lengths W j * 2 ^ (W - j))).sum := by
  intro l
  induction l with
  | zero =>
    intro _
    show (0 + blCountF lengths W 0) * 2 ^ W = _
    rw [blCountF_zero]
    simp
  | succ l ih =>
    intro hle
    rw [List.range'_1_concat, List.map_append, List.sum_append, ← ih (by omega)]
    show (startCodeF lengths W (l + 1) + blCountF lengths W (l + 1)) * 2 ^ (W - (l + 1)) = _
    show ((startCodeF lengths W l + blCountF lengths W l) * 2 + blCountF lengths W (l + 1))
        * 2 ^ (W - (l + 1)) = _
    have hsplit : (2 : Nat) ^ (W - l) = 2 * 2 ^ (W - (l + 1)) := by
      rw [show W - l = (W - (l + 1)) + 1 from by omega, Nat.pow_succ]
      omega
    have hlast : (([1 + l] : List Nat).map (fun j => blCountF lengths W j * 2 ^ (W - j))).sum
        = blCountF lengths W (1 + l) * 2 ^ (W - (1 + l)) := by
      simp
    rw [hlast, Nat.add_mul, hsplit]
    have e1 : 1 + l = l + 1 := by omega
    rw [e1]
    have e2 : (startCodeF lengths W l + blCountF lengths W l) * 2 * 2 ^ (W - (l + 1))
        = (startCodeF lengths W l + blCountF lengths W l) * (2 * 2 ^ (W - (l + 1))) := by
      rw [Nat.mul_assoc]
    omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The histogram Kraft sum regrouped per symbol. -/
theorem hist_sum_eq_symbol_sum (lengths : Array Nat) (W : Nat) :
    ((List.range' 1 W).map (fun j => blCountF lengths W j * 2 ^ (W - j))).sum =
      ((List.range lengths.size).map (fun s =>
        if 1 ≤ lengths[s]! ∧ lengths[s]! ≤ W then 2 ^ (W - lengths[s]!) else 0)).sum := by
  have hterm : ∀ j, 1 ≤ j → j ≤ W → blCountF lengths W j * 2 ^ (W - j) =
      ((List.range lengths.size).map (fun s =>
        if lengths[s]! == j then 2 ^ (W - j) else 0)).sum := by
    intro j h1 h2
    unfold blCountF
    rw [if_pos ⟨h1, h2⟩, ← sum_map_ite_const (fun s => lengths[s]! == j) (2 ^ (W - j))]
  have hstep1 : ((List.range' 1 W).map (fun j => blCountF lengths W j * 2 ^ (W - j))).sum =
      ((List.range' 1 W).map (fun j => ((List.range lengths.size).map (fun s =>
        if lengths[s]! == j then 2 ^ (W - j) else 0)).sum)).sum := by
    apply sum_map_congr
    intro j hj
    have hj' := List.mem_range'_1.mp hj
    exact hterm j (by omega) (by omega)
  rw [hstep1, sum_map_swap]
  apply sum_map_congr
  intro s _
  by_cases hv : 1 ≤ lengths[s]! ∧ lengths[s]! ≤ W
  · rw [if_pos hv]
    have hinner : ∀ j : Nat, (if lengths[s]! == j then 2 ^ (W - j) else 0) =
        (if j = lengths[s]! then 2 ^ (W - j) else 0) := by
      intro j
      by_cases hj : j = lengths[s]!
      · rw [if_pos hj, if_pos (beq_iff_eq.mpr hj.symm)]
      · rw [if_neg hj, if_neg (fun hcon => hj (eq_of_beq hcon).symm)]
    rw [sum_map_congr _ _ _ (fun j _ => hinner j)]
    exact sum_map_delta_range' (fun j => 2 ^ (W - j)) W lengths[s]! hv.1 hv.2
  · rw [if_neg hv]
    apply sum_map_zero
    intro j hj
    have hj' := List.mem_range'_1.mp hj
    rw [if_neg]
    intro hcon
    have := eq_of_beq hcon
    omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- **The L2v → L2d bridge**: a per-symbol Kraft sum within budget, with all lengths within
    `W`, establishes the compact `kraftOk` bound the canonical-table specification runs on. -/
theorem kraftOk_of_symbol_sum (lengths : Array Nat) (W : Nat)
    (hbnd : ∀ s, s < lengths.size → lengths[s]! ≤ W)
    (hsum : ((List.range lengths.size).map (fun s =>
      if 1 ≤ lengths[s]! then 2 ^ (W - lengths[s]!) else 0)).sum ≤ 2 ^ W) :
    kraftOk lengths W := by
  unfold kraftOk
  have h1 := blockEnd_eq_hist_sum lengths W W (Nat.le_refl W)
  have h2 := hist_sum_eq_symbol_sum lengths W
  have h3 : ((List.range lengths.size).map (fun s =>
      if 1 ≤ lengths[s]! ∧ lengths[s]! ≤ W then 2 ^ (W - lengths[s]!) else 0)).sum =
      ((List.range lengths.size).map (fun s =>
        if 1 ≤ lengths[s]! then 2 ^ (W - lengths[s]!) else 0)).sum := by
    apply sum_map_congr
    intro s hs
    have hbs := hbnd s (List.mem_range.mp hs)
    by_cases hv : 1 ≤ lengths[s]!
    · rw [if_pos ⟨hv, hbs⟩, if_pos hv]
    · rw [if_neg (fun hcon => hv hcon.1), if_neg hv]
  have hWW : W - W = 0 := by omega
  have h4 : (startCodeF lengths W W + blCountF lengths W W) * 2 ^ (W - W)
      = startCodeF lengths W W + blCountF lengths W W := by
    rw [hWW]
    simp
  rw [← h4, h1, h2, h3]
  exact hsum

/-
## Canonical-code transfer across get!-pointwise-equal length arrays, and the per-symbol
## emit/decode lemmas for dynamically built tables.

The encoder builds its tables from the full 286/30 slot length arrays; the decoder
rebuilds them from the transmitted, trailing-zero-trimmed arrays. Both are
`buildHuffmanTable` on arrays that agree under `get!` at every index (out-of-bounds reads
are 0, and the trimmed tail is all zeros), and every canonical quantity — histogram,
starting codes, ranks, codes — depends only on the `get!` view.
-/

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Prefix population counts stabilize once past the array. -/
theorem cntP_stable (X : Array Nat) (l : Nat) (hl : 1 ≤ l) : ∀ (d : Nat),
    cntP X l (X.size + d) = cntP X l X.size := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    have hoob : ¬ X[X.size + d]! = l := by
      rw [getElem!_oob X _ (by omega)]
      simp [default]
      omega
    rw [show X.size + (d + 1) = (X.size + d) + 1 from by omega, cntP_succ_ne hoob, ih]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The in-range histogram reads through any window covering the array. -/
theorem blCountF_eq_cntP_of_le (X : Array Nat) (W l M : Nat) (h1 : 1 ≤ l) (h2 : l ≤ W)
    (hM : X.size ≤ M) : blCountF X W l = cntP X l M := by
  unfold blCountF
  rw [if_pos ⟨h1, h2⟩]
  show cntP X l X.size = cntP X l M
  rw [show M = X.size + (M - X.size) from by omega, cntP_stable X l h1]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `get!`-pointwise-equal arrays have identical histograms. -/
theorem blCountF_transfer {A B : Array Nat} (W : Nat) (hpt : ∀ i : Nat, A[i]! = B[i]!) :
    ∀ l, blCountF A W l = blCountF B W l := by
  intro l
  by_cases hv : 1 ≤ l ∧ l ≤ W
  · have hM : A.size ≤ A.size + B.size := by omega
    have hM' : B.size ≤ A.size + B.size := by omega
    rw [blCountF_eq_cntP_of_le A W l _ hv.1 hv.2 hM,
      blCountF_eq_cntP_of_le B W l _ hv.1 hv.2 hM']
    unfold cntP
    apply List.countP_congr
    intro x _
    rw [hpt x]
  · unfold blCountF
    rw [if_neg hv, if_neg hv]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `get!`-pointwise-equal arrays have identical starting codes. -/
theorem startCodeF_transfer {A B : Array Nat} (W : Nat) (hpt : ∀ i : Nat, A[i]! = B[i]!) :
    ∀ l, startCodeF A W l = startCodeF B W l := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show (startCodeF A W l + blCountF A W l) * 2 = (startCodeF B W l + blCountF B W l) * 2
    rw [ih, blCountF_transfer W hpt l]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `get!`-pointwise-equal arrays assign identical canonical codes. -/
theorem canonicalCode_transfer {A B : Array Nat} (W : Nat) (hpt : ∀ i : Nat, A[i]! = B[i]!)
    (s : Nat) : canonicalCode A W s = canonicalCode B W s := by
  unfold canonicalCode rankF
  rw [hpt s, startCodeF_transfer W hpt]
  congr 1
  apply List.countP_congr
  intro x _
  rw [hpt x]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `get!`-pointwise-equal arrays agree on the Kraft bound. -/
theorem kraftOk_transfer {A B : Array Nat} (W : Nat) (hpt : ∀ i : Nat, A[i]! = B[i]!)
    (hk : kraftOk A W) : kraftOk B W := by
  unfold kraftOk at hk ⊢
  rw [← startCodeF_transfer W hpt, ← blCountF_transfer W hpt]
  exact hk

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Emitting one symbol under a canonically built table appends exactly the canonical
    code's MSB-first path, preserving the writer invariant. -/
theorem writerBits_emitHuffSymbol_canonical (lengths : Array Nat) (W : Nat) (hW : W ≤ 15)
    (hk : kraftOk lengths W) {sym : Nat} (hpos : 0 < lengths[sym]!)
    (hle : lengths[sym]! ≤ W) (w : BitWriter)
    (hbuf : w.bitBuf.toNat < 2 ^ w.bitCount) (hcnt : w.bitCount < 8) :
    writerBits (emitHuffSymbol w (buildHuffmanTable lengths W) sym) =
      writerBits w ++ codeBits (canonicalCode lengths W sym) lengths[sym]! ∧
    (emitHuffSymbol w (buildHuffmanTable lengths W) sym).bitCount < 8 ∧
    (emitHuffSymbol w (buildHuffmanTable lengths W) sym).bitBuf.toNat <
      2 ^ (emitHuffSymbol w (buildHuffmanTable lengths W) sym).bitCount := by
  have hspec := buildHuffmanTable_symbol_spec lengths W hk ⟨hpos, hle⟩
  have h := writerBits_emitHuffSymbol w (buildHuffmanTable lengths W) sym
    (canonicalCode lengths W sym) lengths[sym]! hspec.1 (by omega)
    (reverseBits_lt _ _) hbuf hcnt
  refine ⟨?_, h.2.1, h.2.2⟩
  rw [h.1, symbolBits_eq _ _ _ _ hspec.1, natBits_reverseBits]

/- REF: docs/STDLIB_ZLIB.md#32-fixed-huffman-tables-rfc-1951-326 -/
/-- Decoding one canonical code path under a table built from a `get!`-pointwise-equal
    length array recovers the symbol, consuming exactly the path. -/
theorem decodeHuffmanSymbol_canonical (A B : Array Nat) (W : Nat)
    (hpt : ∀ i : Nat, A[i]! = B[i]!) (hk : kraftOk A W) {sym : Nat}
    (hpos : 0 < A[sym]!) (hle : A[sym]! ≤ W) (r : BitReader) (rest : List Bool)
    (hbits : readerBits r = codeBits (canonicalCode A W sym) A[sym]! ++ rest)
    (hinv : r.bitBuf.toNat < 2 ^ r.bitCount) (hcnt : r.bitCount < 8) :
    ∃ r', decodeHuffmanSymbol r (buildHuffmanTable B W) = .ok (r', sym) ∧
      readerBits r' = rest ∧
      r'.bitBuf.toNat < 2 ^ r'.bitCount ∧ r'.bitCount < 8 ∧ r'.bytes = r.bytes := by
  have hkB : kraftOk B W := kraftOk_transfer W hpt hk
  have hvB : validLen B W sym := by
    unfold validLen
    rw [← hpt sym]
    exact ⟨hpos, hle⟩
  have hspecB := buildHuffmanTable_symbol_spec B W hkB hvB
  have hpath : codeBits (canonicalCode A W sym) A[sym]! =
      codeBits (canonicalCode B W sym) B[sym]! := by
    rw [canonicalCode_transfer W hpt, hpt sym]
  rw [hpath] at hbits
  exact decodeHuffmanSymbol_spec (buildHuffmanTable B W) _ sym r rest hspecB.2 hbits hinv hcnt

/-
## `padFrequencies`: at least two nonzero entries, pointwise-monotone, size-preserving.
-/

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `countP` as an indicator sum. -/
theorem countP_eq_indicator_sum {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = (l.map (fun x => if p x then 1 else 0)).sum := by
  rw [sum_map_ite_const p 1]
  omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Setting a zero cell to 1 raises the nonzero population by exactly one. -/
theorem countP_pos_set_incr (f : Array Nat) (N a : Nat) (haN : a < N) (hsz : f.size = N)
    (h0 : f[a]! = 0) :
    (List.range N).countP (fun s => decide (0 < (f.set! a 1)[s]!)) =
      (List.range N).countP (fun s => decide (0 < f[s]!)) + 1 := by
  rw [countP_eq_indicator_sum, countP_eq_indicator_sum]
  have hpt : ∀ s : Nat, (if decide (0 < (f.set! a 1)[s]!) then 1 else 0) =
      (if decide (0 < f[s]!) then 1 else 0) + (if s = a then 1 else 0) := by
    intro s
    by_cases hsa : s = a
    · subst hsa
      rw [getElem!_set!_eq _ _ _ (by omega), h0]
      simp
    · rw [getElem!_set!_ne _ _ _ _ (fun h => hsa h.symm), if_neg hsa]
      omega
  rw [sum_map_congr _ _ _ (fun s _ => hpt s), sum_map_add,
    sum_map_delta_range (fun _ => 1) N a haN]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The counting pass of `padFrequencies` computes the nonzero population. -/
theorem pad_count_fold (freqs : Array Nat) : ∀ (l : List Nat) (b : Nat),
    l.foldl (fun b a => if freqs[a]! > 0 then b + 1 else b) b =
      b + l.countP (fun a => decide (0 < freqs[a]!)) := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
    intro b
    rw [List.foldl_cons, List.countP_cons]
    by_cases h : freqs[a]! > 0
    · rw [if_pos h, ih, if_pos (by simpa using h)]
      omega
    · rw [if_neg h, ih, if_neg (by simpa using h)]
      omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The padding pass invariant: the running count tracks the array's nonzero population,
    cells only ever grow (zeros to 1), and any index processed while the count finishes
    below 2 ends up nonzero. -/
theorem pad_fill_fold (freqs : Array Nat) : ∀ (l : List Nat) (f : Array Nat) (nz : Nat),
    f.size = freqs.size →
    nz = (List.range freqs.size).countP (fun s => decide (0 < f[s]!)) →
    (∀ a ∈ l, a < freqs.size) →
    (l.foldl (fun (b : Array Nat × Nat) a =>
        if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
        else (b.1, b.2)) (f, nz)).1.size = freqs.size ∧
    (l.foldl (fun (b : Array Nat × Nat) a =>
        if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
        else (b.1, b.2)) (f, nz)).2 =
      (List.range freqs.size).countP (fun s => decide (0 <
        (l.foldl (fun (b : Array Nat × Nat) a =>
          if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
          else (b.1, b.2)) (f, nz)).1[s]!)) ∧
    (∀ i : Nat, f[i]! ≤
      (l.foldl (fun (b : Array Nat × Nat) a =>
        if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
        else (b.1, b.2)) (f, nz)).1[i]!) ∧
    (∀ a ∈ l,
      (l.foldl (fun (b : Array Nat × Nat) a =>
        if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
        else (b.1, b.2)) (f, nz)).2 < 2 →
      0 < (l.foldl (fun (b : Array Nat × Nat) a =>
        if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
        else (b.1, b.2)) (f, nz)).1[a]!) := by
  intro l
  induction l with
  | nil =>
    intro f nz hsz hnz _
    exact ⟨hsz, hnz, fun i => Nat.le_refl _, fun a ha => absurd ha (by simp)⟩
  | cons a l ih =>
    intro f nz hsz hnz hmem
    have haN : a < freqs.size := hmem a (by simp)
    rw [List.foldl_cons]
    by_cases hcond : (decide (nz < 2) && f[a]! == 0) = true
    · -- the cell is zero and the count is small: set it
      rw [if_pos (by exact hcond)]
      dsimp only
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      have hnz' : nz + 1 = (List.range freqs.size).countP
          (fun s => decide (0 < (f.set! a 1)[s]!)) := by
        rw [countP_pos_set_incr f freqs.size a haN hsz hcond.2, ← hnz]
      have hrec := ih (f.set! a 1) (nz + 1)
        (by rw [size_set!, hsz]) hnz' (fun x hx => hmem x (by simp [hx]))
      refine ⟨hrec.1, hrec.2.1, ?_, ?_⟩
      · intro i
        have hstep : f[i]! ≤ (f.set! a 1)[i]! := by
          by_cases hia : a = i
          · subst hia
            rw [getElem!_set!_eq _ _ _ (by omega), hcond.2]
            omega
          · rw [getElem!_set!_ne _ _ _ _ hia]
            omega
        exact Nat.le_trans hstep (hrec.2.2.1 i)
      · intro x hx hlt
        rcases List.mem_cons.mp hx with hxa | hxl
        · subst hxa
          have h1 : (f.set! x 1)[x]! = 1 := getElem!_set!_eq _ _ _ (by omega)
          have h2 := hrec.2.2.1 x
          omega
        · exact hrec.2.2.2 x hxl hlt
    · -- skip
      rw [if_neg (by exact hcond)]
      dsimp only
      have hrec := ih f nz hsz hnz (fun x hx => hmem x (by simp [hx]))
      refine ⟨hrec.1, hrec.2.1, hrec.2.2.1, ?_⟩
      intro x hx hlt
      rcases List.mem_cons.mp hx with hxa | hxl
      · subst hxa
        -- the cell was either already nonzero, or the count was already ≥ 2
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
        by_cases hzero : f[x]! = 0
        · -- then nz ≥ 2, and the count only grows — contradiction with hlt
          have hnz2 : 2 ≤ nz := by
            rcases Nat.lt_or_ge nz 2 with h | h
            · exact absurd ⟨h, hzero⟩ hcond
            · exact h
          -- final count ≥ nz: counts only grow along the fold
          exfalso
          have hgrow : ∀ (l' : List Nat) (f' : Array Nat) (nz' : Nat), nz' ≤
              (l'.foldl (fun (b : Array Nat × Nat) a =>
                if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
                else (b.1, b.2)) (f', nz')).2 := by
            intro l'
            induction l' with
            | nil => intro f' nz'; exact Nat.le_refl _
            | cons y l' ihy =>
              intro f' nz'
              rw [List.foldl_cons]
              dsimp only
              by_cases hc : (decide (nz' < 2) && f'[y]! == 0) = true
              · rw [if_pos hc]
                have h := ihy (f'.set! y 1) (nz' + 1)
                omega
              · rw [if_neg hc]
                exact ihy f' nz'
          have hg := hgrow l f nz
          omega
        · -- already nonzero: monotone
          have h2 := hrec.2.2.1 x
          omega
      · exact hrec.2.2.2 x hxl hlt

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- **`padFrequencies` specification**: size preserved, pointwise never decreased, and —
    with an alphabet of at least two symbols — at least two nonzero entries. -/
theorem padFrequencies_spec (freqs : Array Nat) (h2 : 2 ≤ freqs.size) :
    (padFrequencies freqs).size = freqs.size ∧
    (∀ i : Nat, freqs[i]! ≤ (padFrequencies freqs)[i]!) ∧
    2 ≤ (List.range freqs.size).countP (fun s => decide (0 < (padFrequencies freqs)[s]!)) := by
  have ite_pure_yield : ∀ {σ : Type} {c : Prop} [Decidable c] (a b : σ),
      (if c then (pure (ForInStep.yield a) : Id (ForInStep σ)) else pure (ForInStep.yield b)) =
        pure (ForInStep.yield (if c then a else b)) := by
    intro σ c _ a b
    split <;> rfl
  have heq : padFrequencies freqs =
      ((List.range' 0 freqs.size).foldl (fun (b : Array Nat × Nat) a =>
        if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
        else (b.1, b.2))
        (freqs, (List.range' 0 freqs.size).foldl
          (fun b a => if freqs[a]! > 0 then b + 1 else b) 0)).1 := by
    conv => lhs; unfold padFrequencies
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ite_pure_yield,
      List.forIn_pure_yield_eq_foldl, Id.run, pure_bind, Nat.sub_zero, Nat.div_one,
      Nat.add_sub_cancel]
    rfl
  have hnz0 : (List.range' 0 freqs.size).foldl
      (fun b a => if freqs[a]! > 0 then b + 1 else b) 0 =
      (List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)) := by
    rw [pad_count_fold freqs _ 0, ← List.range_eq_range']
    omega
  have hmem : ∀ a ∈ List.range' 0 freqs.size, a < freqs.size := by
    intro a ha
    rw [← List.range_eq_range'] at ha
    exact List.mem_range.mp ha
  have hfold := pad_fill_fold freqs (List.range' 0 freqs.size) freqs
    ((List.range freqs.size).countP (fun s => decide (0 < freqs[s]!))) rfl rfl hmem
  rw [heq, hnz0]
  refine ⟨hfold.1, hfold.2.2.1, ?_⟩
  -- if the final count were below 2, every index would be nonzero — forcing count = size ≥ 2
  rw [← hfold.2.1]
  rcases Nat.lt_or_ge ((List.range' 0 freqs.size).foldl (fun (b : Array Nat × Nat) a =>
      if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
      else (b.1, b.2))
      (freqs, (List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)))).2 2
    with hlt | hge
  · exfalso
    have hall : ∀ a ∈ List.range freqs.size, (fun s => decide (0 <
        ((List.range' 0 freqs.size).foldl (fun (b : Array Nat × Nat) a =>
          if (decide (b.2 < 2) && b.1[a]! == 0) = true then (b.1.set! a 1, b.2 + 1)
          else (b.1, b.2))
          (freqs, (List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)))).1[s]!)) a
        = true := by
      intro a ha
      have := hfold.2.2.2 a (by rw [← List.range_eq_range']; exact ha) hlt
      simpa using this
    have hcnt := List.countP_eq_length.mpr hall
    rw [List.length_range] at hcnt
    rw [hfold.2.1] at hlt
    omega
  · exact hge



end Stdlib.Zlib

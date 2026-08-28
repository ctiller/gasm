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



/-
## L2h, encoder side: the §3.2.7 RLE token stream expands back to exactly the code-length
## sequence it was built from.

`rleOk ts done full` is the decode-step semantics of the code-length alphabet, relative to
an already-reconstructed prefix `done`: symbols 0–15 append themselves, 16 repeats the last
reconstructed value 3–6 times (2 extra bits), 17/18 append zero runs (3 and 7 extra bits) —
ending exactly at `full`. Each arm carries the extra-bits width and range the writer needs.
-/

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Step semantics of the RFC 1951 §3.2.7 code-length token stream, from a reconstructed
    prefix `done` to the full sequence `full`. -/
def rleOk : List (Nat × Nat × Nat) → List Nat → List Nat → Prop
  | [], done, full => done = full
  | (sym, eb, ev) :: ts, done, full =>
      (sym ≤ 15 ∧ eb = 0 ∧ ev = 0 ∧ rleOk ts (done ++ [sym]) full) ∨
      (sym = 16 ∧ eb = 2 ∧ ev < 4 ∧ done ≠ [] ∧
        rleOk ts (done ++ List.replicate (ev + 3) (done.getLastD 0)) full) ∨
      (sym = 17 ∧ eb = 3 ∧ ev < 8 ∧ rleOk ts (done ++ List.replicate (ev + 3) 0) full) ∨
      (sym = 18 ∧ eb = 7 ∧ ev < 128 ∧ rleOk ts (done ++ List.replicate (ev + 11) 0) full)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Concatenating replicates of one value. -/
theorem replicate_append_replicate {α : Type} (v : α) (n m : Nat) :
    List.replicate n v ++ List.replicate m v = List.replicate (n + m) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, ih, show n + 1 + m = (n + m) + 1 from by omega,
      List.replicate_succ]

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The default-last of an append with nonempty right part. -/
theorem getLastD_append_right {α : Type} (xs : List α) {ys : List α} (hne : ys ≠ [])
    (d : α) : (xs ++ ys).getLastD d = ys.getLastD d := by
  match ys, hne with
  | y :: ys', _ =>
    induction ys' generalizing xs y with
    | nil => rw [show xs ++ [y] = xs ++ [y] from rfl, List.getLastD_concat]; rfl
    | cons z ys'' ih =>
      have h1 : xs ++ (y :: z :: ys'') = (xs ++ [y]) ++ (z :: ys'') := by simp
      rw [h1, ih (xs ++ [y]) z (by simp)]
      show (z :: ys'').getLastD d = (y :: z :: ys'').getLastD d
      rfl

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The default-last of a nonempty replicate. -/
theorem getLastD_replicate {α : Type} (v d : α) (n : Nat) (h : 0 < n) :
    (List.replicate n v).getLastD d = v := by
  match n, h with
  | m + 1, _ =>
    rw [List.replicate_succ']
    exact List.getLastD_concat

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Every `rleOk` token is in the code-length alphabet with in-range extra bits. -/
theorem rleOk_bounds : ∀ (ts : List (Nat × Nat × Nat)) (done full : List Nat),
    rleOk ts done full → ∀ t ∈ ts, t.1 ≤ 18 ∧ t.2.1 ≤ 7 ∧ t.2.2 < 2 ^ t.2.1 := by
  intro ts
  induction ts with
  | nil => intro done full _ t ht; simp at ht
  | cons hd ts ih =>
    intro done full hok t ht
    obtain ⟨sym, eb, ev⟩ := hd
    rcases List.mem_cons.mp ht with hta | htl
    · subst hta
      rcases hok with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _, _⟩ | ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩ <;>
        subst h2
      · subst h3
        exact ⟨by omega, by show (0 : Nat) ≤ 7; omega, by show (0 : Nat) < 2 ^ 0; omega⟩
      · exact ⟨by omega, by show (2 : Nat) ≤ 7; omega, by show ev < 2 ^ 2; omega⟩
      · exact ⟨by omega, by show (3 : Nat) ≤ 7; omega, by show ev < 2 ^ 3; omega⟩
      · exact ⟨by omega, by show (7 : Nat) ≤ 7; omega, by show ev < 2 ^ 7; omega⟩
    · rcases hok with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
        exact ih _ full h t htl

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `rleOk` streams only ever extend the prefix; a nonempty stream extends it strictly. -/
theorem rleOk_length : ∀ (ts : List (Nat × Nat × Nat)) (done full : List Nat),
    rleOk ts done full → done.length ≤ full.length ∧ (ts ≠ [] → done.length < full.length) := by
  intro ts
  induction ts with
  | nil =>
    intro done full hok
    rw [show done = full from hok]
    exact ⟨Nat.le_refl _, fun h => absurd rfl h⟩
  | cons hd ts ih =>
    intro done full hok
    obtain ⟨sym, eb, ev⟩ := hd
    have hstep : ∃ ext : List Nat, ext ≠ [] ∧ rleOk ts (done ++ ext) full := by
      rcases hok with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
      · exact ⟨[sym], by simp, h⟩
      · exact ⟨List.replicate (ev + 3) (done.getLastD 0), by simp, h⟩
      · exact ⟨List.replicate (ev + 3) 0, by simp, h⟩
      · exact ⟨List.replicate (ev + 11) 0, by simp, h⟩
    obtain ⟨ext, hne, hrec⟩ := hstep
    have h1 := (ih _ full hrec).1
    rw [List.length_append] at h1
    have h2 : 0 < ext.length := List.length_pos_iff.mpr hne
    exact ⟨by omega, fun _ => by omega⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A run of bare literal-value tokens reconstructs its replicate. -/
theorem rleOk_literals (v : Nat) (hv : v ≤ 15) : ∀ (cnt : Nat) (done full : List Nat)
    (ts' : List (Nat × Nat × Nat)),
    rleOk ts' (done ++ List.replicate cnt v) full →
    rleOk (List.replicate cnt (v, 0, 0) ++ ts') done full := by
  intro cnt
  induction cnt with
  | zero =>
    intro done full ts' h
    simpa using h
  | succ cnt ih =>
    intro done full ts' h
    rw [List.replicate_succ, List.cons_append]
    show rleOk ((v, 0, 0) :: (List.replicate cnt (v, 0, 0) ++ ts')) done full
    left
    refine ⟨hv, rfl, rfl, ?_⟩
    apply ih
    have hrepl : ([v] : List Nat) ++ List.replicate cnt v = List.replicate (cnt + 1) v := by
      rw [List.replicate_succ]
      rfl
    rw [List.append_assoc, hrepl]
    exact h

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `encodeRepeatRun` reconstructs its repeat count, provided the prefix ends in the
    repeated value. -/
theorem encodeRepeatRun_ok (v : Nat) (hv : v ≤ 15) : ∀ (cnt : Nat) (done full : List Nat)
    (ts' : List (Nat × Nat × Nat)),
    done ≠ [] → done.getLastD 0 = v →
    rleOk ts' (done ++ List.replicate cnt v) full →
    rleOk (encodeRepeatRun v cnt ++ ts') done full := by
  intro cnt
  induction cnt using encodeRepeatRun.induct with
  | case1 cnt h3 k ih =>
    intro done full ts' hne hlast hcont
    rw [encodeRepeatRun, if_pos h3]
    show rleOk ((16, 2, min cnt 6 - 3) :: (encodeRepeatRun v (cnt - min cnt 6) ++ ts'))
      done full
    right; left
    refine ⟨rfl, rfl, by omega, hne, ?_⟩
    rw [hlast, show min cnt 6 - 3 + 3 = min cnt 6 from by omega]
    apply ih
    · have hlen : 0 < (done ++ List.replicate (min cnt 6) v).length := by
        rw [List.length_append]
        have := List.length_pos_iff.mpr hne
        omega
      exact List.length_pos_iff.mp hlen
    · rw [getLastD_append_right done (by simp; omega : List.replicate (min cnt 6) v ≠ []) 0,
        getLastD_replicate v 0 (min cnt 6) (by omega)]
    · rw [List.append_assoc, replicate_append_replicate,
        show min cnt 6 + (cnt - min cnt 6) = cnt from by omega]
      exact hcont
  | case2 cnt h3 =>
    intro done full ts' hne hlast hcont
    rw [encodeRepeatRun, if_neg h3]
    exact rleOk_literals v hv cnt done full ts' hcont

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `encodeZeroRun` reconstructs its zero run. -/
theorem encodeZeroRun_ok : ∀ (cnt : Nat) (done full : List Nat)
    (ts' : List (Nat × Nat × Nat)),
    rleOk ts' (done ++ List.replicate cnt 0) full →
    rleOk (encodeZeroRun cnt ++ ts') done full := by
  intro cnt
  induction cnt using encodeZeroRun.induct with
  | case1 cnt h11 k ih =>
    intro done full ts' hcont
    rw [encodeZeroRun, if_pos h11]
    show rleOk ((18, 7, min cnt 138 - 11) :: (encodeZeroRun (cnt - min cnt 138) ++ ts'))
      done full
    right; right; right
    refine ⟨rfl, rfl, by omega, ?_⟩
    rw [show min cnt 138 - 11 + 11 = min cnt 138 from by omega]
    apply ih
    rw [List.append_assoc, replicate_append_replicate,
      show min cnt 138 + (cnt - min cnt 138) = cnt from by omega]
    exact hcont
  | case2 cnt h11 h3 =>
    intro done full ts' hcont
    rw [encodeZeroRun, if_neg h11, if_pos h3]
    show rleOk ((17, 3, cnt - 3) :: ts') done full
    right; right; left
    refine ⟨rfl, rfl, by omega, ?_⟩
    rw [show cnt - 3 + 3 = cnt from by omega]
    exact hcont
  | case3 cnt h11 h3 =>
    intro done full ts' hcont
    rw [encodeZeroRun, if_neg h11, if_neg h3]
    exact rleOk_literals 0 (by omega) cnt done full ts' hcont

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- One run's token block reconstructs the run, chaining into any continuation. -/
theorem rleRun_ok (v cnt : Nat) (hv : v ≤ 15) (hc : 1 ≤ cnt) (done full : List Nat)
    (ts' : List (Nat × Nat × Nat))
    (hcont : rleOk ts' (done ++ List.replicate cnt v) full) :
    rleOk ((if v == 0 then encodeZeroRun cnt
            else (v, 0, 0) :: encodeRepeatRun v (cnt - 1)) ++ ts') done full := by
  by_cases hz : v = 0
  · subst hz
    rw [if_pos (show ((0 : Nat) == 0) = true from rfl)]
    exact encodeZeroRun_ok cnt done full ts' hcont
  · rw [if_neg (by simpa using hz), List.cons_append]
    show rleOk ((v, 0, 0) :: (encodeRepeatRun v (cnt - 1) ++ ts')) done full
    left
    refine ⟨hv, rfl, rfl, ?_⟩
    apply encodeRepeatRun_ok v hv (cnt - 1) (done ++ [v]) full ts'
    · simp
    · exact List.getLastD_concat
    · have hrepl : ([v] : List Nat) ++ List.replicate (cnt - 1) v = List.replicate cnt v := by
        rw [show cnt = (cnt - 1) + 1 from by omega, List.replicate_succ]
        rfl
      rw [List.append_assoc, hrepl]
      exact hcont

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The run decomposition worker: its runs expand to the remaining input. -/
theorem runLengthsAux_ok (full L₀ : List Nat) :
    ∀ (xs : List Nat) (v cnt : Nat) (done : List Nat),
    v ≤ 15 → (∀ u ∈ xs, u ≤ 15) → 1 ≤ cnt →
    done ++ List.replicate cnt v ++ xs = full →
    rleOk ((runLengthsAux v cnt xs).flatMap (fun r =>
      if r.1 == 0 then encodeZeroRun r.2
      else (r.1, 0, 0) :: encodeRepeatRun r.1 (r.2 - 1))) done full := by
  intro xs
  induction xs with
  | nil =>
    intro v cnt done hv _ hc htot
    show rleOk (((v, cnt) :: []).flatMap _) done full
    rw [List.flatMap_cons, List.flatMap_nil]
    dsimp only
    apply rleRun_ok v cnt hv hc done full [] _
    show done ++ List.replicate cnt v = full
    rw [← htot]
    simp
  | cons x xs ih =>
    intro v cnt done hv hxs hc htot
    show rleOk ((runLengthsAux v cnt (x :: xs)).flatMap _) done full
    rw [runLengthsAux]
    by_cases hxv : x = v
    · rw [if_pos (by simpa using hxv)]
      apply ih v (cnt + 1) done hv (fun u hu => hxs u (by simp [hu])) (by omega)
      rw [← htot, show List.replicate (cnt + 1) v = List.replicate cnt v ++ [v] from
        List.replicate_succ']
      subst hxv
      simp
    · rw [if_neg (by simpa using hxv), List.flatMap_cons]
      dsimp only
      apply rleRun_ok v cnt hv hc done full _
      apply ih x 1 (done ++ List.replicate cnt v) (hxs x (by simp))
        (fun u hu => hxs u (by simp [hu])) (by omega)
      rw [← htot]
      simp

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **L2h, encoder side**: the RLE stream `rleCodeLengths L` reconstructs exactly `L`. -/
theorem rleCodeLengths_ok (L : List Nat) (hval : ∀ v ∈ L, v ≤ 15) :
    rleOk (rleCodeLengths L) [] L := by
  unfold rleCodeLengths runLengths
  cases L with
  | nil => rfl
  | cons x xs =>
    have h := runLengthsAux_ok (x :: xs) (x :: xs) xs x 1 []
      (hval x (by simp)) (fun u hu => hval u (by simp [hu])) (by omega)
      (by simp)
    exact h

/-
## `buildDynPlan` component characterizations: token frequencies, trimmed sizes, the
## code-length-alphabet frequency count, and the HCLEN scan.
-/

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Out-of-bounds `set!` is a no-op. -/
theorem set!_oob {α : Type} (arr : Array α) (j : Nat) (v : α) (h : ¬ j < arr.size) :
    arr.set! j v = arr := by
  simp [Array.set!, Array.setIfInBounds]
  omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A cell never shrinks under a counting `set!`. -/
theorem getElem!_set!_incr (arr : Array Nat) (i j : Nat) :
    arr[i]! ≤ (arr.set! j (arr[j]! + 1))[i]! := by
  by_cases hj : j < arr.size
  · by_cases hij : j = i
    · subst hij
      rw [getElem!_set!_eq _ _ _ hj]
      omega
    · rw [getElem!_set!_ne _ _ _ _ hij]
      omega
  · rw [set!_oob _ _ _ hj]
    omega

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The token-frequency accumulation step. -/
def tfStep (s : Array Nat × Array Nat) (t : LZToken) : Array Nat × Array Nat :=
  match t with
  | .lit b => (s.1.set! b.toNat (s.1[b.toNat]! + 1), s.2)
  | .ref len dist =>
      (s.1.set! (encodeLength len).1 (s.1[(encodeLength len).1]! + 1),
       s.2.set! (encodeDistance dist).1 (s.2[(encodeDistance dist).1]! + 1))

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- A `forIn` whose body always yields is the corresponding `foldl` — stated over an
    abstract body so the rewrite site's own (auto-generated) match never needs restating. -/
theorem forIn_yield_eq_foldl {α σ : Type} (B : α → σ → Id (ForInStep σ)) (g : σ → α → σ)
    (hB : ∀ a s, B a s = pure (ForInStep.yield (g s a))) :
    ∀ (l : List α) (s : σ), (forIn (m := Id) l s B) = pure (l.foldl g s) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [List.forIn_cons, hB]
    simp only [pure_bind]
    exact ih (g s a)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `tokenFrequencies` in `foldl` form. -/
theorem tokenFrequencies_eq (tokens : Array LZToken) :
    tokenFrequencies tokens =
      ((tokens.toList.foldl tfStep (Array.replicate 286 0, Array.replicate 30 0)).1.set! 256
        ((tokens.toList.foldl tfStep (Array.replicate 286 0, Array.replicate 30 0)).1[256]! + 1),
       (tokens.toList.foldl tfStep (Array.replicate 286 0, Array.replicate 30 0)).2) := by
  conv => lhs; unfold tokenFrequencies
  simp only [Id.run, ← Array.forIn_toList]
  rw [forIn_yield_eq_foldl _ tfStep (by intro t s; cases t <;> rfl) tokens.toList]
  simp only [pure_bind]
  rfl

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The frequency fold preserves the two alphabet sizes. -/
theorem tfFold_sizes : ∀ (l : List LZToken) (s : Array Nat × Array Nat),
    (l.foldl tfStep s).1.size = s.1.size ∧ (l.foldl tfStep s).2.size = s.2.size := by
  intro l
  induction l with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons t l ih =>
    intro s
    rw [List.foldl_cons]
    have h := ih (tfStep s t)
    cases t with
    | lit b =>
      rw [h.1, h.2]
      exact ⟨size_set! .., rfl⟩
    | ref len dist =>
      rw [h.1, h.2]
      exact ⟨size_set! .., size_set! ..⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Cells never shrink along the frequency fold. -/
theorem tfFold_mono : ∀ (l : List LZToken) (s : Array Nat × Array Nat) (i : Nat),
    s.1[i]! ≤ (l.foldl tfStep s).1[i]! ∧ s.2[i]! ≤ (l.foldl tfStep s).2[i]! := by
  intro l
  induction l with
  | nil => intro s i; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons t l ih =>
    intro s i
    rw [List.foldl_cons]
    have h := ih (tfStep s t) i
    have hstep : s.1[i]! ≤ (tfStep s t).1[i]! ∧ s.2[i]! ≤ (tfStep s t).2[i]! := by
      cases t with
      | lit b => exact ⟨getElem!_set!_incr .., Nat.le_refl _⟩
      | ref len dist => exact ⟨getElem!_set!_incr .., getElem!_set!_incr ..⟩
    exact ⟨Nat.le_trans hstep.1 h.1, Nat.le_trans hstep.2 h.2⟩

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Every processed token's symbol cells end positive, provided they are in bounds. -/
theorem tfFold_covers : ∀ (l : List LZToken) (s : Array Nat × Array Nat),
    (∀ t ∈ l,
      (∀ b : UInt8, t = .lit b → b.toNat < s.1.size) ∧
      (∀ len dist, t = .ref len dist →
        (encodeLength len).1 < s.1.size ∧ (encodeDistance dist).1 < s.2.size)) →
    ∀ t ∈ l,
      (∀ b : UInt8, t = .lit b → 0 < (l.foldl tfStep s).1[b.toNat]!) ∧
      (∀ len dist, t = .ref len dist →
        0 < (l.foldl tfStep s).1[(encodeLength len).1]! ∧
        0 < (l.foldl tfStep s).2[(encodeDistance dist).1]!) := by
  intro l
  induction l with
  | nil => intro s _ t ht; simp at ht
  | cons t0 l ih =>
    intro s hb t ht
    rw [List.foldl_cons]
    have hsz := tfFold_sizes l (tfStep s t0)
    rcases List.mem_cons.mp ht with hta | htl
    · subst hta
      constructor
      · intro b hb'
        subst hb'
        have hbnd := (hb _ (by simp)).1 b rfl
        have hpos : 0 < (tfStep s (LZToken.lit b)).1[b.toNat]! := by
          show 0 < (s.1.set! b.toNat (s.1[b.toNat]! + 1))[b.toNat]!
          rw [getElem!_set!_eq _ _ _ hbnd]
          omega
        have := (tfFold_mono l (tfStep s (LZToken.lit b)) b.toNat).1
        omega
      · intro len dist hr
        subst hr
        have hbnd := (hb _ (by simp)).2 len dist rfl
        have hpos1 : 0 < (tfStep s (LZToken.ref len dist)).1[(encodeLength len).1]! := by
          show 0 < (s.1.set! (encodeLength len).1 (s.1[(encodeLength len).1]! + 1))[(encodeLength len).1]!
          rw [getElem!_set!_eq _ _ _ hbnd.1]
          omega
        have hpos2 : 0 < (tfStep s (LZToken.ref len dist)).2[(encodeDistance dist).1]! := by
          show 0 < (s.2.set! (encodeDistance dist).1 (s.2[(encodeDistance dist).1]! + 1))[(encodeDistance dist).1]!
          rw [getElem!_set!_eq _ _ _ hbnd.2]
          omega
        have hm1 := (tfFold_mono l (tfStep s (LZToken.ref len dist)) (encodeLength len).1).1
        have hm2 := (tfFold_mono l (tfStep s (LZToken.ref len dist)) (encodeDistance dist).1).2
        exact ⟨by omega, by omega⟩
    · -- later token: sizes shift through the step
      apply ih (tfStep s t0) _ t htl
      intro t' ht'
      have hb' := hb t' (by simp [ht'])
      constructor
      · intro b hb''
        have := hb'.1 b hb''
        cases t0 with
        | lit b0 =>
          show b.toNat < (s.1.set! b0.toNat _).size
          rw [size_set!]
          exact this
        | ref l0 d0 =>
          show b.toNat < (s.1.set! (encodeLength l0).1 _).size
          rw [size_set!]
          exact this
      · intro len dist hr
        have := hb'.2 len dist hr
        cases t0 with
        | lit b0 =>
          refine ⟨?_, ?_⟩
          · show (encodeLength len).1 < (s.1.set! b0.toNat _).size
            rw [size_set!]
            exact this.1
          · exact this.2
        | ref l0 d0 =>
          refine ⟨?_, ?_⟩
          · show (encodeLength len).1 < (s.1.set! (encodeLength l0).1 _).size
            rw [size_set!]
            exact this.1
          · show (encodeDistance dist).1 < (s.2.set! (encodeDistance d0).1 _).size
            rw [size_set!]
            exact this.2

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **`tokenFrequencies` specification**: alphabet sizes, the always-counted end-of-block
    symbol, and positivity for every emitted symbol. -/
theorem tokenFrequencies_spec (tokens : Array LZToken)
    (hok : ∀ t ∈ tokens.toList, tokenRangesOk t) :
    (tokenFrequencies tokens).1.size = 286 ∧
    (tokenFrequencies tokens).2.size = 30 ∧
    0 < (tokenFrequencies tokens).1[256]! ∧
    (∀ b : UInt8, (LZToken.lit b) ∈ tokens.toList →
      0 < (tokenFrequencies tokens).1[b.toNat]!) ∧
    (∀ len dist, (LZToken.ref len dist) ∈ tokens.toList →
      0 < (tokenFrequencies tokens).1[(encodeLength len).1]! ∧
      0 < (tokenFrequencies tokens).2[(encodeDistance dist).1]!) := by
  rw [tokenFrequencies_eq]
  have hsz := tfFold_sizes tokens.toList (Array.replicate 286 0, Array.replicate 30 0)
  rw [Array.size_replicate, Array.size_replicate] at hsz
  have hbnds : ∀ t ∈ tokens.toList,
      (∀ b : UInt8, t = .lit b →
        b.toNat < (Array.replicate 286 (0 : Nat), Array.replicate 30 (0 : Nat)).1.size) ∧
      (∀ len dist, t = .ref len dist →
        (encodeLength len).1 < (Array.replicate 286 (0 : Nat), Array.replicate 30 (0 : Nat)).1.size ∧
        (encodeDistance dist).1 < (Array.replicate 286 (0 : Nat), Array.replicate 30 (0 : Nat)).2.size) := by
    intro t ht
    constructor
    · intro b _
      show b.toNat < (Array.replicate 286 (0 : Nat)).size
      rw [Array.size_replicate]
      have := b.toNat_lt
      omega
    · intro len dist hr
      have hrange := hok t ht
      rw [hr] at hrange
      obtain ⟨h3, h258, h1d, h32768⟩ := hrange
      have hL := encodeLength_spec len (by omega) h3
      have hD := encodeDistance_spec' dist h1d h32768
      constructor
      · show (encodeLength len).1 < (Array.replicate 286 (0 : Nat)).size
        rw [Array.size_replicate]
        omega
      · show (encodeDistance dist).1 < (Array.replicate 30 (0 : Nat)).size
        rw [Array.size_replicate]
        omega
  have hcov := tfFold_covers tokens.toList (Array.replicate 286 0, Array.replicate 30 0) hbnds
  have h256 : 256 < (tokens.toList.foldl tfStep
      (Array.replicate 286 0, Array.replicate 30 0)).1.size := by
    rw [hsz.1]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [size_set!, hsz.1]
  · exact hsz.2
  · dsimp only
    rw [getElem!_set!_eq _ _ _ h256]
    omega
  · intro b hb
    have h := (hcov _ hb).1 b rfl
    dsimp only
    by_cases h256b : (256 : Nat) = b.toNat
    · rw [← h256b, getElem!_set!_eq _ _ _ h256]
      omega
    · rw [getElem!_set!_ne _ _ _ _ h256b]
      exact h
  · intro len dist hr
    have h := (hcov _ hr).2 len dist rfl
    constructor
    · dsimp only
      by_cases h256b : (256 : Nat) = (encodeLength len).1
      · rw [← h256b, getElem!_set!_eq _ _ _ h256]
        omega
      · rw [getElem!_set!_ne _ _ _ _ h256b]
        exact h.1
    · exact h.2

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Trim-scan folds only grow the running bound. -/
theorem trim_fold_ge (g : Nat → Nat) : ∀ (l : List Nat) (n₀ : Nat),
    n₀ ≤ l.foldl (fun n i => if g i > 0 then max n (i + 1) else n) n₀ := by
  intro l
  induction l with
  | nil => intro n₀; exact Nat.le_refl _
  | cons a l ih =>
    intro n₀
    rw [List.foldl_cons]
    by_cases h : g a > 0
    · rw [if_pos h]
      have := ih (max n₀ (a + 1))
      have hle : n₀ ≤ max n₀ (a + 1) := Nat.le_max_left ..
      omega
    · rw [if_neg h]
      exact ih n₀

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Trim-scan folds stay below any bound dominating the seed and all hits. -/
theorem trim_fold_le (g : Nat → Nat) (B : Nat) : ∀ (l : List Nat) (n₀ : Nat),
    n₀ ≤ B → (∀ i ∈ l, i + 1 ≤ B) →
    l.foldl (fun n i => if g i > 0 then max n (i + 1) else n) n₀ ≤ B := by
  intro l
  induction l with
  | nil => intro n₀ h _; exact h
  | cons a l ih =>
    intro n₀ h hall
    rw [List.foldl_cons]
    by_cases hg : g a > 0
    · rw [if_pos hg]
      exact ih _ (by have := hall a (by simp); omega) (fun i hi => hall i (by simp [hi]))
    · rw [if_neg hg]
      exact ih _ h (fun i hi => hall i (by simp [hi]))

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- Trim-scan folds cover every hit. -/
theorem trim_fold_covers (g : Nat → Nat) : ∀ (l : List Nat) (n₀ : Nat) (i : Nat),
    i ∈ l → 0 < g i →
    i + 1 ≤ l.foldl (fun n i => if g i > 0 then max n (i + 1) else n) n₀ := by
  intro l
  induction l with
  | nil => intro n₀ i hi; simp at hi
  | cons a l ih =>
    intro n₀ i hi hg
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hi with hia | hil
    · subst hia
      rw [if_pos hg]
      have h1 := trim_fold_ge g l (max n₀ (i + 1))
      have h2 : i + 1 ≤ max n₀ (i + 1) := Nat.le_max_right ..
      omega
    · by_cases hga : g a > 0
      · rw [if_pos hga]
        exact ih _ i hil hg
      · rw [if_neg hga]
        exact ih _ i hil hg

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- `trimmedSize` in `foldl` form. -/
theorem trimmedSize_eq (arr : Array Nat) (k : Nat) :
    trimmedSize arr k = (List.range' 0 arr.size).foldl
      (fun n i => if arr[i]! > 0 then max n (i + 1) else n) k := by
  have ite_pure_yield : ∀ {c : Prop} [Decidable c] (a b : Nat),
      (if c then (pure (ForInStep.yield a) : Id (ForInStep Nat)) else pure (ForInStep.yield b)) =
        pure (ForInStep.yield (if c then a else b)) := by
    intro c _ a b
    split <;> rfl
  conv => lhs; unfold trimmedSize
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind, Nat.sub_zero, Nat.div_one,
    Nat.add_sub_cancel]
  rfl

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- **`trimmedSize` specification**: floored at `atLeast`, capped by the array size, and
    zero everywhere at or beyond the trim point. -/
theorem trimmedSize_spec (arr : Array Nat) (k : Nat) :
    k ≤ trimmedSize arr k ∧ trimmedSize arr k ≤ max k arr.size ∧
    (∀ i : Nat, trimmedSize arr k ≤ i → arr[i]! = 0) := by
  rw [trimmedSize_eq]
  refine ⟨trim_fold_ge _ _ _, ?_, ?_⟩
  · apply trim_fold_le
    · exact Nat.le_max_left ..
    · intro i hi
      rw [← List.range_eq_range'] at hi
      have := List.mem_range.mp hi
      have h2 : arr.size ≤ max k arr.size := Nat.le_max_right ..
      omega
  · intro i hle
    by_cases hi : i < arr.size
    · rcases Nat.eq_zero_or_pos arr[i]! with h0 | hpos
      · exact h0
      · exfalso
        have := trim_fold_covers (fun i => arr[i]!) (List.range' 0 arr.size) k i
          (by rw [← List.range_eq_range']; exact List.mem_range.mpr hi) hpos
        omega
    · exact getElem!_oob arr i hi

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The code-length-alphabet frequency fold. -/
def clenFreqF (rle : List (Nat × Nat × Nat)) : Array Nat :=
  rle.foldl (fun f t => f.set! t.1 (f[t.1]! + 1)) (Array.replicate 19 0)

/- REF: docs/STDLIB_ZLIB.md#42-block-formats -/
/-- The HCLEN scan over the permuted code-length lengths. -/
def hclenF (clenLengths : Array Nat) : Nat :=
  (List.range' 0 19).foldl
    (fun n i => if clenLengths[clenOrder[i]!]! > 0 then max n (i + 1) else n) 4

end Stdlib.Zlib

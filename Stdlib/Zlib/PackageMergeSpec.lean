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
import Stdlib.Zlib.CanonicalTableSpec

/-
## PA16 L2v: package-merge validity — lengths ≤ maxBits, every used symbol coded, Kraft

`packageMergeLengths` (Deflate.lean) runs the in-place boundary package-merge: `maxBits - 1`
rounds of "package the current list in adjacent pairs, merge the fresh leaves back in", then
reads each symbol's code length off as its number of occurrences among the first `2n - 2`
items of the final list. This file proves, structurally (no enumeration — the frequency
array is data-dependent at `compress` time), that for `n ≥ 2` leaves and `n - 1 < 2^(W-1)`:

- every leaf symbol receives a length in `[1, W]`, and only leaf symbols receive lengths;
- the produced lengths satisfy the Kraft inequality `Σ 2^(W - l_s) ≤ 2^W`, in the compact
  `kraftOk` form the canonical-table specification (L2d) consumes.

Proof architecture — a ghost mirror with introduction levels:
1. `PMG` items carry `(symbol, introLevel)` pairs; `pmPackageG`/`pmMergeG` mirror the real
   steps (comparisons read only weights, which the projection preserves), so the real level
   lists are projections of ghost level lists.
2. Structural facts about ghost levels: every annotation's level is within the current
   round; each `(symbol, level)` pair occurs AT MOST ONCE across the entire list (a fresh
   leaf enters once per round and packaging never duplicates an item); every item's value
   `Σ 2^(level-1)` is exactly `2^(round-1)` (leaves enter at the round's value, packages
   add two equal values).
3. The list-length law `|L_d| = 2n - 1 - (n-1)/2^d`, so the final list has `2n - 1` items
   and the `2n - 2` solution prefix drops exactly one.
4. The counting finish: summing item values over the solution gives `(2n-2)·2^(W-1)`;
   per-symbol, distinct levels force `value_s ≤ 2^W - 2^(W - l_s)`; totals then force every
   leaf to be coded (`l_s ≥ 1`) and the Kraft inequality — no exchange/optimality argument
   anywhere, validity only.
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost package-merge item: weight plus `(symbol, introLevel)` annotations. -/
structure PMG where
  weight : Nat
  syms   : List (Nat × Nat)
  deriving Repr, Inhabited

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost twin of `pmPackage`: pair adjacent items, drop the odd trailing item. -/
def pmPackageG : List PMG → List PMG
  | a :: b :: rest => { weight := a.weight + b.weight, syms := a.syms ++ b.syms } :: pmPackageG rest
  | _ => []

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost twin of `pmMerge`: stable merge by weight. -/
def pmMergeG : List PMG → List PMG → List PMG
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x.weight ≤ y.weight then x :: pmMergeG xs (y :: ys)
    else y :: pmMergeG (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Projection dropping the level annotations. -/
def pmProj (g : PMG) : PMNode :=
  { weight := g.weight, syms := g.syms.map Prod.fst }

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Packaging commutes with projection. -/
theorem pmPackageG_proj : ∀ (L : List PMG),
    (pmPackageG L).map pmProj = pmPackage (L.map pmProj) := by
  intro L
  induction L using pmPackageG.induct with
  | case1 a b rest ih =>
    show pmProj _ :: (pmPackageG rest).map pmProj = _
    rw [ih]
    show _ = { weight := (pmProj a).weight + (pmProj b).weight,
               syms := (pmProj a).syms ++ (pmProj b).syms } :: pmPackage (rest.map pmProj)
    congr 1
    unfold pmProj
    simp
  | case2 t h =>
    cases t with
    | nil => rfl
    | cons x t' =>
      cases t' with
      | nil => rfl
      | cons y t'' => exact (h x y t'' rfl).elim

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Merging commutes with projection (comparisons read only weights). -/
theorem pmMergeG_proj : ∀ (A B : List PMG),
    (pmMergeG A B).map pmProj = pmMerge (A.map pmProj) (B.map pmProj) := by
  intro A B
  induction A, B using pmMergeG.induct with
  | case1 ys => simp [pmMergeG, pmMerge]
  | case2 x xs => simp [pmMergeG, pmMerge]
  | case3 x xs y ys hle ih =>
    rw [pmMergeG, if_pos hle]
    show pmProj x :: (pmMergeG xs (y :: ys)).map pmProj = _
    rw [ih]
    show _ = pmMerge (pmProj x :: xs.map pmProj) (pmProj y :: ys.map pmProj)
    rw [pmMerge, if_pos (show (pmProj x).weight ≤ (pmProj y).weight from hle)]
    rfl
  | case4 x xs y ys hle ih =>
    rw [pmMergeG, if_neg hle]
    show pmProj y :: (pmMergeG (x :: xs) ys).map pmProj = _
    rw [ih]
    show _ = pmMerge (pmProj x :: xs.map pmProj) (pmProj y :: ys.map pmProj)
    rw [pmMerge, if_neg (show ¬ (pmProj x).weight ≤ (pmProj y).weight from hle)]
    rfl

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The fresh ghost leaves entering at round `k`. -/
def ghostLeaves (leaves : List PMNode) (k : Nat) : List PMG :=
  leaves.map fun x => { weight := x.weight, syms := x.syms.map (fun s => (s, k)) }

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost level lists: `ghostLevels leaves d` is the working list after `d` rounds
    (round number `d + 1`). -/
def ghostLevels (leaves : List PMNode) : Nat → List PMG
  | 0 => ghostLeaves leaves 1
  | d + 1 => pmMergeG (ghostLeaves leaves (d + 2)) (pmPackageG (ghostLevels leaves d))

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost leaves project to the real leaves. -/
theorem ghostLeaves_proj (leaves : List PMNode) (k : Nat) :
    (ghostLeaves leaves k).map pmProj = leaves := by
  unfold ghostLeaves
  rw [List.map_map]
  have h : (pmProj ∘ fun x => ({ weight := x.weight, syms := x.syms.map (fun s => (s, k)) } : PMG))
      = id := by
    funext x
    show pmProj { weight := x.weight, syms := x.syms.map (fun s => (s, k)) } = x
    unfold pmProj
    have hmm : (x.syms.map (fun s => (s, k))).map Prod.fst = x.syms := by
      rw [List.map_map]
      have hcomp : (Prod.fst ∘ fun s => ((s, k) : Nat × Nat)) = (id : Nat → Nat) := by
        funext s
        rfl
      rw [hcomp, List.map_id]
    show ({ weight := x.weight, syms := (x.syms.map (fun s => (s, k))).map Prod.fst } : PMNode) = x
    rw [hmm]
  rw [h, List.map_id]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Simulation: the real working list after `d` rounds is the ghost list's projection. -/
theorem ghostLevels_proj (leaves : List PMNode) : ∀ d : Nat,
    (ghostLevels leaves d).map pmProj =
      (List.range d).foldl (fun cur _ => pmMerge leaves (pmPackage cur)) leaves := by
  intro d
  induction d with
  | zero => exact ghostLeaves_proj leaves 1
  | succ d ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    show (pmMergeG (ghostLeaves leaves (d + 2)) (pmPackageG (ghostLevels leaves d))).map pmProj = _
    rw [pmMergeG_proj, ghostLeaves_proj, pmPackageG_proj, ih]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Merging adds lengths. -/
theorem pmMergeG_length : ∀ (A B : List PMG), (pmMergeG A B).length = A.length + B.length := by
  intro A B
  induction A, B using pmMergeG.induct with
  | case1 ys => simp [pmMergeG]
  | case2 x xs => simp [pmMergeG]
  | case3 x xs y ys hle ih =>
    rw [pmMergeG, if_pos hle]
    show (pmMergeG xs (y :: ys)).length + 1 = _
    rw [ih]
    simp
    omega
  | case4 x xs y ys hle ih =>
    rw [pmMergeG, if_neg hle]
    show (pmMergeG (x :: xs) ys).length + 1 = _
    rw [ih]
    simp
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Packaging halves lengths (dropping the odd trailing item). -/
theorem pmPackageG_length : ∀ (L : List PMG), (pmPackageG L).length = L.length / 2 := by
  intro L
  induction L using pmPackageG.induct with
  | case1 a b rest ih =>
    show (pmPackageG rest).length + 1 = _
    rw [ih]
    show _ = (rest.length + 1 + 1) / 2
    omega
  | case2 t h =>
    cases t with
    | nil => rfl
    | cons x t' =>
      cases t' with
      | nil => simp [pmPackageG]
      | cons y t'' => exact (h x y t'' rfl).elim

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost leaves count. -/
theorem ghostLeaves_length (leaves : List PMNode) (k : Nat) :
    (ghostLeaves leaves k).length = leaves.length := by
  unfold ghostLeaves
  rw [List.length_map]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **The level-length law**: after `d` rounds the working list holds
    `2n - 1 - (n-1)/2^d` items (`n` = leaf count, `n ≥ 1`). -/
theorem ghostLevels_length (leaves : List PMNode) (hn : 1 ≤ leaves.length) : ∀ d : Nat,
    (ghostLevels leaves d).length = 2 * leaves.length - 1 - (leaves.length - 1) / 2 ^ d := by
  intro d
  induction d with
  | zero =>
    show (ghostLeaves leaves 1).length = _
    rw [ghostLeaves_length]
    simp
    omega
  | succ d ih =>
    show (pmMergeG (ghostLeaves leaves (d + 2)) (pmPackageG (ghostLevels leaves d))).length = _
    rw [pmMergeG_length, ghostLeaves_length, pmPackageG_length, ih]
    have hdiv : (leaves.length - 1) / 2 ^ d / 2 = (leaves.length - 1) / 2 ^ (d + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    rw [← hdiv]
    have hle : (leaves.length - 1) / 2 ^ d ≤ leaves.length - 1 :=
      Nat.div_le_self _ _
    omega

/-
## Ghost invariants: annotation ranges, global once-only counts, and item values.
-/

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Item value: each annotation contributes `2^(level-1)`. -/
def itemVal (g : PMG) : Nat :=
  (g.syms.map (fun e => 2 ^ (e.2 - 1))).sum

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Global multiplicity of one `(symbol, level)` annotation across a whole working list. -/
def ghostCount (e : Nat × Nat) (L : List PMG) : Nat :=
  (L.map (fun g => g.syms.count e)).sum

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- All annotations of all items satisfy a predicate. -/
def annAll (P : Nat × Nat → Prop) (L : List PMG) : Prop :=
  ∀ g ∈ L, ∀ e ∈ g.syms, P e

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Merge produces no new items. -/
theorem mem_pmMergeG : ∀ (A B : List PMG) (g : PMG), g ∈ pmMergeG A B → g ∈ A ∨ g ∈ B := by
  intro A B
  induction A, B using pmMergeG.induct with
  | case1 ys =>
    intro g hg
    rw [pmMergeG] at hg
    exact Or.inr hg
  | case2 x xs =>
    intro g hg
    rw [pmMergeG] at hg
    exact Or.inl hg
  | case3 x xs y ys hle ih =>
    intro g hg
    rw [pmMergeG, if_pos hle] at hg
    rcases List.mem_cons.mp hg with h | h
    · exact Or.inl (by simp [h])
    · rcases ih g h with h' | h'
      · exact Or.inl (by simp [h'])
      · exact Or.inr h'
  | case4 x xs y ys hle ih =>
    intro g hg
    rw [pmMergeG, if_neg hle] at hg
    rcases List.mem_cons.mp hg with h | h
    · exact Or.inr (by simp [h])
    · rcases ih g h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by simp [h'])

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Every annotation of a package comes from some packaged item. -/
theorem pmPackageG_ann : ∀ (L : List PMG) (g : PMG), g ∈ pmPackageG L →
    ∀ e ∈ g.syms, ∃ a, a ∈ L ∧ e ∈ a.syms := by
  intro L
  induction L using pmPackageG.induct with
  | case1 a b rest ih =>
    intro g hg e he
    rcases List.mem_cons.mp hg with h | h
    · subst h
      have he' : e ∈ a.syms ++ b.syms := he
      rcases List.mem_append.mp he' with h' | h'
      · exact ⟨a, by simp, h'⟩
      · exact ⟨b, by simp, h'⟩
    · obtain ⟨a', ha', he'⟩ := ih g h e he
      exact ⟨a', by simp [ha'], he'⟩
  | case2 t h =>
    intro g hg
    cases t with
    | nil => simp [pmPackageG] at hg
    | cons x t' =>
      cases t' with
      | nil => simp [pmPackageG] at hg
      | cons y t'' => exact (h x y t'' rfl).elim

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Annotation ranges through a level step. -/
theorem annAll_ghostLevels (leaves : List PMNode) (Q : Nat → Prop)
    (hQ : ∀ x ∈ leaves, ∀ s ∈ x.syms, Q s) : ∀ d : Nat,
    annAll (fun e => 1 ≤ e.2 ∧ e.2 ≤ d + 1 ∧ Q e.1) (ghostLevels leaves d) := by
  have hleaves : ∀ k, 1 ≤ k → annAll (fun e => 1 ≤ e.2 ∧ e.2 = k ∧ Q e.1)
      (ghostLeaves leaves k) := by
    intro k hk g hg e he
    unfold ghostLeaves at hg
    obtain ⟨x, hx, hgx⟩ := List.mem_map.mp hg
    subst hgx
    obtain ⟨s, hs, hes⟩ := List.mem_map.mp he
    subst hes
    exact ⟨hk, rfl, hQ x hx s hs⟩
  intro d
  induction d with
  | zero =>
    intro g hg e he
    obtain ⟨h1, h2, h3⟩ := hleaves 1 (by omega) g hg e he
    exact ⟨h1, by omega, h3⟩
  | succ d ih =>
    intro g hg e he
    rcases mem_pmMergeG _ _ g hg with h | h
    · obtain ⟨h1, h2, h3⟩ := hleaves (d + 2) (by omega) g h e he
      exact ⟨h1, by omega, h3⟩
    · obtain ⟨a, ha, hea⟩ := pmPackageG_ann _ g h e he
      obtain ⟨h1, h2, h3⟩ := ih a ha e hea
      exact ⟨h1, by omega, h3⟩

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Merging is count-preserving in total. -/
theorem ghostCount_pmMergeG (e : Nat × Nat) : ∀ (A B : List PMG),
    ghostCount e (pmMergeG A B) = ghostCount e A + ghostCount e B := by
  intro A B
  induction A, B using pmMergeG.induct with
  | case1 ys => simp [pmMergeG, ghostCount]
  | case2 x xs => simp [pmMergeG, ghostCount]
  | case3 x xs y ys hle ih =>
    rw [pmMergeG, if_pos hle]
    show x.syms.count e + ghostCount e (pmMergeG xs (y :: ys)) = _
    rw [ih]
    show _ = (x.syms.count e + ghostCount e xs) + ghostCount e (y :: ys)
    omega
  | case4 x xs y ys hle ih =>
    rw [pmMergeG, if_neg hle]
    show y.syms.count e + ghostCount e (pmMergeG (x :: xs) ys) = _
    rw [ih]
    show _ = ghostCount e (x :: xs) + (y.syms.count e + ghostCount e ys)
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Packaging never duplicates an annotation. -/
theorem ghostCount_pmPackageG_le (e : Nat × Nat) : ∀ (L : List PMG),
    ghostCount e (pmPackageG L) ≤ ghostCount e L := by
  intro L
  induction L using pmPackageG.induct with
  | case1 a b rest ih =>
    show (a.syms ++ b.syms).count e + ghostCount e (pmPackageG rest) ≤
      a.syms.count e + (b.syms.count e + ghostCount e rest)
    rw [List.count_append]
    omega
  | case2 t h =>
    cases t with
    | nil => simp [pmPackageG]
    | cons x t' =>
      cases t' with
      | nil =>
        show ghostCount e (pmPackageG [x]) ≤ ghostCount e [x]
        simp [pmPackageG, ghostCount]
      | cons y t'' => exact (h x y t'' rfl).elim

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Absent annotations have zero count. -/
theorem ghostCount_eq_zero {e : Nat × Nat} : ∀ {L : List PMG},
    (∀ g ∈ L, e ∉ g.syms) → ghostCount e L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons g L ih =>
    intro h
    show g.syms.count e + ghostCount e L = 0
    rw [List.count_eq_zero.mpr (h g (by simp)), ih (fun g' hg' => h g' (by simp [hg']))]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Counting one `(symbol, level)` pair in a freshly annotated symbol list. -/
theorem count_pair_map (s j k : Nat) : ∀ (l : List Nat),
    (l.map (fun t => (t, k))).count (s, j) = if j = k then l.count s else 0 := by
  intro l
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.count_cons, ih, List.count_cons]
    by_cases hj : j = k
    · subst hj
      by_cases ht : t = s
      · subst ht
        simp
      · rw [if_pos rfl, if_pos rfl]
        have h1 : (((t, j) : Nat × Nat) == (s, j)) = false := by
          simp [ht]
        have h2 : ((t : Nat) == s) = false := by
          simp [ht]
        rw [h1, h2]
    · rw [if_neg hj, if_neg hj]
      have h1 : (((t, k) : Nat × Nat) == (s, j)) = false := by
        simp
        omega
      rw [h1]
      simp

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Counting one annotation among the fresh leaves of round `k`. -/
theorem ghostCount_ghostLeaves (leaves : List PMNode) (s j k : Nat) :
    ghostCount (s, j) (ghostLeaves leaves k) =
      if j = k then (leaves.map (fun x => x.syms.count s)).sum else 0 := by
  unfold ghostCount ghostLeaves
  rw [List.map_map]
  induction leaves with
  | nil => simp
  | cons x leaves ih =>
    rw [List.map_cons, List.sum_cons, ih]
    show (x.syms.map (fun t => (t, k))).count (s, j) + _ = _
    rw [count_pair_map]
    by_cases hj : j = k
    · rw [if_pos hj, if_pos hj, if_pos hj]
      simp
    · rw [if_neg hj, if_neg hj, if_neg hj]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **Once-only counts**: provided the leaf list mentions each symbol at most once in
    total, every `(symbol, level)` annotation occurs at most once across any level list. -/
theorem ghostCount_ghostLevels_le_one (leaves : List PMNode)
    (honce : ∀ s, ((leaves.map (fun x => x.syms.count s)).sum ≤ 1)) :
    ∀ (d : Nat) (s j : Nat), ghostCount (s, j) (ghostLevels leaves d) ≤ 1 := by
  intro d
  induction d with
  | zero =>
    intro s j
    show ghostCount (s, j) (ghostLeaves leaves 1) ≤ 1
    rw [ghostCount_ghostLeaves]
    by_cases hj : j = 1
    · rw [if_pos hj]
      exact honce s
    · rw [if_neg hj]
      omega
  | succ d ih =>
    intro s j
    show ghostCount (s, j) (pmMergeG (ghostLeaves leaves (d + 2))
      (pmPackageG (ghostLevels leaves d))) ≤ 1
    rw [ghostCount_pmMergeG, ghostCount_ghostLeaves]
    by_cases hj : j = d + 2
    · rw [if_pos hj]
      -- packages carry only annotations of level ≤ d + 1 < d + 2
      have hzero : ghostCount (s, j) (pmPackageG (ghostLevels leaves d)) = 0 := by
        apply ghostCount_eq_zero
        intro g hg he
        obtain ⟨a, ha, hea⟩ := pmPackageG_ann _ g hg (s, j) he
        have := annAll_ghostLevels leaves (fun _ => True) (fun _ _ _ _ => trivial) d a ha
          (s, j) hea
        omega
      rw [hzero]
      have := honce s
      omega
    · rw [if_neg hj]
      have h1 := ghostCount_pmPackageG_le (s, j) (ghostLevels leaves d)
      have h2 := ih s j
      omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Packaging doubles a uniform item value. -/
theorem itemVal_pmPackageG (v : Nat) : ∀ (L : List PMG), (∀ g ∈ L, itemVal g = v) →
    ∀ g ∈ pmPackageG L, itemVal g = 2 * v := by
  intro L
  induction L using pmPackageG.induct with
  | case1 a b rest ih =>
    intro hL g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h
      unfold itemVal
      show ((a.syms ++ b.syms).map (fun e => 2 ^ (e.2 - 1))).sum = _
      rw [List.map_append, List.sum_append]
      have ha := hL a (by simp)
      have hb := hL b (by simp)
      unfold itemVal at ha hb
      omega
    · exact ih (fun g' hg' => hL g' (by simp [hg'])) g h
  | case2 t ht =>
    intro hL g hg
    cases t with
    | nil => simp [pmPackageG] at hg
    | cons x t' =>
      cases t' with
      | nil => simp [pmPackageG] at hg
      | cons y t'' => exact (ht x y t'' rfl).elim

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **Item values**: every item of the round-`d+1` list is worth exactly `2^d`, provided
    every leaf mentions exactly one symbol. -/
theorem itemVal_ghostLevels (leaves : List PMNode)
    (hone : ∀ x ∈ leaves, x.syms.length = 1) :
    ∀ (d : Nat), ∀ g ∈ ghostLevels leaves d, itemVal g = 2 ^ d := by
  have hleaf : ∀ k, 1 ≤ k → ∀ g ∈ ghostLeaves leaves k, itemVal g = 2 ^ (k - 1) := by
    intro k hk g hg
    unfold ghostLeaves at hg
    obtain ⟨x, hx, hgx⟩ := List.mem_map.mp hg
    subst hgx
    unfold itemVal
    match hsyms : x.syms, hone x hx with
    | [s], _ =>
      show ((([s].map (fun t => (t, k))).map (fun e => 2 ^ (e.2 - 1))).sum) = 2 ^ (k - 1)
      simp
    | [], h => simp at h
    | a :: b :: t, h => simp at h
  intro d
  induction d with
  | zero =>
    intro g hg
    exact hleaf 1 (by omega) g hg
  | succ d ih =>
    intro g hg
    rcases mem_pmMergeG _ _ g hg with h | h
    · have := hleaf (d + 2) (by omega) g h
      simpa using this
    · have hpack := itemVal_pmPackageG (2 ^ d) (ghostLevels leaves d) ih g h
      rw [hpack, Nat.pow_succ]
      omega

/-
## Generic finite-sum bookkeeping: pointwise bounds, delta sums, double counting.
All hand-rolled inductions — this project deliberately uses core Lean only.
-/

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Pointwise-zero maps sum to zero. -/
theorem sum_map_zero {α : Type} (f : α → Nat) : ∀ (l : List α),
    (∀ x ∈ l, f x = 0) → (l.map f).sum = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.map_cons, List.sum_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Pointwise-bounded maps have bounded sums. -/
theorem sum_map_le {α : Type} (f g : α → Nat) : ∀ (l : List α),
    (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; exact Nat.le_refl _
  | cons a l ih =>
    intro h
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Sums split over pointwise addition. -/
theorem sum_map_add {α : Type} (f g : α → Nat) : ∀ (l : List α),
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons,
      List.sum_cons, ih]
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Pointwise-equal maps have equal sums. -/
theorem sum_map_congr {α : Type} (f g : α → Nat) : ∀ (l : List α),
    (∀ x ∈ l, f x = g x) → (l.map f).sum = (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, h a (by simp),
      ih (fun x hx => h x (by simp [hx]))]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Summing a guarded constant counts the guard. -/
theorem sum_map_ite_const {α : Type} (p : α → Bool) (v : Nat) : ∀ (l : List α),
    (l.map (fun x => if p x then v else 0)).sum = l.countP p * v := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a
    · rw [if_pos h, if_pos h, Nat.add_mul]
      omega
    · rw [if_neg h, if_neg h]
      simp

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Delta sum over `List.range`: only the hit index contributes. -/
theorem sum_map_delta_range (v : Nat → Nat) : ∀ (N a : Nat), a < N →
    ((List.range N).map (fun s => if s = a then v s else 0)).sum = v a := by
  intro N
  induction N with
  | zero => intro a ha; omega
  | succ N ih =>
    intro a ha
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge a N with h | h
    · rw [ih a h]
      have hne : ¬ (N = a) := by omega
      simp [hne]
    · have haN : a = N := by omega
      subst haN
      have hzero : ((List.range a).map (fun s => if s = a then v s else 0)).sum = 0 := by
        apply sum_map_zero
        intro x hx
        have hxa := List.mem_range.mp hx
        rw [if_neg (by omega)]
      rw [hzero]
      simp

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Delta sum over `List.range' 1 W`: only the hit level contributes. -/
theorem sum_map_delta_range' (v : Nat → Nat) : ∀ (W a : Nat), 1 ≤ a → a ≤ W →
    ((List.range' 1 W).map (fun j => if j = a then v j else 0)).sum = v a := by
  intro W
  induction W with
  | zero => intro a h1 h2; omega
  | succ W ih =>
    intro a h1 h2
    rw [List.range'_1_concat, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge a (W + 1) with h | h
    · rw [ih a h1 (by omega)]
      have hne : ¬ (1 + W = a) := by omega
      simp [hne]
    · have haW : a = 1 + W := by omega
      have hzero : ((List.range' 1 W).map (fun j => if j = a then v j else 0)).sum = 0 := by
        apply sum_map_zero
        intro x hx
        have hxa := List.mem_range'_1.mp hx
        rw [if_neg (by omega)]
      rw [hzero, haW]
      simp

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **Double counting**: a sum over annotations regroups as a sum over symbols and levels
    weighted by multiplicities. -/
theorem sum_flat_eq_sum_counts (W N : Nat) (f : Nat × Nat → Nat) :
    ∀ (F : List (Nat × Nat)), (∀ e ∈ F, e.1 < N ∧ 1 ≤ e.2 ∧ e.2 ≤ W) →
    (F.map f).sum =
      ((List.range N).map (fun s =>
        ((List.range' 1 W).map (fun j => F.count (s, j) * f (s, j))).sum)).sum := by
  intro F
  induction F with
  | nil =>
    intro _
    rw [List.map_nil, List.sum_nil]
    symm
    apply sum_map_zero
    intro s _
    apply sum_map_zero
    intro j _
    simp
  | cons e F ih =>
    intro h
    have he := h e (by simp)
    have hF := ih (fun x hx => h x (by simp [hx]))
    rw [List.map_cons, List.sum_cons, hF]
    -- split each count into the tail count plus the head indicator
    have hsplit : ∀ s j, (e :: F).count (s, j) * f (s, j) =
        F.count (s, j) * f (s, j) + (if e = (s, j) then f e else 0) := by
      intro s j
      rw [List.count_cons]
      by_cases he' : e = (s, j)
      · rw [if_pos (beq_iff_eq.mpr he'), if_pos he', Nat.add_mul, he']
        simp
      · rw [if_neg (fun hcon => he' (eq_of_beq hcon)), if_neg he']
        simp
    have houter : ∀ s, ((List.range' 1 W).map (fun j => (e :: F).count (s, j) * f (s, j))).sum =
        ((List.range' 1 W).map (fun j => F.count (s, j) * f (s, j))).sum +
          ((List.range' 1 W).map (fun j => if e = (s, j) then f e else 0)).sum := by
      intro s
      rw [← sum_map_add]
      apply sum_map_congr
      intro j _
      exact hsplit s j
    rw [sum_map_congr _ _ _ (fun s _ => houter s), sum_map_add]
    -- the indicator double sum contributes exactly f e
    have hdelta : ((List.range N).map (fun s =>
        ((List.range' 1 W).map (fun j => if e = (s, j) then f e else 0)).sum)).sum = f e := by
      have hone : ∀ s, ((List.range' 1 W).map (fun j => if e = (s, j) then f e else 0)).sum =
          if s = e.1 then f e else 0 := by
        intro s
        by_cases hs : s = e.1
        · rw [if_pos hs]
          have hinner : ∀ j : Nat, (if e = (s, j) then f e else 0) =
              (if j = e.2 then f e else 0) := by
            intro j
            by_cases hj : j = e.2
            · rw [if_pos hj, if_pos (by rw [hs, hj])]
            · rw [if_neg hj, if_neg (fun hcon => hj (congrArg Prod.snd hcon).symm)]
          rw [sum_map_congr _ _ _ (fun j _ => hinner j)]
          exact sum_map_delta_range' (fun _ => f e) W e.2 he.2.1 he.2.2
        · rw [if_neg hs]
          apply sum_map_zero
          intro j _
          rw [if_neg (fun hcon => hs (congrArg Prod.fst hcon).symm)]
      rw [sum_map_congr _ _ _ (fun s _ => hone s)]
      exact sum_map_delta_range (fun _ => f e) N e.1 he.1
    rw [hdelta]
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **Distinct-level value bound**: a 0/1 level-indicator's weighted sum is maximized by
    the deepest levels, giving `≤ 2^W - 2^(W - count)` — with `count ≤ W` for free. -/
theorem indicator_sum_bound : ∀ (W : Nat) (c : Nat → Nat), (∀ j, c j ≤ 1) →
    ((List.range' 1 W).map c).sum ≤ W ∧
    ((List.range' 1 W).map (fun j => c j * 2 ^ (j - 1))).sum ≤
      2 ^ W - 2 ^ (W - ((List.range' 1 W).map c).sum) := by
  intro W
  induction W with
  | zero =>
    intro c _
    exact ⟨Nat.le_refl _, by simp⟩
  | succ W ih =>
    intro c hc
    obtain ⟨ihl, ihs⟩ := ih c hc
    rw [List.range'_1_concat, List.map_append, List.sum_append, List.map_append,
      List.sum_append]
    have hlast : (([1 + W] : List Nat).map (fun j => c j * 2 ^ (j - 1))).sum
        = c (1 + W) * 2 ^ W := by
      have he : 1 + W - 1 = W := by omega
      simp [he]
    have hlastc : (([1 + W] : List Nat).map c).sum = c (1 + W) := by
      simp
    rw [hlast, hlastc]
    obtain ⟨l', hl'⟩ : ∃ x, ((List.range' 1 W).map c).sum = x := ⟨_, rfl⟩
    rw [hl'] at ihl ihs ⊢
    have hcW := hc (1 + W)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcW with h0 | h1
    · -- the top level is unused
      rw [h0]
      refine ⟨by omega, ?_⟩
      have hpow1 : (2 : Nat) ^ (W + 1 - (l' + 0)) = 2 * 2 ^ (W - l') := by
        rw [show W + 1 - (l' + 0) = (W - l') + 1 from by omega, Nat.pow_succ]
        omega
      have hpow2 : (2 : Nat) ^ (W + 1) = 2 * 2 ^ W := by
        rw [Nat.pow_succ]
        omega
      have hmono : (2 : Nat) ^ (W - l') ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (2 : Nat) ^ (W - l') ≥ 1 := Nat.one_le_two_pow
      omega
    · -- the top level is used: the bound is exact-tight
      rw [h1]
      refine ⟨by omega, ?_⟩
      have hpow1 : (2 : Nat) ^ (W + 1 - (l' + 1)) = 2 ^ (W - l') := by
        congr 1
        omega
      have hpow2 : (2 : Nat) ^ (W + 1) = 2 * 2 ^ W := by
        rw [Nat.pow_succ]
        omega
      have hmono : (2 : Nat) ^ (W - l') ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (2 : Nat) ^ (W - l') ≥ 1 := Nat.one_le_two_pow
      omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Regrouping per-level counts of one symbol into that symbol's total multiplicity. -/
theorem count_pairs_sum (W s : Nat) : ∀ (F : List (Nat × Nat)),
    (∀ e ∈ F, 1 ≤ e.2 ∧ e.2 ≤ W) →
    ((List.range' 1 W).map (fun j => F.count (s, j))).sum = F.countP (fun e => e.1 == s) := by
  intro F
  induction F with
  | nil =>
    intro _
    rw [List.countP_nil]
    apply sum_map_zero
    intro j _
    simp
  | cons e F ih =>
    intro h
    have he := h e (by simp)
    rw [List.countP_cons, ← ih (fun x hx => h x (by simp [hx]))]
    have hsplit : ∀ j, (e :: F).count (s, j) =
        F.count (s, j) + (if e = (s, j) then 1 else 0) := by
      intro j
      rw [List.count_cons]
      by_cases he' : e = (s, j)
      · rw [if_pos (beq_iff_eq.mpr he'), if_pos he']
      · rw [if_neg (fun hcon => he' (eq_of_beq hcon)), if_neg he']
    rw [sum_map_congr _ _ _ (fun j _ => hsplit j), sum_map_add]
    congr 1
    by_cases hs : e.1 = s
    · have hinner : ∀ j : Nat, (if e = (s, j) then 1 else 0) =
          (if j = e.2 then 1 else 0) := by
        intro j
        by_cases hj : j = e.2
        · rw [if_pos hj, if_pos (by rw [← hs, hj])]
        · rw [if_neg hj, if_neg (fun hcon => hj (congrArg Prod.snd hcon).symm)]
      rw [sum_map_congr _ _ _ (fun j _ => hinner j),
        sum_map_delta_range' (fun _ => 1) W e.2 he.1 he.2]
      simp [hs]
    · have hzero : ((List.range' 1 W).map (fun j => if e = (s, j) then 1 else 0)).sum = 0 := by
        apply sum_map_zero
        intro j _
        rw [if_neg (fun hcon => hs (congrArg Prod.fst hcon))]
      rw [hzero]
      have : (e.1 == s) = false := by
        simp [hs]
      rw [this]
      simp

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- If an implication holds pointwise and the counts agree, the converse holds pointwise. -/
theorem countP_eq_of_imp {α : Type} (p q : α → Bool) : ∀ (l : List α),
    (∀ x ∈ l, p x = true → q x = true) → l.countP p = l.countP q →
    ∀ x ∈ l, q x = true → p x = true := by
  intro l
  induction l with
  | nil => intro _ _ x hx; simp at hx
  | cons a l ih =>
    intro himp hcnt x hx hqx
    have hmono : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun y hy => himp y (by simp [hy]))
    rw [List.countP_cons, List.countP_cons] at hcnt
    by_cases hpa : p a = true
    · have hqa : q a = true := himp a (by simp) hpa
      rw [if_pos hpa, if_pos hqa] at hcnt
      have hcnt' : l.countP p = l.countP q := by omega
      rcases List.mem_cons.mp hx with hxa | hxl
      · subst hxa
        exact hpa
      · exact ih (fun y hy => himp y (by simp [hy])) hcnt' x hxl hqx
    · rw [if_neg hpa] at hcnt
      by_cases hqa : q a = true
      · rw [if_pos hqa] at hcnt
        omega
      · rw [if_neg hqa] at hcnt
        rcases List.mem_cons.mp hx with hxa | hxl
        · subst hxa
          exact absurd hqx hqa
        · exact ih (fun y hy => himp y (by simp [hy])) (by omega) x hxl hqx

/-
## The master counting argument over an annotation multiset.
-/

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Code length a symbol receives from an annotation list: its total multiplicity. -/
def lenOfF (F : List (Nat × Nat)) (s : Nat) : Nat :=
  F.countP (fun e => e.1 == s)

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Positive counts exhibit members. -/
theorem countP_pos_iff {α : Type} (p : α → Bool) : ∀ (l : List α),
    0 < l.countP p ↔ ∃ x, x ∈ l ∧ p x = true := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    by_cases h : p a = true
    · rw [if_pos h]
      constructor
      · intro _
        exact ⟨a, by simp, h⟩
      · intro _
        omega
    · rw [if_neg h]
      constructor
      · intro hpos
        obtain ⟨x, hx, hpx⟩ := ih.mp (by omega)
        exact ⟨x, by simp [hx], hpx⟩
      · intro ⟨x, hx, hpx⟩
        rcases List.mem_cons.mp hx with hxa | hxl
        · subst hxa
          exact absurd hpx h
        · have := ih.mpr ⟨x, hxl, hpx⟩
          omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- A Prop-`ite` equals its decided Bool-`ite`. -/
theorem ite_decide_eq {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if decide c = true then a else b) = if c then a else b := by
  by_cases h : c <;> simp [h]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **The master count**: an annotation multiset whose symbols are leaves, whose levels are
    once-only per `(symbol, level)` and range over `[1, W]`, and whose total value is
    exactly `(2n-2)·2^(W-1)`, forces every one of the `n` leaves to be coded within `W`
    bits and the resulting lengths to satisfy the Kraft inequality. -/
theorem master_counting (W N n : Nat) (isLeaf : Nat → Bool) (hW : 1 ≤ W) (hn : 2 ≤ n)
    (F : List (Nat × Nat))
    (hrange : ∀ e ∈ F, e.1 < N ∧ 1 ≤ e.2 ∧ e.2 ≤ W)
    (honce : ∀ s j, F.count (s, j) ≤ 1)
    (hleafmem : ∀ e ∈ F, isLeaf e.1 = true)
    (hnleaf : (List.range N).countP isLeaf = n)
    (htotal : (F.map (fun e => 2 ^ (e.2 - 1))).sum = (2 * n - 2) * 2 ^ (W - 1)) :
    (∀ s, s < N → isLeaf s = true → 1 ≤ lenOfF F s) ∧
    (∀ s, lenOfF F s ≤ W) ∧
    (∀ s, 1 ≤ lenOfF F s → s < N ∧ isLeaf s = true) ∧
    ((List.range N).map (fun s => if 1 ≤ lenOfF F s then 2 ^ (W - lenOfF F s) else 0)).sum
      ≤ 2 ^ W := by
  -- per-symbol indicator facts
  have hcbound : ∀ s j, F.count (s, j) ≤ 1 := honce
  have hlen_eq : ∀ s, ((List.range' 1 W).map (fun j => F.count (s, j))).sum = lenOfF F s :=
    fun s => count_pairs_sum W s F (fun e he => (hrange e he).2)
  have hind : ∀ s, lenOfF F s ≤ W ∧
      ((List.range' 1 W).map (fun j => F.count (s, j) * 2 ^ (j - 1))).sum ≤
        2 ^ W - 2 ^ (W - lenOfF F s) := by
    intro s
    have h := indicator_sum_bound W (fun j => F.count (s, j)) (fun j => hcbound s j)
    rw [hlen_eq s] at h
    exact h
  have hlenW : ∀ s, lenOfF F s ≤ W := fun s => (hind s).1
  -- symbols with positive length are in-range leaves
  have hposleaf : ∀ s, 1 ≤ lenOfF F s → s < N ∧ isLeaf s = true := by
    intro s hs
    obtain ⟨e, heF, hpe⟩ := (countP_pos_iff (fun e => e.1 == s) F).mp (by unfold lenOfF at hs; omega)
    have hes : e.1 = s := eq_of_beq hpe
    exact ⟨hes ▸ (hrange e heF).1, hes ▸ hleafmem e heF⟩
  -- the total value, regrouped per symbol
  have hregroup := sum_flat_eq_sum_counts W N (fun e => 2 ^ (e.2 - 1)) F hrange
  rw [htotal] at hregroup
  have htot2 : (2 * n - 2) * 2 ^ (W - 1) = (n - 1) * 2 ^ W := by
    have hWpred : W = (W - 1) + 1 := by omega
    calc (2 * n - 2) * 2 ^ (W - 1) = (n - 1) * (2 ^ (W - 1) * 2) := by
          rw [show 2 * n - 2 = (n - 1) * 2 from by omega, Nat.mul_assoc,
            Nat.mul_comm 2 (2 ^ (W - 1))]
      _ = (n - 1) * 2 ^ W := by
          congr 1
          rw [← Nat.pow_succ]
          congr 1
          omega
  rw [htot2] at hregroup
  -- name the per-symbol pieces
  have hvalbound : ∀ s, s < N →
      ((List.range' 1 W).map (fun j => F.count (s, j) * 2 ^ ((s, j).2 - 1))).sum ≤
        2 ^ W - 2 ^ (W - lenOfF F s) := by
    intro s _
    exact (hind s).2
  -- Σ val ≤ Σ A  where A s = 2^W - 2^(W - len s)
  have hA : ((List.range N).map (fun s =>
      ((List.range' 1 W).map (fun j => F.count (s, j) * 2 ^ ((s, j).2 - 1))).sum)).sum ≤
      ((List.range N).map (fun s => 2 ^ W - 2 ^ (W - lenOfF F s))).sum := by
    apply sum_map_le
    intro s hs
    exact hvalbound s (List.mem_range.mp hs)
  rw [← hregroup] at hA
  -- pointwise: A s + (guarded 2^(W - len s)) = guarded 2^W
  have hsplitAK : ∀ s, (2 ^ W - 2 ^ (W - lenOfF F s)) +
      (if 1 ≤ lenOfF F s then 2 ^ (W - lenOfF F s) else 0) =
      (if 1 ≤ lenOfF F s then 2 ^ W else 0) := by
    intro s
    by_cases h : 1 ≤ lenOfF F s
    · rw [if_pos h, if_pos h]
      have hle : (2 : Nat) ^ (W - lenOfF F s) ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · rw [if_neg h, if_neg h]
      have hW0 : W - lenOfF F s = W := by omega
      rw [hW0]
      omega
  have hAK : ((List.range N).map (fun s => 2 ^ W - 2 ^ (W - lenOfF F s))).sum +
      ((List.range N).map (fun s => if 1 ≤ lenOfF F s then 2 ^ (W - lenOfF F s) else 0)).sum =
      ((List.range N).map (fun s => if 1 ≤ lenOfF F s then 2 ^ W else 0)).sum := by
    rw [← sum_map_add]
    exact sum_map_congr _ _ _ (fun s _ => hsplitAK s)
  -- count of coded symbols
  have hm_eq : ((List.range N).map (fun s => if 1 ≤ lenOfF F s then 2 ^ W else 0)).sum =
      ((List.range N).countP (fun s => decide (1 ≤ lenOfF F s))) * 2 ^ W := by
    rw [← sum_map_ite_const (fun s => decide (1 ≤ lenOfF F s)) (2 ^ W)]
    exact sum_map_congr _ _ _ (fun s _ => (ite_decide_eq _ _ _).symm)
  -- m ≤ n
  have hmn : ((List.range N).countP (fun s => decide (1 ≤ lenOfF F s))) ≤ n := by
    rw [← hnleaf]
    apply List.countP_mono_left
    intro s _ hp
    exact (hposleaf s (of_decide_eq_true hp)).2
  -- K ≥ m
  have hKm : ((List.range N).countP (fun s => decide (1 ≤ lenOfF F s))) * 1 ≤
      ((List.range N).map (fun s => if 1 ≤ lenOfF F s then 2 ^ (W - lenOfF F s) else 0)).sum := by
    rw [← sum_map_ite_const (fun s => decide (1 ≤ lenOfF F s)) 1]
    apply sum_map_le
    intro s _
    rw [ite_decide_eq]
    by_cases h : 1 ≤ lenOfF F s
    · rw [if_pos h, if_pos h]
      exact Nat.one_le_two_pow
    · rw [if_neg h, if_neg h]
      omega
  -- A s ≤ guarded (2^W - 1)
  have hAle : ((List.range N).map (fun s => 2 ^ W - 2 ^ (W - lenOfF F s))).sum ≤
      ((List.range N).countP (fun s => decide (1 ≤ lenOfF F s))) * (2 ^ W - 1) := by
    rw [← sum_map_ite_const (fun s => decide (1 ≤ lenOfF F s)) (2 ^ W - 1)]
    apply sum_map_le
    intro s _
    rw [ite_decide_eq]
    by_cases h : 1 ≤ lenOfF F s
    · rw [if_pos h]
      have h2 : (2 : Nat) ^ (W - lenOfF F s) ≥ 1 := Nat.one_le_two_pow
      omega
    · rw [if_neg h]
      have h0 : lenOfF F s = 0 := by omega
      rw [h0]
      simp
  -- arithmetic finish
  obtain ⟨m, hm⟩ : ∃ m, ((List.range N).countP (fun s => decide (1 ≤ lenOfF F s))) = m :=
    ⟨_, rfl⟩
  rw [hm] at hm_eq hmn hKm hAle
  have hP1 : (1 : Nat) ≤ 2 ^ W := Nat.one_le_two_pow
  have hmul1 : m * (2 ^ W - 1) + m = m * 2 ^ W := by
    have : m * ((2 ^ W - 1) + 1) = m * (2 ^ W - 1) + m := by
      rw [Nat.mul_add]
      omega
    rw [← this]
    congr 1
    omega
  have hmul2 : (n - 1) * 2 ^ W + 2 ^ W = n * 2 ^ W := by
    have : ((n - 1) + 1) * 2 ^ W = (n - 1) * 2 ^ W + 1 * 2 ^ W := Nat.add_mul _ _ _
    rw [show (n - 1) + 1 = n from by omega] at this
    omega
  have hmn2 : m * 2 ^ W ≤ n * 2 ^ W := Nat.mul_le_mul_right _ hmn
  -- m = n
  have hmn_eq : m = n := by
    rcases Nat.lt_or_ge m n with hlt | hge
    · exfalso
      -- ΣA ≥ (n-1)·2^W but ΣA ≤ m(2^W - 1) ≤ (n-1)(2^W - 1)
      have hm_le : m ≤ n - 1 := by omega
      have h1 : m * (2 ^ W - 1) ≤ (n - 1) * (2 ^ W - 1) :=
        Nat.mul_le_mul_right _ hm_le
      have h2 : (n - 1) * (2 ^ W - 1) + (n - 1) = (n - 1) * 2 ^ W := by
        have h3 : (n - 1) * ((2 ^ W - 1) + 1) = (n - 1) * (2 ^ W - 1) + (n - 1) := by
          rw [Nat.mul_add]
          omega
        rw [← h3]
        congr 1
        omega
      omega
    · omega
  subst hmn_eq
  refine ⟨?_, hlenW, hposleaf, ?_⟩
  · -- every leaf is coded: counts agree, use the pointwise converse
    intro s hsN hleaf
    have hconv := countP_eq_of_imp (fun s => decide (1 ≤ lenOfF F s)) isLeaf (List.range N)
      (fun x _ hp => (hposleaf x (of_decide_eq_true hp)).2)
      (by rw [hm, hnleaf])
      s (List.mem_range.mpr hsN) hleaf
    exact of_decide_eq_true hconv
  · -- Kraft: K ≤ 2^W
    omega

/-
## Bridging to the real `packageMergeLengths`: leaf-list facts, loop characterizations,
## flatten/count algebra.
-/

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The leaf list `packageMergeLengths` builds, over an arbitrary index list. -/
def pmLeavesOf (freqs : Array Nat) (l : List Nat) : List PMNode :=
  l.filterMap fun s =>
    if freqs[s]! > 0 then some { weight := freqs[s]!, syms := [s] } else none

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The unsorted leaf list `packageMergeLengths` builds. -/
def pmLeaves (freqs : Array Nat) : List PMNode :=
  pmLeavesOf freqs (List.range freqs.size)

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The weight-sorted leaf list `packageMergeLengths` works from. -/
def pmSorted (freqs : Array Nat) : List PMNode :=
  (pmLeaves freqs).mergeSort (fun a b => a.weight ≤ b.weight)

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Every sorted leaf is a singleton over an in-range, used symbol. -/
theorem pmSorted_shape (freqs : Array Nat) {x : PMNode} (hx : x ∈ pmSorted freqs) :
    ∃ s, s < freqs.size ∧ 0 < freqs[s]! ∧ x = { weight := freqs[s]!, syms := [s] } := by
  have hx' : x ∈ pmLeaves freqs := List.mem_mergeSort.mp hx
  obtain ⟨s, hs, hfs⟩ := List.mem_filterMap.mp hx'
  by_cases hpos : freqs[s]! > 0
  · rw [if_pos hpos] at hfs
    exact ⟨s, List.mem_range.mp hs, hpos, (Option.some.injEq .. ▸ hfs).symm⟩
  · rw [if_neg hpos] at hfs
    exact absurd hfs (by simp)

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The sorted leaf count is the number of used symbols. -/
theorem pmSorted_length (freqs : Array Nat) :
    (pmSorted freqs).length =
      (List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)) := by
  unfold pmSorted pmLeaves pmLeavesOf
  rw [List.length_mergeSort, List.length_filterMap_eq_countP]
  apply List.countP_congr
  intro s _
  by_cases hpos : freqs[s]! > 0
  · rw [if_pos hpos]
    simp [hpos]
  · rw [if_neg hpos]
    simp
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Duplicate-free index lists give at most one leaf per symbol. -/
theorem pmLeavesOf_count_le (freqs : Array Nat) (s : Nat) : ∀ (l : List Nat),
    ((pmLeavesOf freqs l).map (fun x => x.syms.count s)).sum ≤ l.count s := by
  intro l
  induction l with
  | nil => simp [pmLeavesOf]
  | cons t l ih =>
    have hstep : pmLeavesOf freqs (t :: l) =
        (if freqs[t]! > 0 then [({ weight := freqs[t]!, syms := [t] } : PMNode)] else []) ++
          pmLeavesOf freqs l := by
      unfold pmLeavesOf
      rw [List.filterMap_cons]
      by_cases hpos : freqs[t]! > 0
      · rw [if_pos hpos, if_pos hpos]
        rfl
      · rw [if_neg hpos, if_neg hpos]
        rfl
    rw [hstep, List.map_append, List.sum_append, List.count_cons]
    by_cases hpos : freqs[t]! > 0
    · rw [if_pos hpos]
      have hone : ((([({ weight := freqs[t]!, syms := [t] } : PMNode)]) : List PMNode).map
          (fun x => x.syms.count s)).sum = ([t] : List Nat).count s := by
        simp
      rw [hone]
      have hcnt : (([t] : List Nat).count s) ≤ if (t == s) = true then 1 else 0 := by
        by_cases hts : t = s
        · subst hts
          simp
        · have h1 : ((t : Nat) == s) = false := by simp [hts]
          rw [h1, List.count_cons, if_neg (by rw [h1]; simp)]
          simp
      omega
    · rw [if_neg hpos]
      simp only [List.map_nil, List.sum_nil, Nat.zero_add]
      omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- `List.range` holds each value at most once. -/
theorem count_range_le_one (s : Nat) : ∀ (N : Nat), (List.range N).count s ≤ 1 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.count_append]
    by_cases hs : N = s
    · subst hs
      have hzero : (List.range N).count N = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        exact absurd (List.mem_range.mp hmem) (by omega)
      rw [hzero]
      simp
    · have h1 : ((N : Nat) == s) = false := by simp [hs]
      have h2 : ([N].count s) = 0 := by
        rw [List.count_cons, h1]
        simp
      omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The sorted leaf list mentions each symbol at most once in total. -/
theorem pmSorted_once (freqs : Array Nat) (s : Nat) :
    ((pmSorted freqs).map (fun x => x.syms.count s)).sum ≤ 1 := by
  have hperm : ((pmSorted freqs).map (fun x => x.syms.count s)).Perm
      ((pmLeaves freqs).map (fun x => x.syms.count s)) :=
    (List.mergeSort_perm (pmLeaves freqs) _).map _
  rw [hperm.sum_nat]
  have h1 := pmLeavesOf_count_le freqs s (List.range freqs.size)
  have h2 := count_range_le_one s freqs.size
  unfold pmLeaves
  omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Incrementing an array cell per listed symbol adds each symbol's multiplicity. -/
theorem foldl_incr_syms : ∀ (syms : List Nat) (arr : Array Nat),
    (∀ s ∈ syms, s < arr.size) →
    (syms.foldl (fun a s => a.set! s (a[s]! + 1)) arr).size = arr.size ∧
    ∀ t, t < arr.size →
      (syms.foldl (fun a s => a.set! s (a[s]! + 1)) arr)[t]! = arr[t]! + syms.count t := by
  intro syms
  induction syms with
  | nil =>
    intro arr _
    exact ⟨rfl, fun t _ => by simp⟩
  | cons s syms ih =>
    intro arr hin
    have hs := hin s (by simp)
    have hrec := ih (arr.set! s (arr[s]! + 1))
      (fun x hx => by rw [size_set!]; exact hin x (by simp [hx]))
    rw [size_set!] at hrec
    refine ⟨hrec.1, ?_⟩
    intro t ht
    rw [List.foldl_cons, hrec.2 t ht, List.count_cons]
    by_cases hts : s = t
    · subst hts
      rw [getElem!_set!_eq _ _ _ hs]
      have h1 : ((s : Nat) == s) = true := by simp
      rw [h1, if_pos rfl]
      omega
    · rw [getElem!_set!_ne _ _ _ _ hts]
      have h1 : ((s : Nat) == t) = false := by simp [hts]
      rw [h1, if_neg (by simp)]
      omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The nested per-item increment loop totals each symbol's multiplicity across items. -/
theorem foldl_incr_items : ∀ (items : List PMNode) (arr : Array Nat),
    (∀ it ∈ items, ∀ s ∈ it.syms, s < arr.size) →
    (items.foldl (fun a it => it.syms.foldl (fun a s => a.set! s (a[s]! + 1)) a) arr).size
      = arr.size ∧
    ∀ t, t < arr.size →
      (items.foldl (fun a it => it.syms.foldl (fun a s => a.set! s (a[s]! + 1)) a) arr)[t]!
        = arr[t]! + ((items.map (fun it => it.syms.count t)).sum) := by
  intro items
  induction items with
  | nil =>
    intro arr _
    exact ⟨rfl, fun t _ => by simp⟩
  | cons it items ih =>
    intro arr hin
    have hone := foldl_incr_syms it.syms arr (hin it (by simp))
    have hrec := ih (it.syms.foldl (fun a s => a.set! s (a[s]! + 1)) arr)
      (fun x hx s hs => by rw [hone.1]; exact hin x (by simp [hx]) s hs)
    rw [hone.1] at hrec
    refine ⟨hrec.1, ?_⟩
    intro t ht
    rw [List.foldl_cons, hrec.2 t ht, hone.2 t ht, List.map_cons, List.sum_cons]
    omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Counting in a flattened annotation list is the ghost count. -/
theorem count_flatMap_syms (e : Nat × Nat) : ∀ (T : List PMG),
    ((T.flatMap (fun g => g.syms)).count e) = ghostCount e T := by
  intro T
  induction T with
  | nil => rfl
  | cons g T ih =>
    rw [List.flatMap_cons, List.count_append, ih]
    rfl

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- `countP` distributes over flattening. -/
theorem countP_flatMap_syms (p : Nat × Nat → Bool) : ∀ (T : List PMG),
    ((T.flatMap (fun g => g.syms)).countP p) = ((T.map (fun g => g.syms.countP p)).sum) := by
  intro T
  induction T with
  | nil => rfl
  | cons g T ih =>
    rw [List.flatMap_cons, List.countP_append, ih, List.map_cons, List.sum_cons]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Mapped sums distribute over flattening. -/
theorem sum_map_flatMap_syms (f : Nat × Nat → Nat) : ∀ (T : List PMG),
    (((T.flatMap (fun g => g.syms)).map f).sum) =
      ((T.map (fun g => ((g.syms.map f).sum))).sum) := by
  intro T
  induction T with
  | nil => rfl
  | cons g T ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Counting a symbol among projected annotations. -/
theorem count_map_fst (t : Nat) : ∀ (l : List (Nat × Nat)),
    ((l.map Prod.fst).count t) = l.countP (fun e => e.1 == t) := by
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.map_cons, List.count_cons, ih, List.countP_cons]

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Ghost counts only shrink on prefixes. -/
theorem ghostCount_take_le (e : Nat × Nat) (k : Nat) : ∀ (L : List PMG),
    ghostCount e (L.take k) ≤ ghostCount e L := by
  intro L
  have hsplit : ghostCount e (L.take k) + ghostCount e (L.drop k) = ghostCount e L := by
    unfold ghostCount
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  omega

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- Sums of a constant-valued map. -/
theorem sum_map_const_of {α : Type} (f : α → Nat) (v : Nat) : ∀ (l : List α),
    (∀ x ∈ l, f x = v) → (l.map f).sum = l.length * v := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    rw [List.map_cons, List.sum_cons, h a (by simp), ih (fun x hx => h x (by simp [hx])),
      List.length_cons, Nat.add_mul]
    omega

/-
## The real `packageMergeLengths`, reduced to its general branch and specified.
-/

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- The general (`n ≥ 2`) branch of `packageMergeLengths`, with the imperative loops in
    `foldl` form. -/
def pmgLengths (freqs : Array Nat) (W : Nat) : Array Nat :=
  ((((List.range (W - 1)).foldl
      (fun cur _ => pmMerge (pmSorted freqs) (pmPackage cur)) (pmSorted freqs)).take
        (2 * (pmSorted freqs).length - 2)).foldl
    (fun arr it => it.syms.foldl (fun arr s => arr.set! s (arr[s]! + 1)) arr)
    (Array.replicate freqs.size 0))

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- With at least two sorted leaves, `packageMergeLengths` is its general branch. -/
theorem packageMergeLengths_eq_general (freqs : Array Nat) (W : Nat) (a b : PMNode)
    (rest : List PMNode) (hS : pmSorted freqs = a :: b :: rest) :
    packageMergeLengths freqs W = pmgLengths freqs W := by
  have hS' := hS
  unfold pmSorted pmLeaves pmLeavesOf at hS'
  unfold packageMergeLengths pmgLengths pmSorted pmLeaves pmLeavesOf
  dsimp only
  rw [hS']
  dsimp only
  simp only [List.forIn_pure_yield_eq_foldl, Id.run, pure_bind, bind_pure]
  rfl

/- REF: docs/STDLIB_ZLIB.md#311-length-limited-code-length-computation-encoder-side -/
/-- **L2v — package-merge validity.** With `n ≥ 2` used symbols and `n - 1 < 2^(W-1)`
    (`n ≤ 286`, `W = 15` for the literal/length alphabet; `n ≤ 30` and `n ≤ 19` for the
    others — all comfortably inside), `packageMergeLengths freqs W`:
    keeps the array size; codes every used symbol (`length ≥ 1`); stays within `W` bits
    everywhere; codes only used symbols; and satisfies the Kraft inequality
    `Σ 2^(W - len_s) ≤ 2^W` over the coded symbols. -/
theorem packageMergeLengths_spec (freqs : Array Nat) (W : Nat) (hW : 1 ≤ W)
    (hn2 : 2 ≤ (List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)))
    (hsmall : (List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)) - 1
      < 2 ^ (W - 1)) :
    (packageMergeLengths freqs W).size = freqs.size ∧
    (∀ s, s < freqs.size → 0 < freqs[s]! → 1 ≤ (packageMergeLengths freqs W)[s]!) ∧
    (∀ s, s < freqs.size → (packageMergeLengths freqs W)[s]! ≤ W) ∧
    (∀ s, s < freqs.size → 0 < (packageMergeLengths freqs W)[s]! → 0 < freqs[s]!) ∧
    ((List.range freqs.size).map (fun s =>
        if 1 ≤ (packageMergeLengths freqs W)[s]! then
          2 ^ (W - (packageMergeLengths freqs W)[s]!) else 0)).sum ≤ 2 ^ W := by
  have hlen := pmSorted_length freqs
  -- the sorted list has at least two leaves: extract its cons-cons shape
  obtain ⟨a, b, rest, hS⟩ : ∃ a b rest, pmSorted freqs = a :: b :: rest := by
    cases hL : pmSorted freqs with
    | nil =>
      rw [hL] at hlen
      simp at hlen
      omega
    | cons a t =>
      cases t with
      | nil =>
        rw [hL] at hlen
        simp at hlen
        omega
      | cons b rest => exact ⟨a, b, rest, rfl⟩
  rw [packageMergeLengths_eq_general freqs W a b rest hS]
  unfold pmgLengths
  -- notation
  have hQ : ∀ x ∈ pmSorted freqs, ∀ s ∈ x.syms, s < freqs.size ∧ 0 < freqs[s]! := by
    intro x hx s hs
    obtain ⟨t, htN, htf, hxe⟩ := pmSorted_shape freqs hx
    rw [hxe] at hs
    have hst : s = t := by
      rcases List.mem_singleton.mp hs with h
      exact h
    subst hst
    exact ⟨htN, htf⟩
  have hone : ∀ x ∈ pmSorted freqs, x.syms.length = 1 := by
    intro x hx
    obtain ⟨t, _, _, hxe⟩ := pmSorted_shape freqs hx
    rw [hxe]
    rfl
  have hann := annAll_ghostLevels (pmSorted freqs)
    (fun s => s < freqs.size ∧ 0 < freqs[s]!) hQ (W - 1)
  have hproj := ghostLevels_proj (pmSorted freqs) (W - 1)
  -- the solution prefix, in ghost form
  have hsol : (((List.range (W - 1)).foldl
      (fun cur _ => pmMerge (pmSorted freqs) (pmPackage cur)) (pmSorted freqs)).take
        (2 * (pmSorted freqs).length - 2)) =
      ((ghostLevels (pmSorted freqs) (W - 1)).take
        (2 * (pmSorted freqs).length - 2)).map pmProj := by
    rw [List.map_take, hproj]
  rw [hsol]
  -- names for the ghost prefix and its annotation multiset
  have hchar : ∀ t, t < freqs.size →
      ((((ghostLevels (pmSorted freqs) (W - 1)).take
          (2 * (pmSorted freqs).length - 2)).map pmProj).foldl
        (fun arr it => it.syms.foldl (fun arr s => arr.set! s (arr[s]! + 1)) arr)
        (Array.replicate freqs.size 0))[t]!
      = lenOfF (((ghostLevels (pmSorted freqs) (W - 1)).take
          (2 * (pmSorted freqs).length - 2)).flatMap (fun g => g.syms)) t := by
    intro t htN
    have hbound : ∀ it ∈ (((ghostLevels (pmSorted freqs) (W - 1)).take
        (2 * (pmSorted freqs).length - 2)).map pmProj),
        ∀ s ∈ it.syms, s < (Array.replicate freqs.size 0).size := by
      intro it hit s hs
      rw [Array.size_replicate]
      obtain ⟨g, hg, hge⟩ := List.mem_map.mp hit
      rw [← hge] at hs
      obtain ⟨e, he, hes⟩ := List.mem_map.mp hs
      have hgL : g ∈ ghostLevels (pmSorted freqs) (W - 1) :=
        List.mem_of_mem_take hg
      have := hann g hgL e he
      rw [← hes]
      exact this.2.2.1
    have hf := foldl_incr_items _ (Array.replicate freqs.size 0) hbound
    rw [Array.size_replicate] at hf
    rw [hf.2 t htN, getElem!_replicate _ _ _ htN]
    -- per-item counts through the projection
    have hcnt : ((((ghostLevels (pmSorted freqs) (W - 1)).take
        (2 * (pmSorted freqs).length - 2)).map pmProj).map
          (fun it => it.syms.count t)).sum
        = lenOfF (((ghostLevels (pmSorted freqs) (W - 1)).take
            (2 * (pmSorted freqs).length - 2)).flatMap (fun g => g.syms)) t := by
      rw [List.map_map]
      unfold lenOfF
      rw [countP_flatMap_syms]
      apply sum_map_congr
      intro g _
      show (pmProj g).syms.count t = g.syms.countP (fun e => e.1 == t)
      unfold pmProj
      exact count_map_fst t g.syms
    rw [hcnt]
    omega
  -- apply the master counting theorem
  have hlenL := ghostLevels_length (pmSorted freqs)
    (by rw [hS, List.length_cons, List.length_cons]; omega) (W - 1)
  have hdiv0 : ((pmSorted freqs).length - 1) / 2 ^ (W - 1) = 0 :=
    Nat.div_eq_of_lt (by rw [hlen]; exact hsmall)
  rw [hdiv0] at hlenL
  have htklen : (((ghostLevels (pmSorted freqs) (W - 1)).take
      (2 * (pmSorted freqs).length - 2))).length = 2 * (pmSorted freqs).length - 2 := by
    rw [List.length_take, hlenL]
    have h2 : 2 ≤ (pmSorted freqs).length := by
      rw [hS, List.length_cons, List.length_cons]
      omega
    omega
  have hmaster := master_counting W freqs.size
    ((List.range freqs.size).countP (fun s => decide (0 < freqs[s]!)))
    (fun s => decide (0 < freqs[s]!)) hW hn2
    (((ghostLevels (pmSorted freqs) (W - 1)).take
      (2 * (pmSorted freqs).length - 2)).flatMap (fun g => g.syms))
    (by
      intro e he
      obtain ⟨g, hg, hge⟩ := List.mem_flatMap.mp he
      have hgL : g ∈ ghostLevels (pmSorted freqs) (W - 1) := List.mem_of_mem_take hg
      have h := hann g hgL e hge
      have hWe : W - 1 + 1 = W := by omega
      exact ⟨h.2.2.1, h.1, by omega⟩)
    (by
      intro s j
      rw [count_flatMap_syms]
      have h1 := ghostCount_take_le (s, j) (2 * (pmSorted freqs).length - 2)
        (ghostLevels (pmSorted freqs) (W - 1))
      have h2 := ghostCount_ghostLevels_le_one (pmSorted freqs)
        (fun s => pmSorted_once freqs s) (W - 1) s j
      omega)
    (by
      intro e he
      obtain ⟨g, hg, hge⟩ := List.mem_flatMap.mp he
      have hgL : g ∈ ghostLevels (pmSorted freqs) (W - 1) := List.mem_of_mem_take hg
      have h := hann g hgL e hge
      exact decide_eq_true h.2.2.2)
    rfl
    (by
      rw [sum_map_flatMap_syms]
      have hval : ∀ g ∈ (((ghostLevels (pmSorted freqs) (W - 1)).take
          (2 * (pmSorted freqs).length - 2))),
          ((g.syms.map (fun e => 2 ^ (e.2 - 1))).sum) = 2 ^ (W - 1) := by
        intro g hg
        have hgL : g ∈ ghostLevels (pmSorted freqs) (W - 1) := List.mem_of_mem_take hg
        exact itemVal_ghostLevels (pmSorted freqs) hone (W - 1) g hgL
      rw [sum_map_const_of _ _ _ hval, htklen, hlen])
  obtain ⟨hcov, hlenW, hposv, hkraft⟩ := hmaster
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- size
    have hbound : ∀ it ∈ (((ghostLevels (pmSorted freqs) (W - 1)).take
        (2 * (pmSorted freqs).length - 2)).map pmProj),
        ∀ s ∈ it.syms, s < (Array.replicate freqs.size 0).size := by
      intro it hit s hs
      rw [Array.size_replicate]
      obtain ⟨g, hg, hge⟩ := List.mem_map.mp hit
      rw [← hge] at hs
      obtain ⟨e, he, hes⟩ := List.mem_map.mp hs
      have hgL : g ∈ ghostLevels (pmSorted freqs) (W - 1) := List.mem_of_mem_take hg
      have := hann g hgL e he
      rw [← hes]
      exact this.2.2.1
    have hf := foldl_incr_items _ (Array.replicate freqs.size 0) hbound
    rw [Array.size_replicate] at hf
    exact hf.1
  · -- coverage
    intro s hsN hsf
    rw [hchar s hsN]
    exact hcov s hsN (decide_eq_true hsf)
  · -- width bound
    intro s hsN
    rw [hchar s hsN]
    exact hlenW s
  · -- only used symbols are coded
    intro s hsN hpos
    rw [hchar s hsN] at hpos
    exact of_decide_eq_true (hposv s (by omega)).2
  · -- Kraft
    have hcongr : ((List.range freqs.size).map (fun s =>
        if 1 ≤ ((((ghostLevels (pmSorted freqs) (W - 1)).take
            (2 * (pmSorted freqs).length - 2)).map pmProj).foldl
          (fun arr it => it.syms.foldl (fun arr s => arr.set! s (arr[s]! + 1)) arr)
          (Array.replicate freqs.size 0))[s]! then
          2 ^ (W - ((((ghostLevels (pmSorted freqs) (W - 1)).take
              (2 * (pmSorted freqs).length - 2)).map pmProj).foldl
            (fun arr it => it.syms.foldl (fun arr s => arr.set! s (arr[s]! + 1)) arr)
            (Array.replicate freqs.size 0))[s]!) else 0)).sum =
        ((List.range freqs.size).map (fun s =>
          if 1 ≤ lenOfF (((ghostLevels (pmSorted freqs) (W - 1)).take
              (2 * (pmSorted freqs).length - 2)).flatMap (fun g => g.syms)) s then
            2 ^ (W - lenOfF (((ghostLevels (pmSorted freqs) (W - 1)).take
              (2 * (pmSorted freqs).length - 2)).flatMap (fun g => g.syms)) s) else 0)).sum := by
      apply sum_map_congr
      intro s hs
      rw [hchar s (List.mem_range.mp hs)]
    rw [hcongr]
    exact hkraft

end Stdlib.Zlib

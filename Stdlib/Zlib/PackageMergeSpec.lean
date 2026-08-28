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

end Stdlib.Zlib

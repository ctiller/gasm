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
import Stdlib.Zlib.Equivalence

/-
## PA16 L2d: canonical decode inverts encode for arbitrary transmitted lengths

The general prefix-tree argument the fixed-table L2 deliberately avoided: for ANY code-length
array satisfying the Kraft inequality (with all lengths within `maxBits`), the canonical
Huffman table `buildHuffmanTable` constructs assigns each valid symbol the canonical code
`startCode(len) + rank-within-length`, that code fits its width, and the decode tree walks the
symbol's emitted bit path (MSB-first, i.e. `natBits len (reverseBits code len)`) back to
exactly that symbol. Everything is a kernel-checked structural induction — no `decide`
enumeration is possible here, since the length array is data-dependent at `compress` time.

Proof architecture:
1. `codeBits` — the MSB-first bit path of a code, with `natBits len (reverseBits code len) =
   codeBits code len` bridging to the emitter's LSB-first packing of the bit-reversed code.
2. `insertCode` self-decode + non-disturbance: inserting a code makes its own path decode to
   its symbol, and preserves every path that is prefix-incomparable with the inserted one.
3. Canonical code arithmetic: `startCodeF`/`blCountF`/`rankF` closed forms for the imperative
   `buildHuffmanTable` steps 1–2, and the block-disjointness consequences of the Kraft bound
   (codes of one length occupy an interval that ends where the next length's block begins),
   giving pairwise prefix-incomparability of all assigned codes.
4. The `buildHuffmanTreeAssign` induction carrying (a) the live `nextCode` counters, (b) the
   assigned `codes` entries, (c) decode-tree correctness for every assigned symbol.
-/

namespace Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `Array.set!` then read back at the same in-bounds index. -/
theorem getElem!_set!_eq {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (v : α)
    (h : i < arr.size) : (arr.set! i v)[i]! = v := by
  simp [Array.set!, Array.getElem!_eq_getD, Array.getD, h]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `Array.set!` leaves every other index unchanged (in or out of bounds). -/
theorem getElem!_set!_ne {α : Type} [Inhabited α] (arr : Array α) (i j : Nat) (v : α)
    (hne : i ≠ j) : (arr.set! i v)[j]! = arr[j]! := by
  have h? : (arr.set! i v)[j]? = arr[j]? := by
    rw [Array.set!, Array.getElem?_setIfInBounds, if_neg hne]
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, h?]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `Array.set!` preserves size. -/
theorem size_set! {α : Type} (arr : Array α) (i : Nat) (v : α) :
    (arr.set! i v).size = arr.size := by
  simp [Array.set!]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Reading a replicated array. -/
theorem getElem!_replicate {α : Type} [Inhabited α] (n : Nat) (x : α) (i : Nat) (h : i < n) :
    (Array.replicate n x)[i]! = x := by
  simp [Array.getElem!_eq_getD, Array.getD, h]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Out-of-bounds `get!` returns the default value. -/
theorem getElem!_oob {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (h : ¬ i < arr.size) :
    arr[i]! = default := by
  simp [Array.getElem!_eq_getD, Array.getD, h]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- MSB-first bit path of the low `len` bits of `code` — the path a canonical code descends
    in the decode tree (`insertCode` peels the MSB first), and, via `natBits_reverseBits`
    below, exactly the LSB-first window of the bit-reversed code the emitter writes. -/
def codeBits (code : Nat) : Nat → List Bool
  | 0 => []
  | l + 1 => (((code >>> l) &&& 1) == 1) :: codeBits code l

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `codeBits` windows have their stated width. -/
theorem codeBits_length (code : Nat) : ∀ len, (codeBits code len).length = len := by
  intro len
  induction len with
  | zero => rfl
  | succ l ih => simp [codeBits, ih]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Structural recursion twin of `reverseBits`' imperative loop: `n` iterations of
    "shift the accumulated reversal up, append the source's LSB, drop it from the source". -/
def revAux : Nat → Nat → Nat → Nat
  | 0, res, _ => res
  | n + 1, res, c => revAux n (2 * res + (c &&& 1)) (c >>> 1)

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `revAux` unfolding at a positive count. -/
theorem revAux_step (n res c : Nat) :
    revAux (n + 1) res c = revAux n (2 * res + (c &&& 1)) (c >>> 1) := rfl

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The imperative `reverseBits` loop is `revAux`. -/
theorem reverseBits_eq_revAux (code len : Nat) : reverseBits code len = revAux len 0 code := by
  have hgen : ∀ (l : List Nat) (res c : Nat),
      (l.foldl (fun (p : Nat × Nat) _ => ((p.1 <<< 1) ||| (p.2 &&& 1), p.2 >>> 1)) (res, c)).1
        = revAux l.length res c := by
    intro l
    induction l with
    | nil => intro res c; rfl
    | cons x xs ih =>
      intro res c
      rw [List.foldl_cons, List.length_cons]
      dsimp only
      have hstep : (res <<< 1) ||| (c &&& 1) = 2 * res + (c &&& 1) := by
        have hb : c &&& 1 < 2 ^ 1 := by
          rw [Nat.and_one_is_mod]
          have := Nat.mod_lt c (y := 2) (by omega)
          omega
        rw [Nat.or_comm, lor_shiftLeft_eq_add hb]
        have h2 : (2 : Nat) ^ 1 = 2 := rfl
        omega
      rw [hstep, revAux_step]
      exact ih (2 * res + (c &&& 1)) (c >>> 1)
  unfold reverseBits
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Id.run, pure_bind]
  simpa using hgen (List.range' 0 len 1) 0 code

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Peeling `revAux` from the top: one more reversal step contributes the source's bit `n`
    at the bottom of the doubled result. -/
theorem revAux_succ : ∀ (n res c : Nat),
    revAux (n + 1) res c = 2 * revAux n res c + ((c >>> n) &&& 1) := by
  intro n
  induction n with
  | zero =>
    intro res c
    show revAux 0 (2 * res + (c &&& 1)) (c >>> 1) = 2 * res + ((c >>> 0) &&& 1)
    rw [Nat.shiftRight_zero]
    rfl
  | succ n ih =>
    intro res c
    rw [revAux_step, ih (2 * res + (c &&& 1)) (c >>> 1), revAux_step]
    have h1 : c >>> 1 >>> n = c >>> (n + 1) := by
      rw [← Nat.shiftRight_add]
      congr 1
      omega
    rw [h1]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The reversal of any code fits its width — unconditionally (only `len` bits are ever
    accumulated). -/
theorem revAux_lt (len : Nat) : ∀ (res c : Nat), revAux len res c < (res + 1) * 2 ^ len := by
  induction len with
  | zero => intro res c; simp [revAux]
  | succ l ih =>
    intro res c
    rw [revAux_step]
    have hb : c &&& 1 ≤ 1 := by rw [Nat.and_one_is_mod]; omega
    have h := ih (2 * res + (c &&& 1)) (c >>> 1)
    have hle : (2 * res + (c &&& 1) + 1) * 2 ^ l ≤ (res + 1) * 2 ^ (l + 1) := by
      have h1 : 2 * res + (c &&& 1) + 1 ≤ (res + 1) * 2 := by omega
      have h2 : (2 * res + (c &&& 1) + 1) * 2 ^ l ≤ ((res + 1) * 2) * 2 ^ l :=
        Nat.mul_le_mul_right _ h1
      have h3 : ((res + 1) * 2) * 2 ^ l = (res + 1) * 2 ^ (l + 1) := by
        rw [Nat.mul_assoc, Nat.pow_succ, Nat.mul_comm 2 (2 ^ l)]
      rw [h3] at h2
      exact h2
    omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `reverseBits code len` fits in `len` bits, for every `code`. -/
theorem reverseBits_lt (code len : Nat) : reverseBits code len < 2 ^ len := by
  rw [reverseBits_eq_revAux]
  have := revAux_lt len 0 code
  simpa using this

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The bridge from the emitter's LSB-first window of the bit-reversed code to the decode
    tree's MSB-first path: they are the same `List Bool`. -/
theorem natBits_reverseBits (code : Nat) : ∀ len, natBits len (reverseBits code len) = codeBits code len := by
  have main : ∀ len, natBits len (revAux len 0 code) = codeBits code len := by
    intro len
    induction len with
    | zero => rfl
    | succ l ih =>
      have hrec := revAux_succ l 0 code
      have hb : (code >>> l) &&& 1 ≤ 1 := by rw [Nat.and_one_is_mod]; omega
      have hmod : revAux (l + 1) 0 code % 2 = (code >>> l) &&& 1 := by omega
      have hdiv : revAux (l + 1) 0 code / 2 = revAux l 0 code := by omega
      show (revAux (l + 1) 0 code % 2 == 1) :: natBits l (revAux (l + 1) 0 code / 2) = _
      rw [hmod, hdiv, ih]
      rfl
  intro len
  rw [reverseBits_eq_revAux]
  exact main len

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Each `codeBits` entry is the corresponding `Nat.testBit` of the code. -/
theorem codeBits_head_eq_testBit (c l : Nat) :
    (((c >>> l) &&& 1) == 1) = c.testBit l := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ l) with h | h <;> rw [h] <;> rfl

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Splitting a code path: the high `a` bits are the path of the shifted code. -/
theorem codeBits_append (c : Nat) : ∀ (a b : Nat),
    codeBits c (a + b) = codeBits (c >>> b) a ++ codeBits c b := by
  intro a
  induction a with
  | zero => intro b; simp [codeBits]
  | succ a ih =>
    intro b
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    show (((c >>> (a + b)) &&& 1) == 1) :: codeBits c (a + b) = _
    rw [ih b]
    show _ = ((((c >>> b) >>> a) &&& 1) == 1) :: (codeBits (c >>> b) a ++ codeBits c b)
    rw [← Nat.shiftRight_add]
    have e2 : b + a = a + b := by omega
    rw [e2]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Equal `l`-bit paths force `testBit` agreement below `l`. -/
theorem codeBits_testBit_eq {c c' : Nat} : ∀ {l : Nat}, codeBits c l = codeBits c' l →
    ∀ i, i < l → c.testBit i = c'.testBit i := by
  intro l
  induction l with
  | zero => intro _ i hi; omega
  | succ l ih =>
    intro h i hi
    simp only [codeBits, List.cons.injEq] at h
    rcases Nat.lt_or_ge i l with hil | hil
    · exact ih h.2 i hil
    · have hieq : i = l := by omega
      subst hieq
      rw [← codeBits_head_eq_testBit, ← codeBits_head_eq_testBit]
      exact h.1

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Codes below `2^l` are recovered exactly from their `l`-bit MSB-first path. -/
theorem codeBits_inj {l c c' : Nat} (hc : c < 2 ^ l) (hc' : c' < 2 ^ l)
    (h : codeBits c l = codeBits c' l) : c = c' := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i l with hil | hil
  · exact codeBits_testBit_eq h i hil
  · have h1 : c < 2 ^ i := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hil)
    have h2 : c' < 2 ^ i := Nat.lt_of_lt_of_le hc' (Nat.pow_le_pow_right (by omega) hil)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A shorter code path prefixes a longer one exactly when the shorter code is the longer
    one's high bits — the arithmetic form the block-disjointness argument refutes. -/
theorem codeBits_prefix_shift {c c' l l' : Nat} (hl : l' ≤ l) (hc : c < 2 ^ l)
    (hpre : codeBits c' l' <+: codeBits c l) : c' % 2 ^ l' = c >>> (l - l') := by
  have hd : l = l' + (l - l') := by omega
  have hsplit : codeBits c l = codeBits (c >>> (l - l')) l' ++ codeBits c (l - l') := by
    conv => lhs; rw [hd]
    exact codeBits_append c l' (l - l')
  rw [hsplit] at hpre
  have heq : codeBits c' l' = codeBits (c >>> (l - l')) l' := by
    have h1 := List.prefix_iff_eq_take.mp hpre
    rw [codeBits_length] at h1
    rw [h1, List.take_append_of_le_length (by simp [codeBits_length]),
      List.take_of_length_le (by simp [codeBits_length])]
  -- codeBits only sees the low l' bits of c'
  have hmod : codeBits (c' % 2 ^ l') l' = codeBits c' l' := by
    have hgen : ∀ ll, ll ≤ l' → codeBits (c' % 2 ^ l') ll = codeBits c' ll := by
      intro ll
      induction ll with
      | zero => intro _; rfl
      | succ ll ih =>
        intro hle
        simp only [codeBits]
        rw [ih (by omega)]
        congr 1
        rw [codeBits_head_eq_testBit, codeBits_head_eq_testBit,
          Nat.testBit_mod_two_pow]
        simp [show ll < l' by omega]
    exact hgen l' (Nat.le_refl _)
  rw [← hmod] at heq
  have hshift_lt : c >>> (l - l') < 2 ^ l' := by
    rw [Nat.shiftRight_eq_div_pow]
    have : c < 2 ^ l' * 2 ^ (l - l') := by
      rw [← Nat.pow_add]
      have e : l' + (l - l') = l := by omega
      rw [e]
      exact hc
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact this)
  exact codeBits_inj (Nat.mod_lt _ (Nat.two_pow_pos l')) hshift_lt heq

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `treeWalk` into a `branch`'s occupied left child. -/
theorem treeWalk_branch_false (l : HuffmanNode) (r : Option HuffmanNode) (p : List Bool) :
    treeWalk (HuffmanNode.branch (some l) r) (false :: p) = treeWalk l p := by
  simp [treeWalk]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `treeWalk` into a `branch`'s vacant left child. -/
theorem treeWalk_branch_false_none (r : Option HuffmanNode) (p : List Bool) :
    treeWalk (HuffmanNode.branch none r) (false :: p) = none := by
  simp [treeWalk]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `treeWalk` into a `branch`'s occupied right child. -/
theorem treeWalk_branch_true (l : Option HuffmanNode) (r : HuffmanNode) (p : List Bool) :
    treeWalk (HuffmanNode.branch l (some r)) (true :: p) = treeWalk r p := by
  simp [treeWalk]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- `treeWalk` into a `branch`'s vacant right child. -/
theorem treeWalk_branch_true_none (l : Option HuffmanNode) (p : List Bool) :
    treeWalk (HuffmanNode.branch l none) (true :: p) = none := by
  simp [treeWalk]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A leaf resolves no nonempty path. -/
theorem treeWalk_leaf_cons (s : Nat) (b : Bool) (p : List Bool) :
    treeWalk (HuffmanNode.leaf s) (b :: p) = none := by
  cases b <;> simp [treeWalk]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A branch resolves no empty path. -/
theorem treeWalk_branch_nil (l r : Option HuffmanNode) :
    treeWalk (HuffmanNode.branch l r) [] = none := by
  simp [treeWalk]

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Self-decode: after inserting `(sym, code, len)`, the decode tree walks `code`'s own
    MSB-first path back to `sym` — for any starting tree. -/
theorem insertCode_loop_self (sym : Nat) : ∀ (len code : Nat) (node : HuffmanNode),
    treeWalk (insertCode.loop sym node code len) (codeBits code len) = some sym := by
  intro len
  induction len with
  | zero =>
    intro code node
    rw [insertCode.loop.eq_def]
    simp [treeWalk, codeBits]
  | succ len ih =>
    intro code node
    have hb : (code >>> len) &&& 1 ≤ 1 := by rw [Nat.and_one_is_mod]; omega
    simp only [codeBits]
    by_cases hbit : (code >>> len) &&& 1 = 0
    case pos =>
      have hif : ((code >>> len) &&& 1 == 0) = true := by rw [hbit]; rfl
      have hhead : (((code >>> len) &&& 1) == 1) = false := by rw [hbit]; rfl
      rw [insertCode.loop.eq_def]
      cases node with
      | leaf s =>
        simp only [hif, reduceIte]
        rw [hhead, treeWalk_branch_false]
        exact ih code _
      | branch l r =>
        simp only [hif, reduceIte]
        rw [hhead, treeWalk_branch_false]
        exact ih code _
    case neg =>
      have hbit1 : (code >>> len) &&& 1 = 1 := by omega
      have hif : ((code >>> len) &&& 1 == 0) = false := by rw [hbit1]; rfl
      have hhead : (((code >>> len) &&& 1) == 1) = true := by rw [hbit1]; rfl
      rw [insertCode.loop.eq_def]
      cases node with
      | leaf s =>
        simp only [hif]
        rw [if_neg (by simp : ¬ (false = true))]
        rw [hhead, treeWalk_branch_true]
        exact ih code _
      | branch l r =>
        simp only [hif]
        rw [if_neg (by simp : ¬ (false = true))]
        rw [hhead, treeWalk_branch_true]
        exact ih code _

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Non-disturbance: inserting a code whose path is prefix-incomparable with an existing
    resolvable path leaves that path resolving to the same symbol. -/
theorem insertCode_loop_preserve (sym : Nat) : ∀ (len code : Nat) (node : HuffmanNode)
    (p : List Bool) (s : Nat),
    treeWalk node p = some s →
    ¬ (codeBits code len <+: p) → ¬ (p <+: codeBits code len) →
    treeWalk (insertCode.loop sym node code len) p = some s := by
  intro len
  induction len with
  | zero =>
    intro code node p s _ hq _
    exact absurd List.nil_prefix hq
  | succ len ih =>
    intro code node p s hwalk hq hp
    cases p with
    | nil => exact absurd List.nil_prefix hp
    | cons pb p' =>
      have hb : (code >>> len) &&& 1 ≤ 1 := by rw [Nat.and_one_is_mod]; omega
      have hqcons : ∀ (b : Bool), (((code >>> len) &&& 1) == 1) = b →
          pb = b → ¬ (codeBits code len <+: p') := by
        intro b hb' hpb hcon
        apply hq
        show codeBits code (len + 1) <+: pb :: p'
        simp only [codeBits, hb', hpb]
        exact List.cons_prefix_cons.mpr ⟨rfl, hcon⟩
      have hpcons : ∀ (b : Bool), (((code >>> len) &&& 1) == 1) = b →
          pb = b → ¬ (p' <+: codeBits code len) := by
        intro b hb' hpb hcon
        apply hp
        show pb :: p' <+: codeBits code (len + 1)
        simp only [codeBits, hb', hpb]
        exact List.cons_prefix_cons.mpr ⟨rfl, hcon⟩
      cases node with
      | leaf s'' =>
        rw [treeWalk_leaf_cons] at hwalk
        exact absurd hwalk (by simp)
      | branch l r =>
        rw [insertCode.loop.eq_def]
        by_cases hbit : (code >>> len) &&& 1 = 0
        · -- insertion goes left (bit = 0)
          have hif : ((code >>> len) &&& 1 == 0) = true := by rw [hbit]; rfl
          have hhead : (((code >>> len) &&& 1) == 1) = false := by rw [hbit]; rfl
          simp only [hif, reduceIte]
          cases pb with
          | true =>
            cases r with
            | none => rw [treeWalk_branch_true_none] at hwalk; exact absurd hwalk (by simp)
            | some n =>
              rw [treeWalk_branch_true] at hwalk
              rw [treeWalk_branch_true]
              exact hwalk
          | false =>
            cases l with
            | none => rw [treeWalk_branch_false_none] at hwalk; exact absurd hwalk (by simp)
            | some n =>
              rw [treeWalk_branch_false] at hwalk
              rw [treeWalk_branch_false]
              exact ih code _ p' s hwalk (hqcons false hhead rfl) (hpcons false hhead rfl)
        · -- insertion goes right (bit = 1)
          have hbit1 : (code >>> len) &&& 1 = 1 := by omega
          have hif : ((code >>> len) &&& 1 == 0) = false := by rw [hbit1]; rfl
          have hhead : (((code >>> len) &&& 1) == 1) = true := by rw [hbit1]; rfl
          simp only [hif]
          rw [if_neg (by simp : ¬ (false = true))]
          cases pb with
          | false =>
            cases l with
            | none => rw [treeWalk_branch_false_none] at hwalk; exact absurd hwalk (by simp)
            | some n =>
              rw [treeWalk_branch_false] at hwalk
              rw [treeWalk_branch_false]
              exact hwalk
          | true =>
            cases r with
            | none => rw [treeWalk_branch_true_none] at hwalk; exact absurd hwalk (by simp)
            | some n =>
              rw [treeWalk_branch_true] at hwalk
              rw [treeWalk_branch_true]
              exact ih code _ p' s hwalk (hqcons true hhead rfl) (hpcons true hhead rfl)

/-
## Canonical code arithmetic (RFC 1951 §3.2.2): closed forms for `buildHuffmanTable`'s
## code-length counting (step 1) and starting-code (step 2) passes, plus the Kraft-bound
## consequences that make all assigned codes pairwise prefix-incomparable.
-/

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Number of symbols assigned code length `l` (RFC 1951 `bl_count[l]`), functional form.
    Zero outside the assignable range `1 ≤ l ≤ maxBits` — exactly step 1's guard. -/
def blCountF (lengths : Array Nat) (W l : Nat) : Nat :=
  if 1 ≤ l ∧ l ≤ W then (List.range lengths.size).countP (fun s => lengths[s]! == l) else 0

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Canonical starting code per length (RFC 1951 `next_code[l]` before any assignment),
    functional form of step 2's recurrence `code = (code + bl_count[bits-1]) << 1`. -/
def startCodeF (lengths : Array Nat) (W : Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => (startCodeF lengths W l + blCountF lengths W l) * 2

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Rank of `sym` among earlier symbols of its own code length — the number of codes of
    that length assigned before step 3 reaches `sym`. -/
def rankF (lengths : Array Nat) (sym : Nat) : Nat :=
  (List.range sym).countP (fun s => lengths[s]! == lengths[sym]!)

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The canonical code RFC 1951 §3.2.2 assigns to `sym`. -/
def canonicalCode (lengths : Array Nat) (W sym : Nat) : Nat :=
  startCodeF lengths W (lengths[sym]!) + rankF lengths sym

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A symbol is assignable when its length is positive and within the width limit. -/
def validLen (lengths : Array Nat) (W s : Nat) : Prop :=
  0 < lengths[s]! ∧ lengths[s]! ≤ W

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- The compact Kraft bound the whole L2d argument runs on: the last length's block ends
    within the code space. Implied by the Kraft inequality `Σ 2^(W-l) ≤ 2^W` (see the
    package-merge validity bridge), and trivially true for under-subscribed trees. -/
def kraftOk (lengths : Array Nat) (W : Nat) : Prop :=
  startCodeF lengths W W + blCountF lengths W W ≤ 2 ^ W

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A valid symbol is in bounds (out-of-bounds `get!` reads 0, an invalid length). -/
theorem validLen_lt_size {lengths : Array Nat} {W s : Nat} (h : validLen lengths W s) :
    s < lengths.size := by
  rcases Nat.lt_or_ge s lengths.size with h1 | h1
  · exact h1
  · exfalso
    have h0 := getElem!_oob lengths s (by omega)
    have h2 := h.1
    rw [h0] at h2
    exact absurd h2 (by simp [default])

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Ranks stay strictly below the length's total population. -/
theorem rankF_lt_blCountF {lengths : Array Nat} {W s : Nat} (h : validLen lengths W s) :
    rankF lengths s < blCountF lengths W (lengths[s]!) := by
  have hs := validLen_lt_size h
  have hstep : (List.range (s + 1)).countP (fun x => lengths[x]! == lengths[s]!) =
      (List.range s).countP (fun x => lengths[x]! == lengths[s]!) + 1 := by
    rw [List.range_succ, List.countP_append]
    simp [List.countP_cons]
  have hmono : (List.range (s + 1)).countP (fun x => lengths[x]! == lengths[s]!) ≤
      (List.range lengths.size).countP (fun x => lengths[x]! == lengths[s]!) :=
    List.Sublist.countP_le (List.range_sublist.mpr (by omega))
  unfold blCountF rankF
  rw [if_pos ⟨h.1, h.2⟩]
  omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Doubling chain for starting codes: each length's start dominates the shifted image of
    every earlier start. -/
theorem startCodeF_mul_le (lengths : Array Nat) (W l : Nat) :
    ∀ d, startCodeF lengths W l * 2 ^ d ≤ startCodeF lengths W (l + d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : startCodeF lengths W (l + d) * 2 ≤ startCodeF lengths W (l + (d + 1)) := by
      show startCodeF lengths W (l + d) * 2 ≤ startCodeF lengths W ((l + d) + 1)
      show _ ≤ (startCodeF lengths W (l + d) + blCountF lengths W (l + d)) * 2
      have := Nat.zero_le (blCountF lengths W (l + d))
      omega
    calc startCodeF lengths W l * 2 ^ (d + 1)
        = (startCodeF lengths W l * 2 ^ d) * 2 := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ startCodeF lengths W (l + d) * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ startCodeF lengths W (l + (d + 1)) := hstep

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- A length's block (start through start+count) ends no later than any deeper length's
    start, once scaled to a common depth. -/
theorem blockEnd_le_startCodeF (lengths : Array Nat) (W l d : Nat) :
    (startCodeF lengths W l + blCountF lengths W l) * 2 ^ (d + 1) ≤
      startCodeF lengths W (l + (d + 1)) := by
  have h1 : (startCodeF lengths W l + blCountF lengths W l) * 2 ^ (d + 1)
      = startCodeF lengths W (l + 1) * 2 ^ d := by
    show _ = (startCodeF lengths W l + blCountF lengths W l) * 2 * 2 ^ d
    rw [Nat.mul_assoc, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2]
  rw [h1]
  have h2 := startCodeF_mul_le lengths W (l + 1) d
  have e : l + 1 + d = l + (d + 1) := by omega
  rw [e] at h2
  exact h2

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Under the Kraft bound, every length's block fits inside its own code space:
    `start(l) + count(l) ≤ 2^l`. -/
theorem blockEnd_le_pow (lengths : Array Nat) (W : Nat) (hk : kraftOk lengths W)
    {l : Nat} (hl : l ≤ W) :
    startCodeF lengths W l + blCountF lengths W l ≤ 2 ^ l := by
  rcases Nat.lt_or_ge l W with hlt | hge
  · have hd : l + (W - l - 1 + 1) = W := by omega
    have h1 := blockEnd_le_startCodeF lengths W l (W - l - 1)
    rw [hd] at h1
    have h2 : startCodeF lengths W W ≤ 2 ^ W := by
      have := Nat.zero_le (blCountF lengths W W)
      unfold kraftOk at hk
      omega
    have h3 : (startCodeF lengths W l + blCountF lengths W l) * 2 ^ (W - l - 1 + 1) ≤ 2 ^ W :=
      Nat.le_trans h1 h2
    have hsplit : (2 : Nat) ^ W = 2 ^ l * 2 ^ (W - l - 1 + 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit] at h3
    exact Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos _)
  · have hleq : l = W := by omega
    subst hleq
    exact hk

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Every valid symbol's canonical code fits its width. -/
theorem canonicalCode_lt (lengths : Array Nat) (W : Nat) (hk : kraftOk lengths W)
    {s : Nat} (hv : validLen lengths W s) :
    canonicalCode lengths W s < 2 ^ lengths[s]! := by
  have h1 := rankF_lt_blCountF (W := W) hv
  have h2 := blockEnd_le_pow lengths W hk hv.2
  unfold canonicalCode
  omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Canonical codes of a common length are strictly ordered by symbol order. -/
theorem canonicalCode_lt_of_same_len {lengths : Array Nat} {W s s' : Nat}
    (heq : lengths[s]! = lengths[s']!) (hlt : s < s') :
    canonicalCode lengths W s < canonicalCode lengths W s' := by
  unfold canonicalCode rankF
  rw [heq]
  have hstep : (List.range (s + 1)).countP (fun x => lengths[x]! == lengths[s']!) =
      (List.range s).countP (fun x => lengths[x]! == lengths[s']!) + 1 := by
    rw [List.range_succ, List.countP_append]
    simp [List.countP_cons, heq]
  have hmono : (List.range (s + 1)).countP (fun x => lengths[x]! == lengths[s']!) ≤
      (List.range s').countP (fun x => lengths[x]! == lengths[s']!) :=
    List.Sublist.countP_le (List.range_sublist.mpr (by omega))
  omega

/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- **Pairwise prefix-incomparability of canonical codes** under the Kraft bound: no valid
    symbol's code path prefixes a different valid symbol's code path. Same-length codes
    differ as values; different-length codes live in disjoint blocks of the code space. -/
theorem canonical_not_prefix (lengths : Array Nat) (W : Nat) (hk : kraftOk lengths W)
    {s s' : Nat} (hv : validLen lengths W s) (hv' : validLen lengths W s') (hne : s' ≠ s) :
    ¬ (codeBits (canonicalCode lengths W s') lengths[s']! <+:
        codeBits (canonicalCode lengths W s) lengths[s]!) := by
  intro hpre
  have hll : lengths[s']! ≤ lengths[s]! := by
    have h := hpre.length_le
    rw [codeBits_length, codeBits_length] at h
    exact h
  have hclt : canonicalCode lengths W s < 2 ^ lengths[s]! := canonicalCode_lt lengths W hk hv
  have hclt' : canonicalCode lengths W s' < 2 ^ lengths[s']! := canonicalCode_lt lengths W hk hv'
  have hshift := codeBits_prefix_shift hll hclt hpre
  rw [Nat.mod_eq_of_lt hclt'] at hshift
  rcases Nat.eq_or_lt_of_le hll with heq | hlt
  · -- same length: the shift is trivial, but same-length codes are distinct
    have hd0 : lengths[s]! - lengths[s']! = 0 := by omega
    rw [hd0, Nat.shiftRight_zero] at hshift
    rcases Nat.lt_or_ge s' s with hss | hss
    · have := canonicalCode_lt_of_same_len (W := W) heq hss
      omega
    · have hss' : s < s' := by omega
      have := canonicalCode_lt_of_same_len (W := W) heq.symm hss'
      omega
  · -- s' is strictly shorter: its block ends before s's start
    have hblock := blockEnd_le_startCodeF lengths W lengths[s']!
      (lengths[s]! - lengths[s']! - 1)
    have he : lengths[s']! + (lengths[s]! - lengths[s']! - 1 + 1) = lengths[s]! := by omega
    rw [he] at hblock
    have hstart : startCodeF lengths W lengths[s]! ≤ canonicalCode lengths W s := by
      unfold canonicalCode
      omega
    have hpow_eq : (2 : Nat) ^ (lengths[s]! - lengths[s']! - 1 + 1)
        = 2 ^ (lengths[s]! - lengths[s']!) := by
      congr 1
      omega
    rw [hpow_eq] at hblock
    have hge : startCodeF lengths W lengths[s']! + blCountF lengths W lengths[s']! ≤
        canonicalCode lengths W s >>> (lengths[s]! - lengths[s']!) := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      omega
    have hlt2 : canonicalCode lengths W s' <
        startCodeF lengths W lengths[s']! + blCountF lengths W lengths[s']! := by
      have := rankF_lt_blCountF (W := W) hv'
      unfold canonicalCode
      omega
    omega

end Stdlib.Zlib

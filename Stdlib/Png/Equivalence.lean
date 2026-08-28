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
import Stdlib.Png.Spec
import Stdlib.Png.Filter
import Stdlib.Png.Streaming
import Stdlib.Zlib.ByteArrayBridge

/-
## Generic `ByteArray` push/get! plumbing (PA10)

`filterScanline`/`unfilterScanline`'s `Id.run`/`for`/`push` loops read back their own
`.get!`-indexed accumulator, so an induction along scanline position needs to know how
`.get!` interacts with `.push` on an otherwise-arbitrary `ByteArray`. The four bridge
lemmas PA10 built for exactly this (`ByteArray.get!_eq_getElem_bang`/`get!_push_lt`/
`get!_push_eq`/`ext_get!`) were, per this header's original note, never PNG-specific; they
now live in `Stdlib/Zlib/ByteArrayBridge.lean` (hoisted unchanged for PA16's LZ77 proofs,
which sit below PNG in the dependency order) and are imported here. -/

namespace Stdlib.Png

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Sub filter step modulo 256. -/
theorem sub_filter_step_invertible (x a : Nat) (hx : x < 256) (ha : a < 256) :
    ((x + 256 - a) % 256 + a) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Up filter step modulo 256. -/
theorem up_filter_step_invertible (x b : Nat) (hx : x < 256) (hb : b < 256) :
    ((x + 256 - b) % 256 + b) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Average filter step modulo 256. -/
theorem average_filter_step_invertible (x avg : Nat) (hx : x < 256) :
    ((x + 256 - (avg % 256)) % 256 + avg % 256) % 256 = x := by
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Exact algebraic invertibility of the Paeth predictor filter step modulo 256. -/
theorem paeth_filter_step_invertible (x pred : Nat) (hx : x < 256) :
    ((x + 256 - (pred % 256)) % 256 + pred % 256) % 256 = x := by
  omega

/-
## Scanline-level invertibility (PA10)

The four per-byte step lemmas above are genuinely universal but were, until this section,
unconnected to `filterScanline`/`unfilterScanline`: the five `_inst` theorems this section
supersedes checked invertibility on one fixed 8-byte literal via `native_decide` rather than
using the per-byte algebra already sitting a few lines above them.

`filterScanline`/`unfilterScanline` are `Id.run do ... for i in [0:len] do ... out :=
out.push _` loops, whose accumulator is not itself a term an inductive proof can name
directly. `Stdlib/Zlib/CRC32Equivalence.lean`'s `updateCrc32_eq_fold` establishes the
reduction technique this reuses: restate the loop as an explicit `List.range n |>.foldl`
(`filterFold`/`unfilterFold` below), prove it equal to the original `Id.run`/`for` form via
the same core simp set (`Id.run`, `List.range_eq_range'`, `Std.Legacy.Range.size`,
`Std.Legacy.Range.forIn_eq_forIn_range'`, `List.forIn_pure_yield_eq_foldl`), then induct on
the fold's step count `n` using a `_succ` lemma. This is the reusable shape the Zlib
oracle-debt entries (byte-at-a-time DEFLATE/INFLATE loops of the same `Id.run`/`for`/`push`
form) will need as well.
-/

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- The value `filterScanline`'s loop body computes for output byte `i`, restated as a
    plain function of `i` (matching the `let filteredVal := match ft with ...` block in
    `Stdlib/Png/Filter.lean` exactly) so an inductive proof can reason about it without
    unfolding the `Id.run`/`for` loop at every step. -/
def filterStepVal (ft : FilterType) (raw prior : ByteArray) (bpp i : Nat) : Nat :=
  let x := (raw.get! i).toNat
  let a := if i >= bpp then (raw.get! (i - bpp)).toNat else 0
  let b := if i < prior.size then (prior.get! i).toNat else 0
  let c := if i >= bpp && i - bpp < prior.size then (prior.get! (i - bpp)).toNat else 0
  match ft with
  | .none => x
  | .sub  => (x + 256 - a) % 256
  | .up   => (x + 256 - b) % 256
  | .average =>
    let avg := (a + b) / 2
    (x + 256 - avg) % 256
  | .paeth =>
    let pred := (paethPredictor (a : Int) (b : Int) (c : Int)).natAbs
    (x + 256 - (pred % 256)) % 256

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Explicit `List.foldl` normal form of `filterScanline`'s accumulator after processing
    the first `n` bytes -- the connection point an induction on scanline position needs
    (mirrors `crc32InternalFold` in `Stdlib/Zlib/CRC32Equivalence.lean`). -/
def filterFold (ft : FilterType) (raw prior : ByteArray) (bpp n : Nat) : ByteArray :=
  (List.range n).foldl (fun out i => out.push (filterStepVal ft raw prior bpp i).toUInt8)
    ByteArray.empty

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
theorem filterFold_succ (ft : FilterType) (raw prior : ByteArray) (bpp k : Nat) :
    filterFold ft raw prior bpp (k + 1) =
      (filterFold ft raw prior bpp k).push (filterStepVal ft raw prior bpp k).toUInt8 := by
  unfold filterFold
  rw [List.range_succ, List.foldl_append]
  rfl

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
theorem filterFold_size (ft : FilterType) (raw prior : ByteArray) (bpp n : Nat) :
    (filterFold ft raw prior bpp n).size = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [filterFold_succ]; simp [ih]

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- **The fold-normalization connection theorem.** `filterScanline`'s `Id.run`/`for` form
    equals the explicit `filterFold` fold over its whole domain (`raw.size` iterations,
    matching `filterScanline`'s own `len := raw.size`). -/
theorem filterScanline_eq_fold (ft : FilterType) (raw prior : ByteArray) (bpp : Nat) :
    filterScanline ft raw prior bpp = filterFold ft raw prior bpp raw.size := by
  unfold filterScanline filterFold filterStepVal
  simp only [Id.run, List.range_eq_range', Std.Legacy.Range.size,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Nat.sub_zero, Nat.div_one, Nat.add_sub_cancel, pure_bind]
  rfl

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- The value `unfilterScanline`'s loop body computes for output byte `i`, given the
    already-reconstructed prefix `out`. Unlike `filterStepVal`, this genuinely depends on
    `out` at `i - bpp` (Sub/Average/Paeth's "already-unfiltered left neighbour"), which is
    exactly why scanline invertibility needs induction rather than a pointwise restatement:
    `out` must have been proven equal to `raw` up to `i - bpp` before this step's algebra
    applies. -/
def unfilterStepVal (ft : FilterType) (out prior : ByteArray) (bpp i : Nat) (filtX : Nat) : Nat :=
  let a := if i >= bpp then (out.get! (i - bpp)).toNat else 0
  let b := if i < prior.size then (prior.get! i).toNat else 0
  let c := if i >= bpp && i - bpp < prior.size then (prior.get! (i - bpp)).toNat else 0
  match ft with
  | .none => filtX
  | .sub  => (filtX + a) % 256
  | .up   => (filtX + b) % 256
  | .average =>
    let avg := (a + b) / 2
    (filtX + avg) % 256
  | .paeth =>
    let pred := (paethPredictor (a : Int) (b : Int) (c : Int)).natAbs
    (filtX + (pred % 256)) % 256

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
def unfilterFold (ft : FilterType) (filtered prior : ByteArray) (bpp n : Nat) : ByteArray :=
  (List.range n).foldl
    (fun out i => out.push (unfilterStepVal ft out prior bpp i (filtered.get! i).toNat).toUInt8)
    ByteArray.empty

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
theorem unfilterFold_succ (ft : FilterType) (filtered prior : ByteArray) (bpp k : Nat) :
    unfilterFold ft filtered prior bpp (k + 1) =
      (unfilterFold ft filtered prior bpp k).push
        (unfilterStepVal ft (unfilterFold ft filtered prior bpp k) prior bpp k
          (filtered.get! k).toNat).toUInt8 := by
  unfold unfilterFold
  rw [List.range_succ, List.foldl_append]
  rfl

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
theorem unfilterFold_size (ft : FilterType) (filtered prior : ByteArray) (bpp n : Nat) :
    (unfilterFold ft filtered prior bpp n).size = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [unfilterFold_succ]; simp [ih]

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
theorem unfilterScanline_eq_fold (ft : FilterType) (filtered prior : ByteArray) (bpp : Nat) :
    unfilterScanline ft filtered prior bpp = unfilterFold ft filtered prior bpp filtered.size := by
  unfold unfilterScanline unfilterFold unfilterStepVal
  simp only [Id.run, List.range_eq_range', Std.Legacy.Range.size,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Nat.sub_zero, Nat.div_one, Nat.add_sub_cancel, pure_bind]
  rfl

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- Every `UInt8`'s `.toNat` is below 256 -- restated as a plain `< 256` fact (rather than
    `< UInt8.size`) since that is the literal bound `sub_filter_step_invertible` et al.
    require. -/
theorem uint8_toNat_lt_256 (u : UInt8) : u.toNat < 256 := by
  have h := u.toNat_lt_size
  simp only [UInt8.size] at h
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- `filterStepVal`'s result is always a genuine byte value, regardless of filter type --
    needed to show `.toUInt8` round-trips back to it exactly (`Nat.toUInt8` wraps mod 256,
    a no-op exactly when the input is already `< 256`). -/
theorem filterStepVal_lt_256 (ft : FilterType) (raw prior : ByteArray) (bpp i : Nat) :
    filterStepVal ft raw prior bpp i < 256 := by
  unfold filterStepVal
  cases ft <;> simp only <;>
    first
      | exact uint8_toNat_lt_256 _
      | omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
theorem toNat_toUInt8_of_lt {n : Nat} (h : n < 256) : (n.toUInt8).toNat = n := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- `filterFold`'s `n`-th byte (for any `n` past `k`) is exactly `filterStepVal` at `k` --
    the pointwise reading `unfilterFold`'s induction step needs to know what filtered byte
    `k` it is unfiltering. Unlike `unfilterStepVal`, `filterStepVal` never reads the
    accumulator, so this holds unconditionally (no `bpp ≥ 1` hypothesis, no dependency on
    a prefix invariant). -/
theorem filterFold_get (ft : FilterType) (raw prior : ByteArray) (bpp : Nat) :
    ∀ n k, k < n →
      (filterFold ft raw prior bpp n).get! k = (filterStepVal ft raw prior bpp k).toUInt8 := by
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
    intro k hk
    rw [filterFold_succ]
    rcases Nat.lt_or_ge k m with hlt | hge
    · exact (ByteArray.get!_push_lt _ _ k (by rw [filterFold_size]; exact hlt)).trans (ih k hlt)
    · have hkm : k = m := by omega
      subst hkm
      exact ByteArray.get!_push_eq _ _ k (filterFold_size ft raw prior bpp k).symm

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- **The per-position roundtrip step.** Given that the already-reconstructed byte at
    `i - bpp` (the one Sub/Average/Paeth read as their "left neighbour," if `i` is at least
    one pixel stride in) agrees with the true raw byte there, unfiltering the byte
    `filterStepVal` produced at position `i` reproduces the true raw byte at `i` exactly.
    This isolates the induction step's algebraic content from the fold machinery: `b`/`c`
    (both read only from `prior`, never from the growing output) are syntactically
    identical on the filter and unfilter sides by construction, so `a`'s agreement
    (supplied by the hypothesis, which is exactly the induction's IH) is the only thing
    that needs establishing before `sub_filter_step_invertible`/`up_filter_step_invertible`/
    `average_filter_step_invertible`/`paeth_filter_step_invertible` close each case --
    confirming the task's framing: Paeth's own case split on its predictor never needs
    re-deriving here, since both sides apply `paethPredictor` to the identical `(a, b, c)`
    triple. -/
theorem unfilterStepVal_filterStepVal (ft : FilterType) (raw prior out : ByteArray) (bpp i : Nat)
    (hprefix : i ≥ bpp → out.get! (i - bpp) = raw.get! (i - bpp)) :
    unfilterStepVal ft out prior bpp i (filterStepVal ft raw prior bpp i) =
      (raw.get! i).toNat := by
  have hx : (raw.get! i).toNat < 256 := uint8_toNat_lt_256 _
  have ha : (if i ≥ bpp then (out.get! (i - bpp)).toNat else 0) =
      (if i ≥ bpp then (raw.get! (i - bpp)).toNat else 0) := by
    by_cases h : i ≥ bpp
    · simp only [if_pos h, hprefix h]
    · simp only [if_neg h]
  have hb : (if i < bpp then (0:Nat) else 0) = 0 := by simp
  unfold unfilterStepVal filterStepVal
  cases ft with
  | none => rfl
  | sub =>
    simp only [ha]
    have hbound : (if i ≥ bpp then (raw.get! (i - bpp)).toNat else 0) < 256 := by
      split <;> first | exact uint8_toNat_lt_256 _ | omega
    exact sub_filter_step_invertible _ _ hx hbound
  | up =>
    have hbbound : (if i < prior.size then (prior.get! i).toNat else 0) < 256 := by
      split <;> first | exact uint8_toNat_lt_256 _ | omega
    exact up_filter_step_invertible _ _ hx hbbound
  | average =>
    simp only [ha]
    have ha'lt : (if i ≥ bpp then (raw.get! (i - bpp)).toNat else 0) < 256 := by
      split <;> first | exact uint8_toNat_lt_256 _ | omega
    have hb'lt : (if i < prior.size then (prior.get! i).toNat else 0) < 256 := by
      split <;> first | exact uint8_toNat_lt_256 _ | omega
    generalize ha' : (if i ≥ bpp then (raw.get! (i - bpp)).toNat else 0) = a' at ha'lt ⊢
    generalize hb' : (if i < prior.size then (prior.get! i).toNat else 0) = b' at hb'lt ⊢
    have havg_lt : (a' + b') / 2 < 256 := by omega
    have havg_eq : (a' + b') / 2 = (a' + b') / 2 % 256 := (Nat.mod_eq_of_lt havg_lt).symm
    rw [havg_eq]
    exact average_filter_step_invertible _ _ hx
  | paeth =>
    simp only [ha]
    exact paeth_filter_step_invertible _ _ hx

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- **The induction workhorse.** For every prefix length `n` of the scanline, unfiltering
    the first `n` filtered bytes (built from `raw`/`prior` via `filterFold`) reproduces the
    first `n` raw bytes exactly, byte for byte -- given that consecutive pixels are at
    least `bpp ≥ 1` bytes apart. That hypothesis is the well-formedness precondition PNG's
    own format guarantees (`bpp` is a channel-count-derived byte stride, never zero), and
    the induction genuinely needs it: at `bpp = 0`, Sub/Average/Paeth's step at byte `i`
    would read `out.get! i` -- itself, before that very push -- collapsing the
    "already-reconstructed prefix" invariant below into circularity. Proved by induction on
    `n`, using `unfilterStepVal_filterStepVal` (hence transitively
    `sub_filter_step_invertible`/`up_filter_step_invertible`/
    `average_filter_step_invertible`/`paeth_filter_step_invertible`) as the per-position
    step. -/
theorem unfilterFold_filterFold_get (ft : FilterType) (raw prior : ByteArray) (bpp : Nat)
    (hbpp : 1 ≤ bpp) :
    ∀ n, n ≤ raw.size → ∀ i, i < n →
      (unfilterFold ft (filterFold ft raw prior bpp raw.size) prior bpp n).get! i
        = raw.get! i := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro hn i hi
    have hk : k ≤ raw.size := by omega
    have hksize : k < raw.size := by omega
    have hout_size :
        (unfilterFold ft (filterFold ft raw prior bpp raw.size) prior bpp k).size = k :=
      unfilterFold_size ft (filterFold ft raw prior bpp raw.size) prior bpp k
    rw [unfilterFold_succ]
    rcases Nat.lt_or_ge i k with hlt | hge
    · rw [ByteArray.get!_push_lt _ _ i (by rw [hout_size]; exact hlt)]
      exact ih hk i hlt
    · have hik : i = k := by omega
      rw [hik, ByteArray.get!_push_eq _ _ k hout_size.symm]
      have hprefix : k ≥ bpp →
          (unfilterFold ft (filterFold ft raw prior bpp raw.size) prior bpp k).get! (k - bpp)
            = raw.get! (k - bpp) := fun _ => ih hk (k - bpp) (by omega)
      have hfilt : ((filterFold ft raw prior bpp raw.size).get! k).toNat =
          filterStepVal ft raw prior bpp k := by
        rw [filterFold_get ft raw prior bpp raw.size k hksize]
        exact toNat_toUInt8_of_lt (filterStepVal_lt_256 ft raw prior bpp k)
      rw [hfilt, unfilterStepVal_filterStepVal ft raw prior _ bpp k hprefix]
      exact UInt8.toNat_inj.mp (toNat_toUInt8_of_lt (uint8_toNat_lt_256 _))

/- REF: docs/STDLIB_PNG.md#61-filter-roundtrip-invariance -/
/-- **Scanline-level invertibility.** Unfiltering a filtered scanline reproduces the
    original scanline exactly, for every filter type, every scanline, and every
    prior-scanline context -- the general fact `filter_none_invertible_inst`/
    `filter_sub_invertible_inst`/`filter_up_invertible_inst`/
    `filter_average_invertible_inst`/`filter_paeth_invertible_inst` each checked on one
    fixed 8-byte literal via `native_decide`. Requires `bpp ≥ 1` (PNG's own well-formedness
    precondition: `bpp` is a channel/depth-derived byte stride, never zero -- see
    `unfilterFold_filterFold_get`'s note on why the induction needs it), stated explicitly
    rather than silently assumed. -/
theorem filter_unfilter_soundness (ft : FilterType) (raw prior : ByteArray) (bpp : Nat)
    (hbpp : 1 ≤ bpp) :
    unfilterScanline ft (filterScanline ft raw prior bpp) prior bpp = raw := by
  rw [filterScanline_eq_fold, unfilterScanline_eq_fold, filterFold_size]
  apply ByteArray.ext_get!
  · rw [unfilterFold_size]
  · intro i hi
    rw [unfilterFold_size] at hi
    exact unfilterFold_filterFold_get ft raw prior bpp hbpp raw.size (Nat.le_refl _) i hi

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Sample 2x2 test image for canonical simulation proofs. -/
def sample2x2Image : ImageRGBA8 := {
  width  := 2
  height := 2
  pixels := ByteArray.mk #[
    255, 0, 0, 255,     0, 255, 0, 255,
    0, 0, 255, 255,     255, 255, 255, 255
  ]
}

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Verified Simulation Instance: Lossless PNG encode-decode roundtrip soundness. -/
theorem png_roundtrip_soundness_inst :
    (match decodeImageRGBA8 (encodeImageRGBA8 sample2x2Image) with
     | Except.ok res => res == sample2x2Image
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem -/
/-- Verified Simulation Instance: Canonical 1.5-roundtrip soundness for PNG byte streams.
    Outer `Except.error _ => false` (2026-08-27, PA16 Phase 1 vacuity fix): the prior `=> true`
    let a `decodeImageRGBA8` that always failed still discharge this theorem, since `testStream` is
    a fixed, already-known-good literal and the check never required the initial decode to actually
    succeed -- see `Stdlib.Zlib.deflate_idempotent_canonical_roundtrip_inst`'s doc comment for the
    full rationale (docs/PA16_CODEC_SOUNDNESS.md). -/
theorem png_idempotent_canonical_roundtrip_inst :
    let testStream := encodeImageRGBA8 sample2x2Image
    (match decodeImageRGBA8 testStream with
     | Except.error _ => false
     | Except.ok img =>
       match decodeImageRGBA8 (encodeImageRGBA8 img) with
       | Except.ok res => res == img
       | Except.error _ => false) = true := by
  native_decide

end Stdlib.Png

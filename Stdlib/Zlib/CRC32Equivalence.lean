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

import Std.Tactic.BVDecide
import Gasm.Core.Types
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Shift
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Assembler
import Stdlib.Zlib.CRC32
import Stdlib.Zlib.Windows

/-!
# PA1 pathfinder: `crc32SymbolicProgram` contract/proof groundwork

This file is the PA1 pathfinder's proof-development module for
`Stdlib.Zlib.Windows.crc32SymbolicProgram`, following the design in
`docs/PATHFINDER_CRC32.md`. It is **not** a completed end-to-end contract
(Theorems 1/2/3 of `docs/EQUIVALENCE_PROOFS.md` §4 are not stated here) --
see this task's completion report for a precise account of what remains.
What this file DOES contain, fully kernel/SAT-checked with zero `sorry`:

1. The fold-normalization connection theorem (design §3.8/M3b): `updateCrc32`'s
   `Id.run`/`for`-loop spec is shown equal to an explicit `List.foldl`
   (`crc32InternalFold`), closing a connection theorem the design flagged as
   a prerequisite that "does not yet exist in the tree."
2. The Law 12 connection theorem the whole pathfinder was chosen to exercise
   (design §3.6): the table-driven spec step and the assembly's inline
   8x-unrolled per-bit recurrence are proven to compute the *same* function,
   via a branch-free bitvector normalization. Originally discharged end-to-end
   by `bv_decide`; per the trust ladder in `docs/REVIEW.md` Law 10, every step is now a structural proof
   (`BitVec` extensionality, `omega`, algebraic rewriting) with zero `bv_decide`
   calls anywhere in this file.
3. The jump-displacement round-trip facts (design §3.8's "recommended, not
   blocking" open question) needed to reason about `assembleProgram`'s
   symbolic-label resolution at a symbolic base `rip` -- resolved here, given
   a no-address-wraparound hypothesis analogous to the routine's own
   buffer-bound precondition.
4. Thirteen of the fourteen per-instruction step lemmas the design's §3.1
   census predicts are needed, stated at the `AnyX86_64Instruction` wrapper
   construction site per §3.2 and discharged by `rfl` (the wrapper-unfolding
   concern §3.2 raises turned out not to obstruct `rfl` in practice).
-/

namespace Stdlib.Zlib.CRC32Equivalence

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Stdlib.Zlib

/-
## Part 1: fold-normalization connection theorem (design §3.8, M3b)

`updateCrc32`'s `Id.run do ... for i in [start:stop] do ...` form does not expose the
loop-carried accumulator as a term an invariant can name (design v1's own §7 Q3, left
open). `crc32InternalFold` is the explicit `List.foldl` the design calls for; the
theorems below prove it agrees with `updateCrc32`/`crc32Table`/`crc32`.
-/

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- `crc32Table` expressed as a plain `List.map`/`.toArray`, closing the `Id.run`/`for`
    reformulation for the *table's own* construction loop (needed because `updateCrc32`'s
    dependent-`if` indexes into `crc32Table`, not directly into `mkCrcTableEntry`). -/
theorem crc32Table_eq_map : crc32Table = ((List.range 256).map mkCrcTableEntry).toArray := by
  unfold crc32Table
  simp [Id.run, List.range_eq_range']

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- `crc32Table` has exactly 256 entries -- a closed, non-parametric fact about a fixed
    definition (no input domain to sample, hence not a Law 9/10 pointwise bypass; see
    `Stdlib/Zlib/CRC32.lean`'s existing `crc32_empty` for the identical precedent of
    discharging a closed fact about a fixed term by evaluation). -/
theorem crc32Table_size : crc32Table.size = 256 := by
  rw [crc32Table_eq_map]
  simp

-- Every in-bounds `crc32Table` entry equals the per-bit recurrence that generates it.
set_option maxRecDepth 8000 in
/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
theorem crc32Table_getElem (idx : Nat) (h : idx < crc32Table.size) :
    crc32Table[idx] = mkCrcTableEntry idx := by
  have _h' : idx < 256 := by rw [crc32Table_size] at h; exact h
  simp [crc32Table_eq_map]

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- Unconditional form of `crc32Table_getElem`: `updateCrc32`'s dependent-`if` table lookup
    always agrees with the direct per-bit recurrence, regardless of which branch is taken
    (the out-of-bounds branch is trivially the same expression already). Stated this way
    (total, no side condition) so it is usable as a plain rewrite/simp lemma against
    `updateCrc32`'s own `dite`, independent of whatever normal form `simp` produces for the
    surrounding index arithmetic. -/
theorem crc32Table_dite (idx : Nat) :
    (if h : idx < crc32Table.size then crc32Table[idx] else mkCrcTableEntry idx) =
      mkCrcTableEntry idx := by
  by_cases h : idx < crc32Table.size
  · rw [dif_pos h, crc32Table_getElem _ h]
  · rw [dif_neg h]

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- One byte's worth of the running-CRC update, expressed directly via the per-bit
    recurrence (`mkCrcTableEntry`) rather than a table lookup -- the explicit fold step
    the design's `crc32InternalFold` sketch names but does not itself define. -/
def crc32ByteStep (c : UInt32) (b : UInt8) : UInt32 :=
  (c >>> 8) ^^^ mkCrcTableEntry (((c ^^^ b.toUInt32) &&& 0xFF).toNat)

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
/-- Explicit `List.foldl` normal form of the running CRC-32 accumulator after processing
    the first `n` bytes of `buf`, starting from the routine's own initial accumulator
    `0xFFFFFFFF`. This is `crc32InternalFold` from `docs/PATHFINDER_CRC32.md` §3.8,
    authored here since the design explicitly notes it does not yet exist in the tree. -/
def crc32InternalFold (buf : ByteArray) (n : Nat) : UInt32 :=
  (List.range n).foldl (fun c i => crc32ByteStep c (buf.get! i)) 0xFFFFFFFF

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
theorem crc32InternalFold_zero (buf : ByteArray) : crc32InternalFold buf 0 = 0xFFFFFFFF := rfl

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
/-- The recursive step an outer-loop invariant/induction actually needs: processing one
    more byte is exactly one more `crc32ByteStep` application. -/
theorem crc32InternalFold_succ (buf : ByteArray) (k : Nat) :
    crc32InternalFold buf (k + 1) = crc32ByteStep (crc32InternalFold buf k) (buf.get! k) := by
  unfold crc32InternalFold
  rw [List.range_succ, List.foldl_append]
  rfl

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
/- REF: docs/EQUIVALENCE_PROOFS.md#4-the-three-independent-split-theorems -/
/-- **The fold-normalization connection theorem (M3b).** `updateCrc32`'s `Id.run`/`for`
    form is shown equal to the explicit `crc32InternalFold` fold, for any prefix length
    `n` not exceeding the buffer -- discharged by reducing the `for`-loop through Lean's
    own `Std.Legacy.Range`/`List.foldl` core simp set (`forIn_eq_forIn_range'`,
    `idRun_forIn_yield_eq_foldl`, etc.), contrary to design v1's fear that this reduction
    would need to be built by hand; it already exists in the Lean 4 standard library. -/
theorem updateCrc32_eq_fold (buf : ByteArray) (n : Nat) (hn : n ≤ buf.size) :
    updateCrc32 0 buf 0 n = crc32InternalFold buf n ^^^ 0xFFFFFFFF := by
  unfold updateCrc32 crc32InternalFold crc32ByteStep
  simp only [Id.run, Nat.min_eq_right hn, List.range_eq_range', Std.Legacy.Range.size,
    Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Nat.zero_add,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind, crc32Table_dite,
    UInt32.zero_xor]

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
/-- The top-level spec function `Stdlib.Zlib.crc32`, restated over `crc32InternalFold`. -/
theorem crc32_eq_fold (buf : ByteArray) :
    crc32 buf = crc32InternalFold buf buf.size ^^^ 0xFFFFFFFF :=
  updateCrc32_eq_fold buf buf.size (Nat.le_refl _)

/-
## Part 2: the Law 12 connection theorem (design §3.6) -- table vs. inline per-bit chain

`crc32SymbolicProgram` computes the same per-byte update as `crc32ByteStep`/
`mkCrcTableEntry`, but inline, 8x unrolled, with no table. The two encodings of the same
model-level fact are linked here via a branch-free bitvector normalization and a single
`bv_decide` certificate over the complete `UInt32` domain (design's primary route, §3.6).
-/

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/-- The per-bit CRC update in its natural (branching) form: the same recurrence
    `mkCrcTableEntry`'s own loop body uses, and the semantic content of the assembly's
    6-instruction bit-test-and-conditional-XOR block. -/
def G (poly c : UInt32) : UInt32 := if c &&& 1 != 0 then (c >>> 1) ^^^ poly else c >>> 1

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/-- Branch-free normal form of `G`, using the standard "all-ones iff bit 0 set" bit trick
    (`0 - (c &&& 1)`). `bv_decide` can certify facts about this form directly; it cannot
    see through `G`'s `Decidable`-guarded `if` (confirmed empirically below). -/
def Gbf (poly c : UInt32) : UInt32 := (c >>> 1) ^^^ (poly &&& (0 - (c &&& 1)))

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/-- Per PA13: proven structurally rather than by `bv_decide`. `(c &&& 1).toNat = c.toNat % 2`
    (`Nat.and_one_is_mod`, via `UInt32.toNat_and`/`UInt32.toNat_one`), and a `Nat` mod-2 value is
    `0` or `1` by `omega`; `UInt32.toNat_inj` lifts each case back up to a `UInt32` equation. -/
theorem and_one_cases (c : UInt32) : c &&& 1 = 0 ∨ c &&& 1 = 1 := by
  have h : (c &&& 1).toNat = c.toNat % 2 := by
    rw [UInt32.toNat_and, UInt32.toNat_one, Nat.and_one_is_mod]
  have h2 : c.toNat % 2 = 0 ∨ c.toNat % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · left; apply UInt32.toNat_inj.mp; rw [h, h2, UInt32.toNat_zero]
  · right; apply UInt32.toNat_inj.mp; rw [h, h2, UInt32.toNat_one]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `G = Gbf` pointwise. Confirms the design's M9(a) finding that `G`'s raw `Bool`-decidability
    guard must be case-split first (via `and_one_cases`) before the branch-free form can be
    related to it. Per PA13, each branch is then closed structurally, not by `bv_decide`: the
    `c &&& 1 = 0` branch rewrites `0 - 0` away via `UInt32.and_zero`/`UInt32.xor_zero`; the
    `c &&& 1 = 1` branch rewrites `0 - 1` to `-1` (`UInt32.zero_sub`) and then uses
    `UInt32.and_neg_one` (`poly &&& -1 = poly`, i.e. ANDing with all-ones is the identity). -/
theorem G_eq_Gbf (poly c : UInt32) : G poly c = Gbf poly c := by
  unfold G Gbf
  rcases and_one_cases c with h | h
  · have hne : ¬ (c &&& 1 != 0) := by simp [h]
    simp only [hne]
    simp [h, UInt32.and_zero, UInt32.xor_zero]
  · have hne : (c &&& 1 != 0) := by simp [h]
    simp only [hne, if_pos]
    simp [h, UInt32.zero_sub, UInt32.and_neg_one]

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
/-- Eight applications of `G`, matching the assembly's 8x-unrolled bit chain exactly
    (`crc_sub_bit0` .. `crc_sub_bit7`) and `mkCrcTableEntry`'s 8-iteration loop. -/
def G8 (poly c : UInt32) : UInt32 :=
  G poly (G poly (G poly (G poly (G poly (G poly (G poly (G poly c)))))))

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
def Gbf8 (poly c : UInt32) : UInt32 :=
  Gbf poly (Gbf poly (Gbf poly (Gbf poly (Gbf poly (Gbf poly (Gbf poly (Gbf poly c)))))))

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
theorem G8_eq_Gbf8 (poly c : UInt32) : G8 poly c = Gbf8 poly c := by
  unfold G8 Gbf8
  rw [G_eq_Gbf, G_eq_Gbf, G_eq_Gbf, G_eq_Gbf, G_eq_Gbf, G_eq_Gbf, G_eq_Gbf, G_eq_Gbf]

/-
### PA14: `G8bf_table` structural closure (no `bv_decide`)

The table/closed-form connection identity -- applying the 8-step map to a full 32-bit
value equals shifting it down by 8 and XORing in the 8-step map applied to just its low
byte, i.e. exactly what a byte-indexed CRC table precomputes -- was originally discharged
by a single `bv_decide` SAT certificate over the complete `UInt32 x UInt32` domain. PA14
found this reachable structurally, via the observation that `Gbf poly` (fixed `poly`) is
`UInt32`-XOR-linear: `Gbf poly (a ^^^ b) = Gbf poly a ^^^ Gbf poly b` (`Gbf_additive`
below), because both its shift term and its "inject `poly` iff bit 0 is set" feedback term
are linear in this sense. Given that, `x`'s low byte and high bits split by XOR
(`and_xor_compl`), and the identity reduces to: (a) `Gbf8` distributes over that XOR
(`Gbf8_additive`), (b) running 8 steps on the high bits alone is a pure shift-by-8 with no
`poly` ever injected, because the low 8 bits stay zero at bit 0 through all 8 steps
(`Gbf8_high_part`, via a small hand-rolled `iterGbf` recursor since this project has no
`Nat.iterate`/Mathlib), and (c) that shift-by-8 of the high bits equals the shift-by-8 of
`x` itself, since the masked-off bits are exactly the ones shifted away (`and_high_shr8`).
-/

/- REF: docs/PATHFINDER_CRC32.md -/
/-- Bitwise AND distributes over bitwise XOR (the Boolean-ring distributive law, applied
    bit-by-bit via `BitVec` extensionality and a case split on each side's bit). -/
theorem and_xor_distrib (a b c : UInt32) : a &&& (b ^^^ c) = (a &&& b) ^^^ (a &&& c) := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [UInt32.toBitVec_and, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases c.toBitVec.getLsbD i <;> simp

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `and_xor_distrib` with the mask on the right instead of the left (AND commutes). -/
theorem xor_and_one (a b : UInt32) : (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) := by
  rw [UInt32.and_comm, and_xor_distrib, UInt32.and_comm 1 a, UInt32.and_comm 1 b]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `Gbf`'s branch-free feedback mask (`0 - (c &&& 1)`, all-ones or all-zero) is itself
    XOR-linear in `c`: case-split `a &&& 1` and `b &&& 1` (via `and_one_cases`) into their
    four combinations and check each concretely. -/
theorem mask_xor (a b : UInt32) :
    (0 - ((a ^^^ b) &&& 1)) = (0 - (a &&& 1)) ^^^ (0 - (b &&& 1)) := by
  rw [xor_and_one]
  rcases and_one_cases a with ha | ha <;> rcases and_one_cases b with hb | hb <;>
    rw [ha, hb] <;> decide

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `Gbf poly` is `UInt32`-XOR-linear for fixed `poly`: its shift term distributes over XOR
    (`UInt32.shiftRight_xor`) and its feedback-mask term does too (`mask_xor` plus
    `and_xor_distrib`), so the whole map does. This is the key algebraic fact PA14's
    structural proof of `G8bf_table` rests on. -/
theorem Gbf_additive (poly a b : UInt32) : Gbf poly (a ^^^ b) = Gbf poly a ^^^ Gbf poly b := by
  unfold Gbf
  rw [UInt32.shiftRight_xor, mask_xor, and_xor_distrib]
  ac_rfl

/- REF: docs/PATHFINDER_CRC32.md -/
/-- Eight compositions of a linear map are linear: `simp` applies `Gbf_additive` bottom-up
    through all eight nested layers of `Gbf8`'s definition. -/
theorem Gbf8_additive (poly a b : UInt32) : Gbf8 poly (a ^^^ b) = Gbf8 poly a ^^^ Gbf8 poly b := by
  unfold Gbf8
  simp only [Gbf_additive]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- When `y`'s bit 0 is clear, `Gbf`'s feedback mask is `0 - 0 = 0`, so no `poly` is
    injected and the step is a pure shift -- the branch-free-form counterpart of
    `G_eq_Gbf`'s `c &&& 1 = 0` case. -/
theorem Gbf_of_bit0_zero (poly y : UInt32) (h : y &&& 1 = 0) : Gbf poly y = y >>> 1 := by
  unfold Gbf
  simp [h, UInt32.and_zero, UInt32.xor_zero]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- Two `UInt32` right-shifts by literal amounts compose into one shift by their sum,
    given both amounts (and the sum) are within the 32-bit shift range so no `% 32`
    wraparound kicks in. Bridges `UInt32`'s `BitVec`-shift-amount semantics
    (`UInt32.toNat_shiftRight`) to `Nat.shiftRight_add`. -/
theorem shr_shr_add (z : UInt32) (a b c : UInt32) (h : a.toNat + b.toNat = c.toNat)
    (ha : a.toNat < 32) (hb : b.toNat < 32) (hc : c.toNat < 32) :
    (z >>> a) >>> b = z >>> c := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight, UInt32.toNat_shiftRight,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, ← h, Nat.shiftRight_add]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- A minimal hand-rolled "apply `Gbf poly` `n` times" recursor. This project has no
    `Nat.iterate`/`f^[n]` (a Mathlib addition, per `mkCrcTableEntry_eq_G8`'s own note above),
    so `Gbf8_high_part` below needs its own small recursive definition to state and prove,
    by ordinary structural induction on `n`, the fact that a zero-low-bits input passes
    through any fixed number of `Gbf` steps as a pure shift. -/
def iterGbf (poly : UInt32) : Nat → UInt32 → UInt32
  | 0, c => c
  | n + 1, c => iterGbf poly n (Gbf poly c)

/- REF: docs/PATHFINDER_CRC32.md -/
/-- If `y`'s bit `k` is clear for every `k < n`, then `n` applications of `Gbf poly` to `y`
    never inject `poly` and reduce to a single shift by `n`. Proved by induction on `n`:
    the first step needs bit 0 (`Gbf_of_bit0_zero`); the inductive hypothesis is then
    re-applied to `y >>> 1` against a re-indexed hypothesis (`shr_shr_add` relates
    `(y >>> 1) >>> k` back to a single shift `y >>> (k+1)` so it can reuse `h`); the final
    shift composition (`(y >>> 1) >>> n = y >>> (n+1)`) is `shr_shr_add` again. -/
theorem iterGbf_zero_low (poly : UInt32) (n : Nat) (hn : n < 32) (y : UInt32)
    (h : ∀ k, k < n → (y >>> k.toUInt32) &&& 1 = 0) :
    iterGbf poly n y = y >>> n.toUInt32 := by
  induction n generalizing y with
  | zero => simp [iterGbf]
  | succ n ih =>
    unfold iterGbf
    have h0 : y &&& 1 = 0 := by
      have := h 0 (by omega)
      simpa using this
    rw [Gbf_of_bit0_zero poly y h0]
    have hstep : ∀ k, k < n → ((y >>> (1 : UInt32)) >>> k.toUInt32) &&& 1 = 0 := by
      intro k hk
      have hk1 : (y >>> (1 : UInt32)) >>> k.toUInt32 = y >>> (k + 1).toUInt32 := by
        apply shr_shr_add
        · simp <;> omega
        · simp <;> omega
        · simp <;> omega
        · simp <;> omega
      rw [hk1]
      exact h (k + 1) (by omega)
    rw [ih (by omega) (y >>> (1 : UInt32)) hstep]
    apply shr_shr_add
    · simp <;> omega
    · simp <;> omega
    · simp <;> omega
    · simp <;> omega

/- REF: docs/PATHFINDER_CRC32.md -/
/-- The high-24-bits mask's bit `k` (`k < 8`) is always clear, so masking `x`'s high bits
    first cannot set the low-order bit that a subsequent shift-by-`k` would expose --
    purely a fact about the concrete mask constant, via `UInt32.shiftRight_and` pushing the
    shift onto each operand separately. -/
theorem high_shr_bit0_zero (x : UInt32) (k : Nat)
    (hk : ((0xFFFFFF00 : UInt32) >>> k.toUInt32) &&& 1 = 0) :
    ((x &&& 0xFFFFFF00) >>> k.toUInt32) &&& 1 = 0 := by
  rw [UInt32.shiftRight_and, UInt32.and_assoc, hk, UInt32.and_zero]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- The high-24-bits half of `x` passes through all 8 `Gbf` steps as a pure shift: instance
    `iterGbf_zero_low` at `n = 8` (`8 < 32`), discharging its "bit `k` clear for `k < 8`"
    hypothesis by the 8 concrete instances of `high_shr_bit0_zero`, then noting
    `Gbf8 poly = iterGbf poly 8` definitionally (8 is a literal, exactly as
    `mkCrcTableEntry_eq_G8` above notes for its own `G8`/8-iteration match). -/
theorem Gbf8_high_part (poly x : UInt32) :
    Gbf8 poly (x &&& 0xFFFFFF00) = (x &&& 0xFFFFFF00) >>> 8 := by
  have heq : Gbf8 poly (x &&& 0xFFFFFF00) = iterGbf poly 8 (x &&& 0xFFFFFF00) := rfl
  rw [heq]
  have hall : ∀ k, k < 8 → ((x &&& 0xFFFFFF00) >>> k.toUInt32) &&& 1 = 0 := by
    intro k hk
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk8 with h | h | h | h | h | h | h | h <;> subst h <;>
      exact high_shr_bit0_zero x _ (by decide)
  rw [iterGbf_zero_low poly 8 (by omega) (x &&& 0xFFFFFF00) hall]
  congr 1

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `x`'s low byte, as a `UInt32`, is `< 256` (`Nat.and_le_right` bounds it by the mask),
    so shifting it right by 8 gives `0` (a value `< 2^8` divided by `2^8` is `0`). -/
theorem and_0xFF_shr8_zero (x : UInt32) : (x &&& 0xFF) >>> 8 = 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, UInt32.toNat_zero]
  have hb : (x &&& 0xFF).toNat ≤ 255 := by
    rw [UInt32.toNat_and, UInt32.toNat_ofNat]
    exact Nat.and_le_right
  have hlt : (x &&& 0xFF).toNat < 2 ^ 8 := by omega
  have hmod : (8 : UInt32).toNat % 32 = 8 := by decide
  rw [hmod, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt hlt

/- REF: docs/PATHFINDER_CRC32.md -/
/-- ANDing with a mask's bitwise complement equals XORing with the AND: at each bit,
    `x_i && !m_i` is `x_i` when `m_i` is clear and `0` when `m_i` is set, which is exactly
    `x_i ^^ (x_i && m_i)` either way (a per-bit case split closes it). -/
theorem and_not_eq_xor_and (x m : UInt32) : x &&& (~~~m) = x ^^^ (x &&& m) := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [UInt32.toBitVec_and, UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_not,
    BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not]
  simp only [hi, decide_true, Bool.true_and]
  cases x.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> decide

/- REF: docs/PATHFINDER_CRC32.md -/
/-- The high-24-bits mask is exactly the bitwise complement of the low-byte mask (both
    concrete 32-bit numerals; `decide` computes it directly, no free variables). -/
theorem not_0xFF_eq : (~~~(0xFF : UInt32)) = 0xFFFFFF00 := by decide

/- REF: docs/PATHFINDER_CRC32.md -/
/-- Restates `x`'s high bits (`x &&& 0xFFFFFF00`) via `and_not_eq_xor_and` and
    `not_0xFF_eq`, in the XOR form `Gbf8_additive`/`and_xor_compl` need. -/
theorem and_0xFFFFFF00_eq (x : UInt32) : x &&& 0xFFFFFF00 = x ^^^ (x &&& 0xFF) := by
  rw [← not_0xFF_eq, and_not_eq_xor_and]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- Masking off `x`'s low byte before shifting right by 8 doesn't change the result: the
    masked-off bits are exactly the ones the shift discards. -/
theorem and_high_shr8 (x : UInt32) : (x &&& 0xFFFFFF00) >>> 8 = x >>> 8 := by
  rw [and_0xFFFFFF00_eq, UInt32.shiftRight_xor, and_0xFF_shr8_zero, UInt32.xor_zero]

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `x`'s low byte and high bits XOR back together to `x` (they're complementary masks, so
    this is `y ^^^ (x ^^^ y) = x`, an XOR-cancellation rearrangement). -/
theorem and_xor_compl (x : UInt32) : (x &&& 0xFF) ^^^ (x &&& 0xFFFFFF00) = x := by
  rw [and_0xFFFFFF00_eq, UInt32.xor_comm (x &&& 0xFF) (x ^^^ (x &&& 0xFF)), UInt32.xor_assoc,
    UInt32.xor_self, UInt32.xor_zero]

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/-- **The table/closed-form connection identity**, over the complete `UInt32 x UInt32`
    domain (`poly`, `x`): applying the 8-step map to a full 32-bit value equals shifting it
    down by 8 and XORing in the 8-step map applied to just its low byte -- i.e. exactly
    what a byte-indexed CRC table precomputes. This is the design's primary route (§3.6).
    Per PA14, proven structurally rather than by `bv_decide`: split `x` into its low byte
    and high bits (`and_xor_compl`), push `Gbf8` through that XOR (`Gbf8_additive`), collapse
    the high-bits branch to a pure shift (`Gbf8_high_part`) that equals shifting `x` itself
    (`and_high_shr8`), and commute the resulting XOR into the stated order. -/
theorem G8bf_table (poly x : UInt32) :
    Gbf8 poly x = (x >>> 8) ^^^ Gbf8 poly (x &&& 0xFF) := by
  have step : Gbf8 poly x = Gbf8 poly ((x &&& 0xFF) ^^^ (x &&& 0xFFFFFF00)) := by
    rw [and_xor_compl]
  rw [step, Gbf8_additive, Gbf8_high_part, and_high_shr8, UInt32.xor_comm]

/- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023 -/
/-- `mkCrcTableEntry`'s fixed-8-iteration loop is exactly `G8` applied to the seed --
    closes by `rfl` since the iteration count (8) is a literal, not a symbolic `k`, so no
    induction (nor the `Nat.iterate`/`f^[n]` notation, which is a Mathlib addition not
    available in this Lean-core-only project) is needed. -/
theorem mkCrcTableEntry_eq_G8 (n : Nat) :
    mkCrcTableEntry n = G8 crc32Polynomial (n.toUInt32) := by
  unfold mkCrcTableEntry G8 G
  rfl

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/-- XORing in a single byte's worth of bits (`b.toUInt32 < 256`) never changes bits 8
    and above, so shifting right by 8 afterward is unaffected by that XOR. This is what
    lets the per-byte connection theorem below equate `crc32ByteStep`'s `c >>> 8` (over
    the pre-XOR accumulator) with the asm's `(c ^^^ b) >>> 8` (the value it actually
    shifts, since the assembly XORs the byte in *before* the 8-bit chain runs). Per PA13,
    proven by bit-extensionality (`BitVec.eq_of_getLsbD_eq`) rather than `bv_decide`: at bit
    index `8 + i` the XOR's right operand (`b.toUInt32`, zero-extended from 8 bits) is always
    `false` (`BitVec.getLsbD_of_ge`, reached via the default simp set), so the XOR is a no-op
    at every bit position the right-shift-by-8 exposes. -/
theorem xor_byte_shr8 (c : UInt32) (b : UInt8) : (c ^^^ b.toUInt32) >>> 8 = c >>> 8 := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [UInt32.toBitVec_shiftRight, UInt32.toBitVec_xor, UInt8.toBitVec_toUInt32,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
theorem toUInt32_toNat_and_0xFF (x : UInt32) : (x &&& 0xFF).toNat.toUInt32 = x &&& 0xFF := by
  simp

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/- REF: docs/REVIEW.md#law-12-connection-theorem-mandate-no-unlinked-twins -/
/-- **The Law 12 connection theorem this pathfinder exists to exercise**: the table-driven
    spec step (`crc32ByteStep`, via `mkCrcTableEntry`) and the assembly's inline
    8x-unrolled per-bit recurrence (`G8`, applied to the byte-XORed accumulator, matching
    the assembly's actual instruction order: XOR the byte in, *then* run the 8-bit chain)
    compute the identical function. Chains `mkCrcTableEntry_eq_G8`,
    `toUInt32_toNat_and_0xFF`, `G8_eq_Gbf8`, `G8bf_table`, and `xor_byte_shr8` -- exactly
    the algebraic chain `docs/PATHFINDER_CRC32.md` §3.6 step 3 describes in prose. -/
theorem crc32ByteStep_eq_G8 (c : UInt32) (b : UInt8) :
    crc32ByteStep c b = G8 crc32Polynomial (c ^^^ b.toUInt32) := by
  unfold crc32ByteStep
  rw [mkCrcTableEntry_eq_G8, toUInt32_toNat_and_0xFF, G8_eq_Gbf8, G8_eq_Gbf8,
    G8bf_table crc32Polynomial (c ^^^ b.toUInt32), xor_byte_shr8]

/-
## Part 3: jump-displacement round-trip at a symbolic base `rip` (design §3.8, "recommended
## not blocking" open question)

`assembleProgram`'s two-pass label resolution computes each jump's displacement via
`toDisp32`, to be consumed by the concrete jump instruction's own `step` via
`signExtend32To64`. The design explicitly left open whether this round-trips cleanly at a
*symbolic* base `rip` (as opposed to one fixed concrete address). It does, given a
mild "the program does not straddle the address-space wraparound point" hypothesis --
the code-address analogue of the routine's own `ptr.toNat + len < 2^64` buffer hypothesis.
-/

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
theorem toDisp32_add_const (nextRip : UInt64) (k : Nat) (hk : k < 2 ^ 30)
    (hbound : nextRip.toNat + k < 2 ^ 64) :
    toDisp32 (nextRip + k.toUInt64) nextRip = Int32.ofNat k := by
  unfold toDisp32
  have e1 : (nextRip + k.toUInt64).toNat = nextRip.toNat + k := by
    rw [UInt64.toNat_add]
    have hk' : k.toUInt64.toNat = k := by simp; omega
    rw [hk', Nat.mod_eq_of_lt] <;> omega
  simp only [e1]
  have hpos : (((nextRip.toNat + k : Nat) : Int) - (nextRip.toNat : Int)) ≥ 0 := by omega
  rw [if_pos hpos]
  have hval : (((nextRip.toNat + k : Nat) : Int) - (nextRip.toNat : Int)).toNat = k := by
    omega
  rw [hval]

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
theorem signExtend32To64_small (k : Nat) (hk : k < 2 ^ 30) :
    signExtend32To64 (Int32.ofNat k) = k.toUInt64 := by
  unfold signExtend32To64
  have hnn : ¬ (Int32.ofNat k < 0) := by
    rw [Int32.lt_iff_toInt_lt, Int32.toInt_ofNat_of_lt (by omega : k < 2 ^ 31)]
    simp
  rw [if_neg hnn, Int32.toUInt32_ofNat']
  have heq : (UInt32.ofNat k).toUInt64 = k.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp
    omega
  rw [heq]
  simp

/- REF: docs/PATHFINDER_CRC32.md#38-the-reformulation-is-the-design-on-both-sides-not-a-fallback-m3 -/
/-- **Resolves design open question #8 (§3.8, §11 item 8's sibling for jump arithmetic)**:
    a near jump/branch whose target is a fixed, small, compile-time-known number of bytes
    ahead of `nextRip` lands exactly on that target, for *any* symbolic base, provided the
    program's address range does not wrap `UInt64`. This is route (a) of the two the
    design left open in §3.8 ("prove the decode-lemma set generically over a symbolic
    base") -- shown tractable here for the constant-offset case every forward jump in
    `crc32SymbolicProgram` needs (each symbolic jump's displacement is a compile-time
    constant byte count, never a runtime-varying quantity). -/
theorem jump_lands_at_const_offset (nextRip : UInt64) (k : Nat) (hk : k < 2 ^ 30)
    (hbound : nextRip.toNat + k < 2 ^ 64) :
    nextRip + signExtend32To64 (toDisp32 (nextRip + k.toUInt64) nextRip) = nextRip + k.toUInt64 := by
  rw [toDisp32_add_const nextRip k hk hbound, signExtend32To64_small k hk]

/-
## Part 4: per-instruction step lemmas (design §3.1's fourteen-instruction census)

Thirteen of the fourteen predicted step lemmas, stated at the point of construction
(`X86_64Instruction.step (mov_r32 ...) s = ...`, i.e. applied directly to the smart
constructor's `AnyX86_64Instruction` result) per design §3.2. Contrary to §3.2's own
concern that a concrete-type statement would not fire against the wrapper's `step` field
without an explicit unfolding step, `rfl` closes every one of these directly: the
existential is already resolved at the literal `⟨...⟩` construction site, so kernel
reduction dispatches through the wrapper for free. The fourteenth (`MovzxR64Mem8`) is
listed as a finding, not proven here -- see the completion report.
-/

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_mov_r32 (dst : Reg32) (imm : UInt32) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_r32 dst imm) s =
      { s.setGpr32 dst imm with rip := s.rip + (if (reg32Code dst).2 then 6 else 5) } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_xor_r32 (dst src : Reg32) (s : X86_64MachineState) :
    X86_64Instruction.step (xor_r32 dst src) s =
      { (s.setGpr32 dst
            ((s.gprs (reg32To64 dst)).toUInt32 ^^^ (s.gprs (reg32To64 src)).toUInt32)).setFlagsLogic
          32 (((s.gprs (reg32To64 dst)).toUInt32 ^^^ (s.gprs (reg32To64 src)).toUInt32).toUInt64) with
        rip := s.rip + (if (reg32Code dst).2 || (reg32Code src).2 then 3 else 2) } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_cmp_r64 (dst src : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64 dst src) s =
      { s.setFlagsCmp64 (s.gprs dst) (s.gprs src) with rip := s.rip + 3 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
/-- `JaeRel32`'s concrete step: branches on `!CF` (unsigned "above or equal"), the §8(a)
    fix's replacement for the original defective signed `JgeRel32`. -/
theorem step_jae_rel32 (disp : Int32) (s : X86_64MachineState) :
    X86_64Instruction.step (jae_rel32 disp) s =
      { s with rip := if !s.cf then s.rip + 6 + signExtend32To64 disp else s.rip + 6 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_mov_r64 (dst src : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_r64 dst src) s =
      { s.setGpr64 dst (s.gprs src) with rip := s.rip + 3 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_add_r64 (dst src : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (add_r64 dst src) s =
      { (s.setGpr64 dst (s.gprs dst + s.gprs src)).setFlagsAdd64 (s.gprs dst) (s.gprs src) with
        rip := s.rip + 3 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_and_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (and_r64_imm8 dst imm) s =
      { (s.setGpr64 dst (s.gprs dst &&& signExtend8To64 imm)).setFlagsLogic64
          (s.gprs dst &&& signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_shr_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (shr_r64_imm8 dst imm) s =
      { (s.setGpr64 dst (s.gprs dst >>> (imm &&& 0x3F).toUInt64)).setFlagsShift64
          (s.gprs dst >>> (imm &&& 0x3F).toUInt64)
          (if (imm &&& 0x3F).toUInt64 > 0 && (imm &&& 0x3F).toUInt64 <= 64 then
              (s.gprs dst >>> ((imm &&& 0x3F).toUInt64 - 1)) &&& 1
            else 0)
          (if (imm &&& 0x3F).toUInt64 == 1 then (s.gprs dst >>> 63) &&& 1 else 0)
          (imm &&& 0x3F) with
        rip := s.rip + 4 } := by
  let core : X86_64MachineState :=
    { s with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  let stepped := @X86_64Instruction.step ShrR64Imm8 instX86_64InstructionShrR64Imm8
    (ShrR64Imm8.mk dst imm) core
  change ({ { stepped with stdinBuffer := s.stdinBuffer } with
    incomingRequests := s.incomingRequests } : X86_64MachineState) = _
  simp only [stepped, X86_64Instruction.step, core, X86_64MachineState.setGpr64,
    X86_64MachineState.setFlagsShift64]
  split <;> rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_cmp_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm8 dst imm) s =
      { s.setFlagsCmp64 (s.gprs dst) (signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_je_rel32 (disp : Int32) (s : X86_64MachineState) :
    X86_64Instruction.step (je_rel32 disp) s =
      { s with rip := if s.zf then s.rip + 6 + signExtend32To64 disp else s.rip + 6 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_add_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (add_r64_imm8 dst imm) s =
      { (s.setGpr64 dst (s.gprs dst + signExtend8To64 imm)).setFlagsAdd64 (s.gprs dst)
          (signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_jmp_rel32 (disp : Int32) (s : X86_64MachineState) :
    X86_64Instruction.step (jmp_rel32 disp) s =
      { s with rip := s.rip + 5 + signExtend32To64 disp } := rfl

/- REF: docs/PATHFINDER_CRC32.md#31-fourteen-distinct-instruction-types-revised-again-m5 -/
theorem step_ret_op (s : X86_64MachineState) :
    X86_64Instruction.step ret_op s =
      { s.setGpr64 .rsp (s.rsp + 8) with rip := s.read64 s.rsp } := rfl

end Stdlib.Zlib.CRC32Equivalence

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
   via a branch-free bitvector normalization discharged by `bv_decide`.
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
theorem and_one_cases (c : UInt32) : c &&& 1 = 0 ∨ c &&& 1 = 1 := by bv_decide

/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
/-- `G = Gbf` pointwise. Confirms the design's M9(a) finding: `bv_decide` invoked on the
    raw `Bool`-decidability guard fails ("abstracted ... as opaque variables"); the fix is
    to case-split on `c &&& 1` first (via `and_one_cases`) and only then invoke `bv_decide`
    on each branch, where the residual goal is pure bitvector arithmetic. -/
theorem G_eq_Gbf (poly c : UInt32) : G poly c = Gbf poly c := by
  unfold G Gbf
  rcases and_one_cases c with h | h
  · have hne : ¬ (c &&& 1 != 0) := by simp [h]
    simp only [hne]
    bv_decide
  · have hne : (c &&& 1 != 0) := by simp [h]
    simp only [hne, if_pos]
    bv_decide

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

-- **The table/closed-form connection identity**, over the complete `UInt32` domain
-- (`2^32` values) and `poly`, discharged by a single SAT certificate: applying the
-- 8-step map to a full 32-bit value equals shifting it down by 8 and XORing in the
-- 8-step map applied to just its low byte -- i.e. exactly what a byte-indexed CRC table
-- precomputes. This is the design's primary route (§3.6), verified working on this
-- toolchain (~1.8s wall time here, close to the design's own 2.3s estimate).
set_option maxHeartbeats 1000000 in
/- REF: docs/PATHFINDER_CRC32.md#36-the-connection-theorem-bvdecide-on-a-branch-free-normal-form-not-linearity-m1 -/
theorem G8bf_table (poly x : UInt32) :
    Gbf8 poly x = (x >>> 8) ^^^ Gbf8 poly (x &&& 0xFF) := by
  unfold Gbf8 Gbf
  bv_decide

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
    shifts, since the assembly XORs the byte in *before* the 8-bit chain runs). -/
theorem xor_byte_shr8 (c : UInt32) (b : UInt8) : (c ^^^ b.toUInt32) >>> 8 = c >>> 8 := by
  bv_decide

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
        rip := s.rip + 4 } := rfl

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

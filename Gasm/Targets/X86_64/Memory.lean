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
import Gasm.Core.Types
import Gasm.Targets.X86_64.Registers

-- Module layout note: `docs/MEMORY_HOOK.md` §3.1 sketches `X86_64Memory` and
-- `X86_64Mem.read`/`write` living in this file. They instead live in `MemoryCell.lean`
-- (imported transitively via `Registers.lean`), because `MemRef.effectiveAddress` below needs
-- `X86_64MachineState` (for `s.gprs`/`s.rip`) and `X86_64MachineState` needs `X86_64Memory` as
-- its `memory` field's type -- putting the sealed wrapper and the width-indexed read/write in
-- the SAME file as `X86_64MachineState` would make `Registers.lean` and this file import each
-- other. `MemoryCell.lean` breaks the cycle: it is the file the seal's `private` scope actually
-- applies to (needing only `Address`/`Byte`, not the machine state), `Registers.lean` builds the
-- state-level `read64`/`write8`/... abbrevs on top of it, and this file adds the descriptor
-- vocabulary (`MemRef`, `MemAccessSpec`) and the §3.4 lemma set on top of both. The chokepoint
-- property this design cares about -- `X86_64Mem.read`/`write` are the only functions that can
-- touch memory bytes -- is unaffected by which file states it.

namespace Gasm.Targets.X86_64

open Gasm.Core

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Canonical x86-64 effective-address term: `base + index*scale + disp`. `base := none` denotes
    RIP-relative addressing (`CallRipRel`'s indirect-call target, evaluated against the *current*
    `rip` -- callers fold the instruction's own fixed encoded length into `disp` so evaluation
    against the pre-step state yields the correct next-instruction-relative address). This is a
    deliberate widening of the design's literal `base : Reg64` sketch: `Reg64` has no case for
    the instruction pointer, and `CallRipRel` (one of the 14 memory forms) genuinely addresses
    RIP-relative, not register-relative -- the design's own text ("today's 14 forms use only
    base+disp8/disp32") did not anticipate this form. `index` is the forward slot the ISA
    expansion's SIB-indexed forms fill without a new address representation; none of today's 14
    forms use it. -/
structure MemRef where
  base  : Option Reg64 := none
  index : Option (Reg64 × Nat) := none
  disp  : UInt64 := 0

-- `disp` is `UInt64`, not the design's literal `Int`: callers supply it as the already-signed-
-- extended UInt64 bit pattern (`signExtend8To64 i.disp`, `signExtend32To64 i.disp`, or a literal
-- like `-8` -- UInt64 has a `Neg` instance and the pre-hook code already used plain `UInt64`
-- subtraction/negation for stack displacements, e.g. `push64`'s `s.rsp - 8`). This is a
-- deliberate simplification of the design's `disp : Int` sketch: an `Int`-mediated round trip
-- (`UInt8` -> signed `Int` -> two's-complement `UInt64`) needs a nontrivial connecting lemma to
-- `signExtend8To64`/`signExtend32To64` to prove a descriptor's address matches `step`'s actual
-- computed address -- exactly the fact every `writesWithin`/`readsWithin` frame lemma needs --
-- and callers already HAVE that UInt64 value in hand (it's what `step` itself computes), so
-- routing through `Int` only to convert back was pure overhead with no expressiveness gained.

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Evaluates a `MemRef` against the pre-step machine state: every declared access's dynamic
    address is `MemRef.effectiveAddress` at the state `step` was called with, uniformly
    (`docs/MEMORY_HOOK.md` §3.3). -/
def MemRef.effectiveAddress (m : MemRef) (s : X86_64MachineState) : Address :=
  let baseVal : UInt64 := match m.base with
    | some r => s.gprs r
    | none => s.rip
  let idxVal : UInt64 := match m.index with
    | some (r, scale) => s.gprs r * scale.toUInt64
    | none => 0
  baseVal + idxVal + m.disp

/- REF: docs/MEMORY_HOOK.md#3-layer-s-the-semantic-hook -/
/-- One declared access: static shape (kind, width, addressing term), dynamic address obtained by
    evaluating `ref` against the pre-step machine state. -/
structure MemAccessSpec where
  kind  : MemAccessKind
  width : MemWidth
  ref   : MemRef

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The concrete byte addresses one access spec touches, evaluated against state `s`. -/
def MemAccessSpec.addresses (spec : MemAccessSpec) (s : X86_64MachineState) : List Address :=
  let base := spec.ref.effectiveAddress s
  (List.range spec.width.bytes).map (fun k => base + k.toUInt64)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Every byte address a list of access specs of a given kind touches, evaluated against `s`. -/
def footprintFor (kind : MemAccessKind) (specs : List MemAccessSpec) (s : X86_64MachineState) : List Address :=
  (specs.filter (fun spec => spec.kind == kind)).flatMap (fun spec => spec.addresses s)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The declared write footprint: every address `step` is permitted to change. -/
def storeFootprint (specs : List MemAccessSpec) (s : X86_64MachineState) : List Address :=
  footprintFor .store specs s

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The declared read footprint: every address `step`'s result may depend on. -/
def loadFootprint (specs : List MemAccessSpec) (s : X86_64MachineState) : List Address :=
  footprintFor .load specs s

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Two memory images agree at every address in a list -- the hypothesis shape `readsWithin`
    frame lemmas take over a declared load footprint. -/
def agreeOn (addrs : List Address) (m1 m2 : X86_64Memory) : Prop :=
  ∀ a ∈ addrs, X86_64Mem.read .w8 a m1 = X86_64Mem.read .w8 a m2

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Every field of `X86_64MachineState` except `memory` agrees between two states -- the "same
    everything but memory contents" half of a `readsWithin` hypothesis. -/
def agreeOutsideMemory (s1 s2 : X86_64MachineState) : Prop :=
  s1.rip = s2.rip ∧ s1.gprs = s2.gprs ∧ s1.flags = s2.flags ∧
  s1.stdinBuffer = s2.stdinBuffer ∧ s1.incomingRequests = s2.incomingRequests ∧
  s1.fault = s2.fault

-- `WritesWithin`/`ReadsWithin` (the per-family connection obligation shape, §3.3) live in
-- `MemoryFrame/Common.lean`, not here: they quantify over `X86_64Instruction.step`/`memAccesses`,
-- and that typeclass is declared in `Instructions/Base.lean`, which in turn needs `MemAccessSpec`
-- from this file for its new `memAccesses` field -- so this file cannot import `Instructions.Base`
-- without a cycle. `MemoryFrame/Common.lean` imports both and is where the obligation shape and
-- the register-only batch lemma live.

--------------------------------------------------------------------------------------------------
-- §3.4 lemma set: the theory every future memory proof needs, proved once.
--------------------------------------------------------------------------------------------------

-- The three `UInt64` bit-algebra lemmas below exist so `read64_write64_same` can close
-- STRUCTURALLY rather than by a `bv_decide` SAT certificate. Per `docs/REVIEW.md` Law 10's
-- four-rung trust-cost ordering, `bv_decide` is rung 4 (trusted, not kernel-checked: `TCB.md`
-- T14 established that `LratCert.toReflectionProof` asserts its result through the same
-- `Lean.Meta.nativeEqTrue` routine `native_decide` uses, so the kernel never replays the LRAT
-- certificate). A structural proof is rung 1 and needs no `scripts/gate_allowlist.txt` entry at
-- all. This is the same `BitVec.eq_of_getLsbD_eq` playbook PA13/PA14 used to take
-- `Stdlib/Zlib/CRC32Equivalence.lean` to zero `bv_decide`, applied at 64 bits.
--
-- The route deliberately avoids per-bit-index case analysis over all 64 positions (the
-- obstruction a prior reviewer hit applying `BitVec.eq_of_getLsbD_eq` to the goal directly):
-- `shr_and_shl` moves every byte-selection shift into a MASK CONSTANT, after which the whole
-- eight-way little-endian reassembly is a single `AND`-over-`OR` collapse against a mask that
-- `decide` evaluates to `-1`. Only `shr_and_shl` and `and_or_and` reason bitwise, and each
-- splits on one condition, not sixty-four.

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Truncating a `UInt64` to its low byte and zero-extending back is exactly masking with
    `0xFF`. Bridges `read`'s `UInt8`-valued byte ladder into the pure mask algebra the
    reassembly identity below is stated in. -/
theorem toUInt8_toUInt64_eq_and (x : UInt64) : x.toUInt8.toUInt64 = x &&& 0xFF := by
  apply UInt64.toNat_inj.mp
  have h : x.toNat &&& (2 ^ 8 - 1) = x.toNat % 2 ^ 8 := Nat.and_two_pow_sub_one_eq_mod x.toNat 8
  rw [show (2 ^ 8 - 1 : Nat) = 255 from rfl, show (2 ^ 8 : Nat) = 256 from rfl] at h
  rw [UInt64.toNat_and]
  simp [h]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Shifting a value down by `s`, masking, and shifting back up by `s` is the same as masking
    the original value with the shifted-up mask -- the identity that turns each byte-selection
    step of a little-endian ladder into a plain `AND` against a constant. Proved by `BitVec`
    extensionality with a single split on whether the bit index is below the shift amount (no
    64-way enumeration): above it, both sides read bit `i` of `v` and bit `i - s` of the mask;
    below it, both sides are `false`. Needs no `s < 64` side condition -- `UInt64`'s shift
    semantics reduce the amount mod 64 on both sides identically. -/
theorem shr_and_shl (v m s : UInt64) : ((v >>> s) &&& m) <<< s = v &&& (m <<< s) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.getLsbD_and]
  by_cases h : i < s.toNat % 64
  · simp [h]
  · have he : s.toNat % 64 + (i - s.toNat % 64) = i := by omega
    simp [h, hi, he]

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `AND` distributes over `OR` on a shared left operand, so a chain of masked reads of the same
    value collapses into one mask (a per-bit case split on `v`'s bit closes it). -/
theorem and_or_and (v m1 m2 : UInt64) : (v &&& m1) ||| (v &&& m2) = v &&& (m1 ||| m2) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases v.toBitVec.getLsbD i <;> simp

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Little-endian reassembly: `OR`-ing a `UInt64`'s eight bytes back into their own positions
    reconstructs it. This is the whole arithmetic content of `read64_write64_same` -- everything
    else in that proof is address-disequality bookkeeping. Via `toUInt8_toUInt64_eq_and` and
    `shr_and_shl` each summand becomes `v &&& (0xFF <<< 8k)`; `and_or_and` folds the eight masks
    into one, which `decide` evaluates to `-1` (all ones), and `UInt64.and_neg_one` finishes. -/
theorem le_bytes_reassemble (v : UInt64) :
    v.toUInt8.toUInt64 |||
    ((v >>> 8).toUInt8.toUInt64 <<< 8) |||
    ((v >>> 16).toUInt8.toUInt64 <<< 16) |||
    ((v >>> 24).toUInt8.toUInt64 <<< 24) |||
    ((v >>> 32).toUInt8.toUInt64 <<< 32) |||
    ((v >>> 40).toUInt8.toUInt64 <<< 40) |||
    ((v >>> 48).toUInt8.toUInt64 <<< 48) |||
    ((v >>> 56).toUInt8.toUInt64 <<< 56) = v := by
  simp only [toUInt8_toUInt64_eq_and, shr_and_shl, and_or_and]
  rw [show ((0xFF : UInt64) ||| (0xFF <<< (8 : UInt64)) ||| (0xFF <<< (16 : UInt64))
      ||| (0xFF <<< (24 : UInt64)) ||| (0xFF <<< (32 : UInt64)) ||| (0xFF <<< (40 : UInt64))
      ||| (0xFF <<< (48 : UInt64)) ||| (0xFF <<< (56 : UInt64))) = -1 from by decide]
  exact UInt64.and_neg_one

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Width decomposition + read-over-write, same address, at the width the 14 memory forms
    overwhelmingly use: a 64-bit write is read back byte-for-byte by a same-address 64-bit read
    (today's byte ladders, made a lemma instead of implicit per-file re-derivation,
    `docs/MEMORY_HOOK.md` §3.4). Address-offset disequalities among `{a, ..., a+7}` need no
    no-overflow side condition (unlike `readByte_write_disjoint`'s external `a'`): the offsets are
    bounded constants ≤ 7, and no two of `a+i`/`a+j` for `i ≠ j ≤ 7` can collide mod 2⁶⁴ regardless
    of `a`'s value -- each such disequality is discharged by `simp` (via `UInt64.add_right_inj`)
    inline in the `simp only` set below, which collapses `write`'s eight-way `if` ladder to the
    byte each read position actually selects. What remains is `le_bytes_reassemble`. Structural
    throughout: no `bv_decide`, hence no `scripts/gate_allowlist.txt` entry (Law 10 rung 1). -/
theorem X86_64Mem.read64_write64_same (a : Address) (v : UInt64) (m : X86_64Memory) :
    X86_64Mem.read .w64 a (X86_64Mem.write .w64 a v m) = v := by
  simp only [X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte,
    beq_self_eq_true, if_true,
    show (a == a + 1) = false by simp, show (a == a + 2) = false by simp,
    show (a == a + 3) = false by simp, show (a == a + 4) = false by simp,
    show (a == a + 5) = false by simp, show (a == a + 6) = false by simp,
    show (a == a + 7) = false by simp,
    show (a + 1 == a) = false by simp, show (a + 2 == a) = false by simp,
    show (a + 3 == a) = false by simp, show (a + 4 == a) = false by simp,
    show (a + 5 == a) = false by simp, show (a + 6 == a) = false by simp,
    show (a + 7 == a) = false by simp,
    show (a + 2 == a + 1) = false by simp, show (a + 3 == a + 1) = false by simp,
    show (a + 4 == a + 1) = false by simp, show (a + 5 == a + 1) = false by simp,
    show (a + 6 == a + 1) = false by simp, show (a + 7 == a + 1) = false by simp,
    show (a + 3 == a + 2) = false by simp, show (a + 4 == a + 2) = false by simp,
    show (a + 5 == a + 2) = false by simp, show (a + 6 == a + 2) = false by simp,
    show (a + 7 == a + 2) = false by simp,
    show (a + 4 == a + 3) = false by simp, show (a + 5 == a + 3) = false by simp,
    show (a + 6 == a + 3) = false by simp, show (a + 7 == a + 3) = false by simp,
    show (a + 5 == a + 4) = false by simp, show (a + 6 == a + 4) = false by simp,
    show (a + 7 == a + 4) = false by simp,
    show (a + 6 == a + 5) = false by simp, show (a + 7 == a + 5) = false by simp,
    show (a + 7 == a + 6) = false by simp,
    Bool.false_eq_true, if_false]
  exact le_bytes_reassemble v

-- `X86_64Mem.readByte_initRegion` and `X86_64Mem.readByte_zero` live in `MemoryCell.lean`
-- (byte-granular, no `MemRef`/state dependency needed) rather than duplicated here.

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Push/pop roundtrip: popping immediately after pushing `v` returns `v`, restores RSP, and
    leaves every other register untouched, for any pre-state (the standard hardware-stack
    roundtrip fact every calling-convention proof ultimately rests on). Stated observationally
    (return value / RSP / other-register facts) rather than as one literal full-state equality:
    the mutable-update encoding of `gprs` makes a literal record equality require proving pointwise
    function equality of two `Reg64 → UInt64` closures that differ only by an unreachable-but-
    syntactically-present redundant branch, which is not `rfl` (the branch's dead-ness depends on
    `reg`, a bound variable) -- these three facts are the actual content calling-convention proofs
    need and each closes directly. -/
theorem push64_pop64_roundtrip (s : X86_64MachineState) (v : UInt64) :
    (s.push64 v).pop64.1 = v ∧
    (s.push64 v).pop64.2.rsp = s.rsp ∧
    ∀ r, r ≠ .rsp → (s.push64 v).pop64.2.gprs r = s.gprs r := by
  simp only [X86_64MachineState.push64, X86_64MachineState.pop64, X86_64MachineState.rsp,
    X86_64MachineState.setGpr64]
  refine ⟨?_, ?_, ?_⟩
  · simp [X86_64MachineState.read64, X86_64MachineState.write64, X86_64Mem.read64_write64_same]
  · have heq : (s.gprs .rsp - 8 + 8).toNat = (s.gprs .rsp).toNat := by simp
    simp [UInt64.toNat_inj.mp heq]
  · intro r hr
    simp [hr]

end Gasm.Targets.X86_64

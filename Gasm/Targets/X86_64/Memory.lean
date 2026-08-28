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
  disp  : Int := 0

/- REF: docs/MEMORY_HOOK.md#31-types-and-api -/
/-- Encodes a (possibly negative) displacement as its UInt64 two's-complement bit pattern -- the
    same wraparound convention the pre-hook code already used ad hoc (e.g. `push64`'s `s.rsp - 8`
    via plain `UInt64` subtraction). -/
def dispToUInt64 (d : Int) : UInt64 :=
  if d ≥ 0 then d.toNat.toUInt64 else 0 - (-d).toNat.toUInt64

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
  baseVal + idxVal + dispToUInt64 m.disp

/- REF: docs/MEMORY_HOOK.md#3-layer-s-the-semantic-hook -/
/-- One declared access: static shape (kind, width, addressing term), dynamic address obtained by
    evaluating `ref` against the pre-step machine state. -/
structure MemAccessSpec where
  kind  : MemAccessKind
  width : MemWidth
  ref   : MemRef

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor--the-one-source-four-consumers-read -/
/-- The concrete byte addresses one access spec touches, evaluated against state `s`. -/
def MemAccessSpec.addresses (spec : MemAccessSpec) (s : X86_64MachineState) : List Address :=
  let base := spec.ref.effectiveAddress s
  (List.range spec.width.bytes).map (fun k => base + k.toUInt64)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor--the-one-source-four-consumers-read -/
/-- Every byte address a list of access specs of a given kind touches, evaluated against `s`. -/
def footprintFor (kind : MemAccessKind) (specs : List MemAccessSpec) (s : X86_64MachineState) : List Address :=
  (specs.filter (fun spec => spec.kind == kind)).flatMap (fun spec => spec.addresses s)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor--the-one-source-four-consumers-read -/
/-- The declared write footprint: every address `step` is permitted to change. -/
def storeFootprint (specs : List MemAccessSpec) (s : X86_64MachineState) : List Address :=
  footprintFor .store specs s

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor--the-one-source-four-consumers-read -/
/-- The declared read footprint: every address `step`'s result may depend on. -/
def loadFootprint (specs : List MemAccessSpec) (s : X86_64MachineState) : List Address :=
  footprintFor .load specs s

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Two memory images agree at every address in a list -- the hypothesis shape `readsWithin`
    frame lemmas take over a declared load footprint. -/
def agreeOn (addrs : List Address) (m1 m2 : X86_64Memory) : Prop :=
  ∀ a ∈ addrs, X86_64Mem.read .w8 a m1 = X86_64Mem.read .w8 a m2

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor--the-one-source-four-consumers-read -/
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

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Read-over-write, same address: a write of width `w` at `a` is read back exactly (truncated to
    the reading width) by a same-width, same-address read. -/
theorem X86_64Mem.read_write_same (w : MemWidth) (a : Address) (v : UInt64) (m : X86_64Memory) :
    X86_64Mem.read w a (X86_64Mem.write w a v m) =
      (match w with
        | .w8  => v.toUInt8.toUInt64
        | .w16 => v.toUInt16.toUInt64
        | .w32 => v.toUInt32.toUInt64
        | .w64 => v) := by
  cases w <;> simp [X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte, X86_64Mem.writeByte] <;>
    (try omega) <;> (try bv_decide)

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Read-over-write, disjoint ranges: a write of width `wW` at `aW` never disturbs a read of width
    `wR` at `aR` whose byte range `[aR, aR+wR)` does not overlap `[aW, aW+wW)`. Wraparound at 2⁶⁴
    is ruled out by `hnov` (the disjointness hypotheses on the `Nat` addresses), matching how
    `MemoryPerm.validRange` already carries a no-overflow side condition rather than re-deriving
    it per access (`docs/MEMORY_HOOK.md` §3.4). -/
theorem X86_64Mem.read_write_disjoint (wW wR : MemWidth) (aW aR : Address) (v : UInt64) (m : X86_64Memory)
    (hnov : aR.toNat + wR.bytes ≤ aW.toNat ∨ aW.toNat + wW.bytes ≤ aR.toNat) :
    X86_64Mem.read wR aR (X86_64Mem.write wW aW v m) = X86_64Mem.read wR aR m := by
  cases wW <;> cases wR <;>
    simp only [X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte, X86_64Mem.writeByte] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | rfl
      | (exfalso; omega)
      | (congr 1 <;> omega)

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `initRegion` read-back: reading any byte of an installed image returns exactly what the
    installing function says at that address. -/
theorem X86_64Mem.readByte_initRegion (f : Address → Byte) (a : Address) :
    X86_64Mem.readByte (X86_64Mem.initRegion f) a = f a := rfl

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- `zero`'s bytes are all zero. -/
theorem X86_64Mem.readByte_zero (a : Address) : X86_64Mem.readByte X86_64Mem.zero a = 0 := rfl

/- REF: docs/MEMORY_HOOK.md#34-the-lemma-set-what-one-place-buys-proofs -/
/-- Push/pop roundtrip: popping immediately after pushing `v` returns `v` and restores RSP,
    for any pre-state (the standard hardware-stack roundtrip fact every calling-convention proof
    ultimately rests on). -/
theorem push64_pop64_roundtrip (s : X86_64MachineState) (v : UInt64) :
    (s.push64 v).pop64 = (v, s.setGpr64 .rsp (s.rsp - 8 + 8)) := by
  simp only [X86_64MachineState.push64, X86_64MachineState.pop64, X86_64MachineState.rsp,
    X86_64MachineState.setGpr64]
  constructor
  · simp [X86_64MachineState.read64, X86_64Mem.read_write_same]
  · rfl

end Gasm.Targets.X86_64

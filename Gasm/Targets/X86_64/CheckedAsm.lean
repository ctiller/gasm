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
import Gasm.Core.Permissions
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Memory
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Assembler

/-
Gasm/Targets/X86_64/CheckedAsm.lean -- Layer A, the capability authoring surface
(`docs/MEMORY_HOOK.md` #4, MH3). This is Law 11's fail-to-assemble ENFORCEMENT MECHANISM: a
checked-program type whose memory-operand constructors demand a capability citation (which
`Frame` the access is claimed against) plus an in-bounds proof, and which erases to today's
`SymbolicInstr` list before encoding -- omitting the proof is a Lean elaboration failure, not a
lint (Law 13 preference-tier 1).

THE v1 LINE (owner-ruled, `docs/adr/0040-memory-hook-approved.md` Q1 = "all yes"):
entry-anchored `Frame`s with invariant-discharged dynamic bounds. Literal-displacement accesses
against a declared region discharge via `mem_bounds`, a `decide` auto-param over `Γ`'s own
(concrete, closed) structure -- Law 10 rung 2, kernel-checked, no allowlist entry. A computed
address (the access's `MemRef` does not name a region's anchor register directly -- a register
copy, a loop-advanced pointer) does not match `mem_bounds`'s pattern and the author must supply an
explicit proof term instead, drawing on the routine's stated invariant `Inv`. Both classes v1
declares unrepresentable -- no capability citation at all, and any literal-offset overrun of a
declared region -- are genuinely unrepresentable here: `mem_bounds` fails to close (so the
constructor fails to elaborate) exactly when no region of `Γ` both names the access's base
register and admits its `[disp, disp+width)` range. Dynamic in-boundedness (loop index < length)
is CARRIED (the constructor still demands a proof term) but SEMANTICALLY discharged, in whatever
theorem actually proves the invariant `Inv` -- not by the elaborator alone. Flow-sensitive
capability transfer (register-to-register, `BlockM`-indexed frames) is the PA2/PA3 upgrade this
shape is deliberately built to accept without rework (`docs/MEMORY_HOOK.md` #4.3).

`CheckedProgram` is deliberately restricted to STRAIGHT-LINE instruction sequences (`X86_64Instr`,
never a label/jump `SymbolicInstr`): v1's frame is entry-anchored, not flow-sensitive, and a branch
is exactly where flow-sensitivity would matter (which anchor facts survive to which successor is
undecidable without `BlockM`). A checked fragment is spliced into a larger, still-raw
`List SymbolicInstr` routine at the call site (see `Stdlib/SmolAlloc/Program.lean`'s pathfinder)
rather than the whole branching routine being checked at once -- an honest, stated v1 boundary, not
a silent one.

ENCODABLE INSTRUCTION STRUCTURES STAY PROOF-FREE (Law 11's second design boundary,
`docs/MEMORY_HOOK.md` #2): the proof lives one layer up, on `CheckedInstr`/`CheckedProgram`, and
`erase` throws it away before encoding -- the decoder, the differential fuzzers, and the roundtrip
gate go on constructing `MovMem64DispReg64` etc. directly, unaffected.

INFRASTRUCTURE STATUS OF THIS FILE: this module is itself one of the "designated infrastructure
modules" the bypass gate (`Tools/CheckMemBypass.lean`, `scripts/mem_bypass_allowlist.txt`) exempts
-- alongside `Assembler.lean` (erasure/symbolic-call resolution), `Decoder.lean`, and the
fuzzer/roundtrip modules -- because it is the ONE place authorized to call the raw 14
memory-operand smart constructors (`mov_mem64_disp`, `push_r64`, ...) directly, and it does so only
after collecting the `AccessOK` proof the wrapped constructor demands. Every OTHER module must go
through this file's named wrappers (`CheckedAsm.storeReg64`, `.push`, `.ret`, ...), never the raw
constructors, to be ledger-exempt.
-/

namespace Gasm.Targets.X86_64.CheckedAsm

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler

--------------------------------------------------------------------------------------------------
-- The obligation shape (`docs/MEMORY_HOOK.md` #4.2)
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- One entry of a routine's memory frame: at the frame's anchoring point, register `anchor` holds
    the base address of a region of `len` bytes, granted with `share`. Backed by a `MemoryPerm` at
    the concrete (runtime) address the anchor register holds -- `Frame.WF` below is what actually
    produces that `MemoryPerm` term, giving the dormant `Gasm.Core.Permissions` machinery a real,
    semantically-invoked call site (Law 8) rather than a decorative mention. -/
structure RegionSpec where
  anchor : Reg64
  len    : Nat
  share  : PermissionShare
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- A routine's memory frame: the set of regions granted at its anchoring point. Pairwise
    disjointness is `Frame.WF`'s job (via Core's `DisjointTokens`), not carried on `Frame` itself,
    so an author can state a candidate frame before proving it well-formed at any particular
    state. -/
abbrev Frame := List RegionSpec

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- Whether a region held with `share` admits an access of kind `kind`: `ReadOnly` admits loads
    only (a write citing a `ReadOnly` region is exactly one of v1's unrepresentable classes,
    `docs/MEMORY_HOOK.md` #4.3); `Exclusive` admits both.

    `Locked` admits NEITHER through this ordinary load/store path -- deliberately, not an
    oversight. `docs/BORROW_MODEL.md` #2.2 (coordinator review, in flight as this lands) found an
    earlier version of this mapping treated `.Locked` identically to `.Exclusive`, which is wrong
    on the design's own re-reading: `Locked` is not "exclusive, but atomic" -- it is a THIRD
    authority point, shared-mutable (many simultaneous holders, all may store), whose
    race-freedom is discharged dynamically by atomicity rather than statically by exclusion. Every
    access to a `Locked` region must be an indivisible `.rmw`-kind access or otherwise
    synchronization-ordered -- but `MemAccessKind` (`Gasm/Targets/X86_64/MemoryCell.lean`) has
    only `load`/`store` today; the `.rmw` kind `docs/BORROW_MODEL.md` #2.2 (citing
    `docs/X86_MEMORY_MODEL.md` #2.3 Decision 1) recommends is proposed, not landed, and is Owner
    Question Q2 -- not ratified. Falsely granting Exclusive-equivalent access to `Locked` here
    would be the over-permissive direction Law 11 exists to prevent; rejecting both kinds until
    the `.rmw` extension lands is the conservative, honest line MH3's scope can actually support
    (no wired `CheckedAsm` constructor performs an atomic RMW today, on x86-64 or otherwise --
    "do not bake in the x86 shape" per the coordinator's note that an ARM exclusive-monitor access
    is a retry loop, not a single access, architecture-neutrality this file does not need to
    solve). -/
def shareAllows : PermissionShare → MemAccessKind → Bool
  | .ReadOnly,  .load  => true
  | .ReadOnly,  .store => false
  | .Exclusive, _      => true
  | .Locked,    _       => false

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- A frame is well-formed at a concrete machine state `s` when every region's anchor+len is a
    genuine `MemoryPerm` (no address-space wraparound, non-empty -- the same `validRange`/
    `nonEmpty` obligations `Gasm.Core.Permissions` already states) and the regions are pairwise
    disjoint via Core's own `DisjointTokens`, evaluated at the anchors' CURRENT values in `s`. This
    is the real call site Law 8 requires: `Frame.WF.perm` below literally constructs a
    `MemoryPerm` term from it, and `MemSafe`-shaped theorems (`docs/MEMORY_HOOK.md` #4.4) take it
    as a hypothesis alongside the routine's own precondition. -/
def Frame.WF (Γ : Frame) (s : X86_64MachineState) : Prop :=
  (∀ rs ∈ Γ, (s.gprs rs.anchor).toNat + rs.len ≤ 2 ^ 64 ∧ rs.len > 0) ∧
  DisjointTokens (Γ.map (fun rs => (s.gprs rs.anchor, rs.len, rs.share)))

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- Extracts the genuine `MemoryPerm` token `Frame.WF` asserts exists for a region of `Γ`, at the
    address `s` actually holds for its anchor register. The literal, semantically-invoked call
    site: no code elsewhere constructs a `MemoryPerm` for a frame region except through this. -/
def Frame.WF.perm {Γ : Frame} {s : X86_64MachineState} (h : Frame.WF Γ s) (rs : RegionSpec)
    (hmem : rs ∈ Γ) : MemoryPerm (s.gprs rs.anchor) rs.len rs.share :=
  ⟨(h.1 rs hmem).1, (h.1 rs hmem).2⟩

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- The per-access obligation: under frame `Γ`, well-formed at `s`, and the author-stated
    program-point invariant `Inv`, the access `acc`'s dynamic address (evaluated at `s`) lands
    inside some region of `Γ` whose share admits the access kind. `s` ranges over every state
    reachable at this access's program point that satisfies `Inv` -- for a literal-displacement
    access whose `MemRef` names a region's anchor register directly, `Inv` plays no role in the
    proof at all (see `AccessOK.ofLiteral`/`literalAccessOK`, `mem_bounds`'s target); for a
    computed address the author's proof term is precisely what supplies the missing link between
    `Inv` and the region. -/
def AccessOK (Γ : Frame) (Inv : X86_64MachineState → Prop) (acc : MemAccessSpec) : Prop :=
  ∀ s : X86_64MachineState, Inv s → Frame.WF Γ s →
    ∃ rs ∈ Γ, shareAllows rs.share acc.kind = true ∧
      (s.gprs rs.anchor).toNat ≤ (acc.ref.effectiveAddress s).toNat ∧
      (acc.ref.effectiveAddress s).toNat + acc.width.bytes ≤ (s.gprs rs.anchor).toNat + rs.len

--------------------------------------------------------------------------------------------------
-- Literal-displacement discharge: `mem_bounds`, the `decide`/`omega` auto-param (Law 10 rung 2)
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- Pure, `Γ`-structural (no machine state) decision of the literal-displacement case: does `Γ`
    contain a region literally anchored at `r` whose share admits `kind` and whose
    `[disp, disp+width)` fits inside its declared length? Fully computable when `Γ`/`r`/`disp`/
    `w`/`kind` are closed terms, which they are at every real call site (a checked program's frame
    and every instruction's operands are concrete) -- this is exactly what makes it `decide`-able,
    the mechanism `mem_bounds` runs. -/
def literalAccessOK (Γ : Frame) (r : Reg64) (disp : UInt64) (w : MemWidth) (kind : MemAccessKind) :
    Bool :=
  Γ.any (fun rs => decide (rs.anchor = r) && shareAllows rs.share kind &&
    Nat.ble (disp.toNat + w.bytes) rs.len)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `literalAccessOK`'s soundness: a positive decision genuinely discharges `AccessOK`, for ANY
    `Inv` (the literal case never needs it -- the access's `MemRef` names the anchor register
    directly, so `s.gprs r = s.gprs rs.anchor` by the very shape of the term, no invariant
    required). The address-arithmetic step needs `Frame.WF`'s no-wraparound fact (the region's
    `MemoryPerm.validRange`-equivalent) exactly the way `MemoryCell.lean`'s `readByte_write_disjoint`
    needed an explicit `hno` -- without it, `s.gprs rs.anchor + disp` could wrap past 2⁶⁴ and land
    outside the region despite `disp` being small. -/
theorem AccessOK.ofLiteral {Γ : Frame} {Inv : X86_64MachineState → Prop}
    {r : Reg64} {disp : UInt64} {w : MemWidth} {kind : MemAccessKind}
    (h : literalAccessOK Γ r disp w kind = true) :
    AccessOK Γ Inv ⟨kind, w, ⟨some r, none, disp⟩⟩ := by
  intro s _hInv hwf
  unfold literalAccessOK at h
  rw [List.any_eq_true] at h
  obtain ⟨rs, hmem, hcond⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at hcond
  obtain ⟨⟨heq, hshare⟩, hbound⟩ := hcond
  subst heq
  have hnw := (hwf.1 rs hmem).1
  have hlt := UInt64.toNat_lt (s.gprs rs.anchor)
  have hwpos : w.bytes ≥ 1 := by cases w <;> decide
  have hsum : (s.gprs rs.anchor).toNat + disp.toNat < 2 ^ 64 := by omega
  refine ⟨rs, hmem, hshare, ?_, ?_⟩ <;>
    (simp only [MemRef.effectiveAddress, UInt64.toNat_add,
      UInt64.reduceToNat, Nat.add_zero, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hsum]
     omega)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- The auto-param every `CheckedAsm` memory constructor's proof obligation defaults to
    (`h := by mem_bounds`): reduces the goal to `AccessOK.ofLiteral`'s hypothesis and runs
    `decide` on it. Succeeds exactly on the literal-displacement, in-bounds case; fails to
    elaborate on every other input -- a missing capability citation (no region of `Γ` names the
    base register at all), a literal overrun (a matching region exists but `disp+width > len`), or
    a genuinely computed address (`MemRef`'s base is not literally an anchor register) -- which is
    Law 11's bar: the artifact does not build. -/
macro "mem_bounds" : tactic => `(tactic| exact AccessOK.ofLiteral (by decide))

--------------------------------------------------------------------------------------------------
-- The checked-program type and erasure (`docs/MEMORY_HOOK.md` #4.5)
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#45-erasure-coexistence-and-the-bypass-gate -/
/-- One checked instruction under frame `Γ` and program-point invariant `Inv`: either a
    register-only `X86_64Instr` (carries no obligation -- true by construction, since a
    register-only form's `memAccesses` is `[]`, `docs/MEMORY_HOOK.md` #3.3), or a memory-operand
    instruction paired with a proof that EVERY access it declares is `AccessOK` against `Γ`. -/
inductive CheckedInstr (Γ : Frame) (Inv : X86_64MachineState → Prop) : Type 1 where
  | plain : X86_64Instr → CheckedInstr Γ Inv
  | mem : (i : X86_64Instr) →
      (∀ acc ∈ X86_64Instruction.memAccesses i, AccessOK Γ Inv acc) →
      CheckedInstr Γ Inv

/- REF: docs/MEMORY_HOOK.md#45-erasure-coexistence-and-the-bypass-gate -/
/-- A checked, straight-line routine fragment: a list of checked instructions sharing one frame
    and invariant. -/
abbrev CheckedProgram (Γ : Frame) (Inv : X86_64MachineState → Prop) := List (CheckedInstr Γ Inv)

/- REF: docs/MEMORY_HOOK.md#45-erasure-coexistence-and-the-bypass-gate -/
/-- Erases a checked program to today's `SymbolicInstr` list -- literally a `List.map` throwing
    away the proof, so the assembler/linker/emitter pipeline downstream is completely untouched:
    the ENCODING of a checked and an unchecked authoring of the same instruction sequence is
    identical by construction, not merely claimed to be. Zero-cost proof erasure, the same shape
    `docs/API_STATE_MODELS.md` establishes for `ComposedState`. -/
def erase {Γ : Frame} {Inv : X86_64MachineState → Prop} : CheckedProgram Γ Inv → List SymbolicInstr :=
  List.map fun
    | .plain i => .concrete i
    | .mem i _ => .concrete i

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- Direct interpreter for a checked program, folding `step` left-to-right (straight-line, no
    labels/jumps to resolve -- `erase` followed by re-decoding would give the identical result,
    since `erase` never changes which concrete instruction each node is; this is the more directly
    provable route for `MemSafe`). -/
def CheckedProgram.run {Γ : Frame} {Inv : X86_64MachineState → Prop} (prog : CheckedProgram Γ Inv)
    (s : X86_64MachineState) : X86_64MachineState :=
  prog.foldl (fun st ci => match ci with
    | .plain i => X86_64Instruction.step i st
    | .mem i _ => X86_64Instruction.step i st) s

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- The dynamic footprint of running a checked program from `s`: the union, along the trace, of
    every declared access's addresses -- evaluated at each instruction's own PRE-step state,
    uniformly, matching `docs/MEMORY_HOOK.md` #3.3's convention. Definable without interpreter
    instrumentation because `memAccesses` is data (§3.3's whole point). -/
def CheckedProgram.dynamicFootprint {Γ : Frame} {Inv : X86_64MachineState → Prop}
    (prog : CheckedProgram Γ Inv) (s : X86_64MachineState) : List Address :=
  (prog.foldl (fun (acc : List Address × X86_64MachineState) ci =>
      match ci with
      | .plain i => (acc.1, X86_64Instruction.step i acc.2)
      | .mem i _ =>
        let addrs := (X86_64Instruction.memAccesses i).flatMap (·.addresses acc.2)
        (acc.1 ++ addrs, X86_64Instruction.step i acc.2))
    ([], s)).1

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- The footprint a frame actually grants at a state `s`: every byte address of every region,
    evaluated at the anchors' current values. -/
def grantedFootprint (Γ : Frame) (s : X86_64MachineState) : List Address :=
  Γ.flatMap (fun rs => (List.range rs.len).map (fun k => s.gprs rs.anchor + k.toUInt64))

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- The `MemSafe` SHAPE (`docs/MEMORY_HOOK.md` #4.4): the general statement every PA4 migration
    instantiates. NOT proved here in general -- v1 is entry-anchored, not flow-sensitive, so a
    general proof would need exactly the typestate machinery PA2/PA3 supplies; what MH3 delivers
    is this shape plus ONE discharged instance (the pathfinder routine,
    `Stdlib/SmolAlloc/Program.lean`'s `freshAllocHeaderMemSafe`). Restated as a `def` (a
    proposition-builder), not a `theorem`, precisely because it is not claimed to hold in
    general -- a bare `axiom`/`sorry` here would be exactly the facade Law 8 prohibits.

    RECORDED DEPENDENCY (adversarial review, in-flight as this lands): a review of MH1's chain
    found `X86_64Memory`'s `private mk ::` seal does not privatize Lean's auto-generated
    `casesOn`/`rec` eliminators (available in PROOFS, not just runtime code -- a leak via
    `m.casesOn (fun f => f)` compiles and is `rfl`-equal to the sealed field), and that
    `ReadsWithin` (`Gasm/Targets/X86_64/MemoryFrame/Common.lean`) does not constrain the resulting
    MEMORY of its two related steps, only `agreeOutsideMemory` -- so a hypothetical memory-to-
    memory form could read an undeclared location and smuggle it into a declared write without
    `ReadsWithin` catching it. Neither defect is exploited by any of today's 14 registered forms
    (confirmed by the reviewer), and NEITHER `MemSafeStatement` here NOR `AccessOK`/`Frame.WF`/
    `AccessOK.addresses_subset_granted` above cite the seal or `WritesWithin`/`ReadsWithin` at
    all -- this file's soundness does not rest on either premise. The pathfinder instance
    (`Stdlib/SmolAlloc/MemSafety.lean`'s `freshAllocHeaderMemSafe`) independently verifies its two
    forms' declared-vs-actual correspondence directly against their own `step` definitions
    (`mov_mem64_disp`/`mov_mem64_disp_imm`, both pure register/immediate stores, not memory-to-
    memory) rather than citing the general connection theorems. A FUTURE `MemSafeStatement`
    instance that instead cites `WritesWithin`/`ReadsWithin` directly (as PA4 migrations of
    memory-to-memory forms, should any be added, would need to) inherits `ReadsWithin`'s present
    weakness until the fix lands; recorded here rather than silently assumed away. -/
def MemSafeStatement {Γ : Frame} {Inv : X86_64MachineState → Prop} (prog : CheckedProgram Γ Inv)
    (Pre : X86_64MachineState → Prop) : Prop :=
  ∀ s₀, Pre s₀ → Inv s₀ → Frame.WF Γ s₀ →
    ∀ a ∈ prog.dynamicFootprint s₀, a ∈ grantedFootprint Γ s₀

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- The general bridge every `MemSafeStatement` instance reduces to: a discharged `AccessOK`
    proof, evaluated at a state satisfying `Inv`/`Frame.WF`, places every one of the access's own
    concrete byte addresses inside the frame's granted footprint. Proved once here so a routine's
    `MemSafe` proof never has to re-derive this arithmetic per instruction -- it only has to
    thread `Inv`/`Frame.WF` forward across its own straight-line steps (register-file invariance
    across memory-only instructions) and hand each access's own `h` (already on file, from the
    `CheckedAsm` constructor that built it) to this lemma. -/
theorem AccessOK.addresses_subset_granted {Γ : Frame} {Inv : X86_64MachineState → Prop}
    {acc : MemAccessSpec} (hok : AccessOK Γ Inv acc) {s : X86_64MachineState}
    (hs : Inv s) (hwf : Frame.WF Γ s) :
    ∀ a ∈ acc.addresses s, a ∈ grantedFootprint Γ s := by
  obtain ⟨rs, hmem, _hshare, hlo, hhi⟩ := hok s hs hwf
  have hlt := UInt64.toNat_lt (s.gprs rs.anchor)
  have haddr_lt : (acc.ref.effectiveAddress s).toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hnw := (hwf.1 rs hmem).1
  intro a ha
  simp only [MemAccessSpec.addresses, List.mem_map, List.mem_range] at ha
  obtain ⟨k, hk, hka⟩ := ha
  have hsum : (acc.ref.effectiveAddress s).toNat + k < 2 ^ 64 := by omega
  have hka' : a.toNat = (acc.ref.effectiveAddress s).toNat + k := by
    rw [← hka]; simp [UInt64.toNat_add]; omega
  have hlo' : (s.gprs rs.anchor).toNat + (a.toNat - (s.gprs rs.anchor).toNat) < 2 ^ 64 := by omega
  simp only [grantedFootprint, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨rs, hmem, a.toNat - (s.gprs rs.anchor).toNat, by omega, ?_⟩
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add]
  omega

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- Every `mov_mem64_disp` store leaves the register file untouched -- true by construction (its
    `step` only ever updates `.memory` and `.rip`), stated once so a routine's `MemSafe` proof can
    thread a frame's anchor value forward across a straight-line run of stores without re-deriving
    this per instruction. -/
theorem mov_mem64_disp_step_gprs (basePtr : Reg64) (disp : UInt8) (srcReg : Reg64)
    (s : X86_64MachineState) :
    (X86_64Instruction.step (mov_mem64_disp basePtr disp srcReg) s).gprs = s.gprs := rfl

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- `mov_mem64_disp_imm`'s register-file-invariance twin. -/
theorem mov_mem64_disp_imm_step_gprs (basePtr : Reg64) (disp : UInt8) (imm : UInt32)
    (s : X86_64MachineState) :
    (X86_64Instruction.step (mov_mem64_disp_imm basePtr disp imm) s).gprs = s.gprs := rfl

--------------------------------------------------------------------------------------------------
-- Named authoring wrappers -- the ONLY place the raw 14 memory-form smart constructors may be
-- called outside the bypass ledger (see this file's header comment and
-- `scripts/mem_bypass_allowlist.txt`). Covers the forms the pathfinder routine needs; PA4 extends
-- this set as it migrates further forms.
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- A register-only instruction, carried through with no memory obligation. -/
def plain {Γ : Frame} {Inv : X86_64MachineState → Prop} (i : X86_64Instr) : CheckedInstr Γ Inv :=
  .plain i

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `mov qword [basePtr + disp], srcReg` -- checked. The literal-displacement authoring pattern
    (`docs/MEMORY_HOOK.md` #4.2's own example) that dominates `Stdlib/Zlib/X86_64.lean`'s
    RSP-frame/header-field stores. -/
def storeReg64 {Γ : Frame} {Inv : X86_64MachineState → Prop} (basePtr : Reg64) (disp : UInt8)
    (srcReg : Reg64)
    (h : AccessOK Γ Inv ⟨.store, .w64, ⟨some basePtr, none, signExtend8To64 disp⟩⟩ := by
      mem_bounds) :
    CheckedInstr Γ Inv :=
  .mem (mov_mem64_disp basePtr disp srcReg) (by
    intro acc hacc
    have hspec : X86_64Instruction.memAccesses (mov_mem64_disp basePtr disp srcReg)
        = [⟨.store, .w64, ⟨some basePtr, none, signExtend8To64 disp⟩⟩] := rfl
    rw [hspec, List.mem_singleton] at hacc
    subst hacc
    exact h)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `mov qword [basePtr + disp], imm32` -- checked. -/
def storeImm64 {Γ : Frame} {Inv : X86_64MachineState → Prop} (basePtr : Reg64) (disp : UInt8)
    (imm : UInt32)
    (h : AccessOK Γ Inv ⟨.store, .w64, ⟨some basePtr, none, signExtend8To64 disp⟩⟩ := by
      mem_bounds) :
    CheckedInstr Γ Inv :=
  .mem (mov_mem64_disp_imm basePtr disp imm) (by
    intro acc hacc
    have hspec : X86_64Instruction.memAccesses (mov_mem64_disp_imm basePtr disp imm)
        = [⟨.store, .w64, ⟨some basePtr, none, signExtend8To64 disp⟩⟩] := rfl
    rw [hspec, List.mem_singleton] at hacc
    subst hacc
    exact h)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `mov dstReg, qword [basePtr + disp]` -- checked. -/
def loadReg64 {Γ : Frame} {Inv : X86_64MachineState → Prop} (dstReg basePtr : Reg64) (disp : UInt8)
    (h : AccessOK Γ Inv ⟨.load, .w64, ⟨some basePtr, none, signExtend8To64 disp⟩⟩ := by
      mem_bounds) :
    CheckedInstr Γ Inv :=
  .mem (mov_reg64_mem64_disp dstReg basePtr disp) (by
    intro acc hacc
    have hspec : X86_64Instruction.memAccesses (mov_reg64_mem64_disp dstReg basePtr disp)
        = [⟨.load, .w64, ⟨some basePtr, none, signExtend8To64 disp⟩⟩] := rfl
    rw [hspec, List.mem_singleton] at hacc
    subst hacc
    exact h)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `push r64` -- checked: a store of `r` at `[rsp - 8]`. -/
def push {Γ : Frame} {Inv : X86_64MachineState → Prop} (r : Reg64)
    (h : AccessOK Γ Inv ⟨.store, .w64, ⟨some .rsp, none, (-8 : UInt64)⟩⟩ := by mem_bounds) :
    CheckedInstr Γ Inv :=
  .mem (push_r64 r) (by
    intro acc hacc
    have hspec : X86_64Instruction.memAccesses (push_r64 r)
        = [⟨.store, .w64, ⟨some .rsp, none, (-8 : UInt64)⟩⟩] := rfl
    rw [hspec, List.mem_singleton] at hacc
    subst hacc
    exact h)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `pop r64` -- checked: a load from `[rsp]`. -/
def pop {Γ : Frame} {Inv : X86_64MachineState → Prop} (r : Reg64)
    (h : AccessOK Γ Inv ⟨.load, .w64, ⟨some .rsp, none, (0 : UInt64)⟩⟩ := by mem_bounds) :
    CheckedInstr Γ Inv :=
  .mem (pop_r64 r) (by
    intro acc hacc
    have hspec : X86_64Instruction.memAccesses (pop_r64 r)
        = [⟨.load, .w64, ⟨some .rsp, none, (0 : UInt64)⟩⟩] := rfl
    rw [hspec, List.mem_singleton] at hacc
    subst hacc
    exact h)

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `ret` -- checked: a load of the return address from `[rsp]`. -/
def ret {Γ : Frame} {Inv : X86_64MachineState → Prop}
    (h : AccessOK Γ Inv ⟨.load, .w64, ⟨some .rsp, none, (0 : UInt64)⟩⟩ := by mem_bounds) :
    CheckedInstr Γ Inv :=
  .mem ret_op (by
    intro acc hacc
    have hspec : X86_64Instruction.memAccesses ret_op
        = [⟨.load, .w64, ⟨some .rsp, none, (0 : UInt64)⟩⟩] := rfl
    rw [hspec, List.mem_singleton] at hacc
    subst hacc
    exact h)

--------------------------------------------------------------------------------------------------
-- The computed-address case (`docs/MEMORY_HOOK.md` #4.2's second example): an access whose
-- `MemRef` does not name a frame anchor directly, discharged by an explicit invariant-derived
-- proof term rather than `mem_bounds`'s literal-only automation. Illustrative, not tied to the
-- pathfinder routine (which is entirely literal-displacement) -- demonstrates the shape the loop
-- case (a buffer scan) will use once a routine needs it.
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#42-the-obligation-shape -/
/-- `Inv` states exactly the fact a loop invariant would establish at some later program point:
    the working register `rsi` currently equals the entry anchor `rdi` plus an in-bounds offset.
    `mem_bounds` cannot discharge this (`rsi` is not literally `Γ`'s anchor register), so the
    proof unfolds `AccessOK` directly and uses `hInv` -- exactly the shape
    `CheckedAsm.loadReg64 ... (h := inv_implies_rsi_in_input_region ...)` sketches in the design. -/
example (Γ : Frame) (hΓ : Γ = [⟨.rdi, 16, .ReadOnly⟩])
    (Inv : X86_64MachineState → Prop) (hInv : ∀ s, Inv s → s.gprs .rsi = s.gprs .rdi + 4) :
    AccessOK Γ Inv ⟨.load, .w32, ⟨some .rsi, none, 0⟩⟩ := by
  intro s hs hwf
  have hnw : (s.gprs (.rdi : Reg64)).toNat + 16 ≤ 2 ^ 64 :=
    (hwf.1 ⟨.rdi, 16, .ReadOnly⟩ (by simp [hΓ])).1
  refine ⟨⟨.rdi, 16, .ReadOnly⟩, ?_, ?_, ?_, ?_⟩
  · simp [hΓ]
  · decide
  · simp only [MemRef.effectiveAddress, hInv s hs, UInt64.toNat_add, UInt64.reduceToNat]; omega
  · simp only [MemRef.effectiveAddress, hInv s hs, MemWidth.bytes, UInt64.toNat_add, UInt64.reduceToNat]
    omega

--------------------------------------------------------------------------------------------------
-- #4.6: the read-binder composition, restated in statement form (Spike 4's undischargeable case)
--------------------------------------------------------------------------------------------------

/- REF: docs/MEMORY_HOOK.md#46-relation-to-the-read-binder-contract-deliberately-not-unified -/
/-- The composed obligation `docs/MEMORY_HOOK.md` #4.6 / `docs/READ_BINDER_CONTRACT.md` #5
    DESCRIBE (a design target, not a report of live enforcement -- see the accuracy note below): a
    routine that writes `requested` bytes read from a syscall into a `capacity`-byte destination
    region would need to discharge `AccessOK` for every length such a read's quantifier could
    honestly range over (0 through `requested`), not merely the ones that happen to fit. Stated
    here purely as a `Prop`-shape over `AccessOK` -- write-side only, and not proved, cited as
    live, or connected to any read obligation -- so the shape is checkable directly: instantiated
    at Spike 4's own witness (`requested = 128`, `capacity = 16`), `writeSafeForAll` is a statement
    quantified from 0 to 128 while the granted region is only 16 bytes wide -- for every `n` from
    17 to 128 the store `⟨.store, .w8, ⟨some destAnchor, none, n-1⟩⟩` cites an offset that
    overruns the region, so `AccessOK` is undischargeable for those `n` by `AccessOK.ofLiteral`'s
    own decision procedure (`literalAccessOK Γ destAnchor (n-1) .w8 .store = false` whenever
    `n - 1 ≥ capacity`, checkable by `decide` per instance) -- IF a routine were ever obligated to
    prove `writeSafeForAll` for these numbers, that obligation would fail at authoring time rather
    than silently passing. Nothing here narrows or asserts any read-side quantifier, and nothing
    here weakens `AccessOK`'s own bound to `requested` instead of `capacity` -- the write side and
    the read side stay two distinct, uncomposed mechanisms (`docs/READ_BINDER_CONTRACT.md` #5's
    conclusion).

    ACCURACY NOTE (do not overclaim from this file): `docs/READ_BINDER_CONTRACT.md`'s own
    `ReadBinderObligation`/`IsValidReadChunk`/`ChunksOf` are NOT currently wired to any consumer
    (zero call sites outside their own two files), and `splitBytes` is today a deterministic
    maximal-greedy function, not a quantifier ranging nondeterministically over every chunking --
    every in-tree spike also requests fewer bytes than its cap. So this model cannot currently
    PRODUCE a short read, and no live obligation anywhere actually quantifies `n` from `0` to
    `requested` the way `writeSafeForAll` does above; that quantification is this definition's own
    stipulation, offered as the composed obligation's SHAPE (per this task's acceptance criterion:
    "statement + discussion suffice; closing Spike 4 itself remains N8/PA17 scope"), not evidence
    that the read side is closed, wired, or live. Closing that gap is N8/PA17's and the read-binder
    contract's own consumer-wiring work, neither of which this file performs or claims to. -/
def writeSafeForAll (Γ : Frame) (Inv : X86_64MachineState → Prop) (destAnchor : Reg64)
    (requested : Nat) : Prop :=
  ∀ n : Nat, n ≤ requested → n > 0 →
    AccessOK Γ Inv ⟨.store, .w8, ⟨some destAnchor, none, (n - 1).toUInt64⟩⟩

/- REF: docs/MEMORY_HOOK.md#46-relation-to-the-read-binder-contract-deliberately-not-unified -/
/-- Spike 4's concrete witness: `requested = 128` against a 16-byte destination is undischargeable
    -- `writeSafeForAll` fails at `n = 17` (offset 16, which overruns a 16-byte region), by
    `literalAccessOK`'s own decision procedure. This is the "requested > capacity is a proof
    failure at authoring time" claim, checked mechanically rather than merely argued in prose. -/
example : literalAccessOK [⟨.r13, 16, .Exclusive⟩] .r13 (16 : UInt64) .w8 .store = false := by
  decide

end Gasm.Targets.X86_64.CheckedAsm

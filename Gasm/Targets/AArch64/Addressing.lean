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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.MemoryCell

namespace Gasm.Targets.AArch64

open Gasm.Core

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Shift types supported in AArch64 addressing and data processing operands. -/
inductive ShiftType where
  | LSL
  | LSR
  | ASR
  | ROR
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Formats ShiftType to lowercase assembly mnemonic. -/
def ShiftType.toString : ShiftType → String
  | .LSL => "lsl"
  | .LSR => "lsr"
  | .ASR => "asr"
  | .ROR => "ror"

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- ToString instance for ShiftType. -/
instance : ToString ShiftType where
  toString := ShiftType.toString

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Evaluates a shift operation on a 64-bit unsigned integer. -/
def ShiftType.apply (st : ShiftType) (val : UInt64) (amount : Nat) : UInt64 :=
  match st with
  | .LSL =>
    if amount == 0 then val
    else if amount >= 64 then 0
    else val <<< amount.toUInt64
  | .LSR =>
    if amount == 0 then val
    else if amount >= 64 then 0
    else val >>> amount.toUInt64
  | .ASR =>
    if amount == 0 then val
    else if amount >= 64 then
      if (val >>> 63) == 1 then 0xFFFFFFFFFFFFFFFF else 0
    else
      let shifted := val >>> amount.toUInt64
      if (val >>> 63) == 1 then
        shifted ||| (0xFFFFFFFFFFFFFFFF <<< (64 - amount.toUInt64))
      else shifted
  | .ROR =>
    let shift := amount % 64
    if shift == 0 then val
    else (val >>> shift.toUInt64) ||| (val <<< (64 - shift.toUInt64))

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Extension and sign-extension types supported in AArch64 register operands. -/
inductive ExtendType where
  | UXTB
  | UXTH
  | UXTW
  | UXTX
  | SXTB
  | SXTH
  | SXTW
  | SXTX
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Formats ExtendType to lowercase assembly mnemonic. -/
def ExtendType.toString : ExtendType → String
  | .UXTB => "uxtb"
  | .UXTH => "uxth"
  | .UXTW => "uxtw"
  | .UXTX => "uxtx"
  | .SXTB => "sxtb"
  | .SXTH => "sxth"
  | .SXTW => "sxtw"
  | .SXTX => "sxtx"

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- ToString instance for ExtendType. -/
instance : ToString ExtendType where
  toString := ExtendType.toString

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Evaluates an extend or sign-extend operation on a 64-bit integer. -/
def ExtendType.apply (et : ExtendType) (val : UInt64) : UInt64 :=
  match et with
  | .UXTB => val &&& 0xFF
  | .UXTH => val &&& 0xFFFF
  | .UXTW => val &&& 0xFFFFFFFF
  | .UXTX => val
  | .SXTB =>
    let b := val &&& 0xFF
    if (b >>> 7) == 1 then b ||| 0xFFFFFFFFFFFFFF00 else b
  | .SXTH =>
    let h := val &&& 0xFFFF
    if (h >>> 15) == 1 then h ||| 0xFFFFFFFFFFFF0000 else h
  | .SXTW =>
    let w := val &&& 0xFFFFFFFF
    if (w >>> 31) == 1 then w ||| 0xFFFFFFFF00000000 else w
  | .SXTX => val

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Constructs a 64-bit signed immediate `Int64` from an arbitrary `Int`. -/
def int64OfInt (n : Int) : Int64 :=
  if n >= 0 then
    Int64.ofUInt64 n.toNat.toUInt64
  else
    Int64.ofUInt64 (0 - (-n).toNat.toUInt64)

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Constructs a 64-bit signed immediate `Int64` from a raw `UInt64` two's-complement bit pattern. -/
def int64OfUInt64 (u : UInt64) : Int64 :=
  Int64.ofUInt64 u

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Canonical AArch64 memory addressing modes covering immediate, indexed, register, and PC-relative forms. -/
inductive AArch64AddrMode where
  | immOffset (base : Reg64) (imm : Int64)
  | preIndex  (base : Reg64) (imm : Int64)
  | postIndex (base : Reg64) (imm : Int64)
  | regOffset (base : Reg64) (offset : Reg64) (shift : Option (ShiftType × Nat) := none)
  | literal   (offset : Int64)
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Formats an immediate displacement into standard signed assembly syntax (e.g. `#-16` or `#16`). -/
def AArch64AddrMode.formatImm (imm : Int64) : String :=
  let i := imm.toInt
  if i < 0 then s!"#-{ -i }"
  else s!"#{i}"

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Formats an addressing mode into standard AArch64 assembly syntax. -/
def AArch64AddrMode.toString (m : AArch64AddrMode) : String :=
  match m with
  | .immOffset base imm =>
    if imm.toUInt64 == 0 then s!"[{base}]"
    else s!"[{base}, {AArch64AddrMode.formatImm imm}]"
  | .preIndex base imm =>
    s!"[{base}, {AArch64AddrMode.formatImm imm}]!"
  | .postIndex base imm =>
    s!"[{base}], {AArch64AddrMode.formatImm imm}"
  | .regOffset base offset shift =>
    match shift with
    | none => s!"[{base}, {offset}]"
    | some (st, amt) =>
      if amt == 0 then s!"[{base}, {offset}]"
      else s!"[{base}, {offset}, {st} #{amt}]"
  | .literal offset =>
    s!"[pc, {AArch64AddrMode.formatImm offset}]"

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- ToString instance for AArch64AddrMode. -/
instance : ToString AArch64AddrMode where
  toString := AArch64AddrMode.toString

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Evaluates an addressing mode given a general register lookup function and the current PC.
    Returns the effective memory address and an optional base register writeback pair `(register, updatedAddress)`. -/
def evalAddr (mode : AArch64AddrMode) (getReg : Reg64 → UInt64) (pc : Address) :
    Address × Option (Reg64 × Address) :=
  match mode with
  | .immOffset base imm =>
    let addr := getReg base + imm.toUInt64
    (addr, none)
  | .preIndex base imm =>
    let addr := getReg base + imm.toUInt64
    (addr, some (base, addr))
  | .postIndex base imm =>
    let addr := getReg base
    let newBase := addr + imm.toUInt64
    (addr, some (base, newBase))
  | .regOffset base offset shift =>
    let baseVal := getReg base
    let offVal := getReg offset
    let shifted := match shift with
      | none => offVal
      | some (st, amt) => st.apply offVal amt
    (baseVal + shifted, none)
  | .literal offset =>
    (pc + offset.toUInt64, none)

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Computes only the effective memory access address of an addressing mode. -/
def effectiveAddress (mode : AArch64AddrMode) (getReg : Reg64 → UInt64) (pc : Address) : Address :=
  (evalAddr mode getReg pc).1

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Computes only the optional writeback pair of an addressing mode. -/
def writeback (mode : AArch64AddrMode) (getReg : Reg64 → UInt64) (pc : Address) : Option (Reg64 × Address) :=
  (evalAddr mode getReg pc).2

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Indicates whether an addressing mode modifies its base register via pre-index or post-index writeback. -/
def AArch64AddrMode.hasWriteback (mode : AArch64AddrMode) : Bool :=
  match mode with
  | .preIndex .. | .postIndex .. => true
  | _ => false

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Indicates whether an addressing mode is pre-indexed with writeback (`[Xn, #imm]!`). -/
def AArch64AddrMode.isPreIndexed (mode : AArch64AddrMode) : Bool :=
  match mode with
  | .preIndex .. => true
  | _ => false

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Indicates whether an addressing mode is post-indexed with writeback (`[Xn], #imm`). -/
def AArch64AddrMode.isPostIndexed (mode : AArch64AddrMode) : Bool :=
  match mode with
  | .postIndex .. => true
  | _ => false

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Retrieves the base register of an addressing mode, if one is specified. -/
def AArch64AddrMode.baseRegister (mode : AArch64AddrMode) : Option Reg64 :=
  match mode with
  | .immOffset base _ | .preIndex base _ | .postIndex base _ | .regOffset base _ _ => some base
  | .literal _ => none

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Retrieves the offset register of an addressing mode, if one is specified. -/
def AArch64AddrMode.offsetRegister (mode : AArch64AddrMode) : Option Reg64 :=
  match mode with
  | .regOffset _ off _ => some off
  | _ => none

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Retrieves the immediate value of an addressing mode, if one is specified. -/
def AArch64AddrMode.immediate (mode : AArch64AddrMode) : Option Int64 :=
  match mode with
  | .immOffset _ imm | .preIndex _ imm | .postIndex _ imm | .literal imm => some imm
  | .regOffset .. => none

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Declarative memory access descriptor: specifies operation kind, access width, and addressing mode. -/
structure AArch64MemAccessSpec where
  kind  : MemAccessKind
  width : MemWidth
  mode  : AArch64AddrMode
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Evaluates all byte addresses accessed by a memory access specification. -/
def AArch64MemAccessSpec.addresses (spec : AArch64MemAccessSpec) (getReg : Reg64 → UInt64) (pc : Address) : List Address :=
  let base := effectiveAddress spec.mode getReg pc
  (List.range spec.width.bytes).map (fun k => base + k.toUInt64)

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Computes all byte addresses touched by access specifications of a given kind. -/
def footprintFor (kind : MemAccessKind) (specs : List AArch64MemAccessSpec) (getReg : Reg64 → UInt64) (pc : Address) : List Address :=
  (specs.filter (fun spec => spec.kind == kind)).flatMap (fun spec => spec.addresses getReg pc)

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Computes the store footprint: all byte addresses permitted to be modified by an instruction. -/
def storeFootprint (specs : List AArch64MemAccessSpec) (getReg : Reg64 → UInt64) (pc : Address) : List Address :=
  footprintFor .store specs getReg pc

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Computes the load footprint: all byte addresses whose contents an instruction may depend upon. -/
def loadFootprint (specs : List AArch64MemAccessSpec) (getReg : Reg64 → UInt64) (pc : Address) : List Address :=
  footprintFor .load specs getReg pc

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Memory agreement predicate: two memory states agree on all bytes in the specified address list. -/
def agreeOn (addrs : List Address) (m1 m2 : AArch64Memory) : Prop :=
  ∀ a ∈ addrs, AArch64Mem.read .w8 a m1 = AArch64Mem.read .w8 a m2

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that immediate offset addressing produces no writeback. -/
theorem immOffset_writeback_none (base : Reg64) (imm : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    writeback (.immOffset base imm) getReg pc = none := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that register offset addressing produces no writeback. -/
theorem regOffset_writeback_none (base : Reg64) (offset : Reg64) (shift : Option (ShiftType × Nat)) (getReg : Reg64 → UInt64) (pc : Address) :
    writeback (.regOffset base offset shift) getReg pc = none := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that literal addressing produces no writeback. -/
theorem literal_writeback_none (offset : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    writeback (.literal offset) getReg pc = none := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that pre-index addressing updates the base register to the computed address. -/
theorem preIndex_writeback_some (base : Reg64) (imm : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    writeback (.preIndex base imm) getReg pc = some (base, getReg base + imm.toUInt64) := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that post-index addressing updates the base register to base + immediate. -/
theorem postIndex_writeback_some (base : Reg64) (imm : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    writeback (.postIndex base imm) getReg pc = some (base, getReg base + imm.toUInt64) := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that pre-index effective address equals base + immediate. -/
theorem preIndex_effectiveAddress (base : Reg64) (imm : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    effectiveAddress (.preIndex base imm) getReg pc = getReg base + imm.toUInt64 := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that post-index effective address equals the initial base register value. -/
theorem postIndex_effectiveAddress (base : Reg64) (imm : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    effectiveAddress (.postIndex base imm) getReg pc = getReg base := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that literal effective address equals PC + immediate. -/
theorem literal_effectiveAddress (offset : Int64) (getReg : Reg64 → UInt64) (pc : Address) :
    effectiveAddress (.literal offset) getReg pc = pc + offset.toUInt64 := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that zero shift leaves any value unchanged across all shift types. -/
theorem shiftType_apply_zero (st : ShiftType) (val : UInt64) :
    st.apply val 0 = val := by
  cases st <;> rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that UXTX extension is the identity function on 64-bit values. -/
theorem extendType_apply_uxtx (val : UInt64) :
    ExtendType.UXTX.apply val = val := rfl

/- REF: docs/TARGETS/ARM64.md#addressing-modes -/
/-- Proves that SXTX extension is the identity function on 64-bit values. -/
theorem extendType_apply_sxtx (val : UInt64) :
    ExtendType.SXTX.apply val = val := rfl

end Gasm.Targets.AArch64

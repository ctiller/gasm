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
import Gasm.Core.Arch
import Gasm.Core.CFG

namespace Gasm.Targets.AArch64

open Gasm.Core

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Architecture tag for 64-bit AArch64 (ARMv8-A / ARMv9-A little-endian). -/
structure AArch64

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- 64-bit general-purpose registers: X0 through X30, dedicated zero register XZR, and stack pointer SP. -/
inductive Reg64 where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30
  | xzr | sp
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Register constant for X0. -/
def Reg64.X0 : Reg64 := .x0

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Register constant for X30. -/
def Reg64.X30 : Reg64 := .x30

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Register constant for SP. -/
def Reg64.SP : Reg64 := .sp

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Register constant for XZR. -/
def Reg64.XZR : Reg64 := .xzr

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- 32-bit general-purpose sub-registers: w0 through w30, dedicated zero register wzr, and stack pointer wsp. -/
inductive Reg32 where
  | w0  | w1  | w2  | w3  | w4  | w5  | w6  | w7
  | w8  | w9  | w10 | w11 | w12 | w13 | w14 | w15
  | w16 | w17 | w18 | w19 | w20 | w21 | w22 | w23
  | w24 | w25 | w26 | w27 | w28 | w29 | w30
  | wzr | wsp
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Register operand supporting general register or stack pointer. -/
inductive RegOrSp where
  | reg (r : Reg64)
  | sp
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Converts RegOrSp to a Reg64. -/
def RegOrSp.toReg64 : RegOrSp → Reg64
  | .reg r => r
  | .sp => .sp

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Converts a Reg64 to RegOrSp. -/
def Reg64.toRegOrSp (r : Reg64) : RegOrSp :=
  match r with
  | .sp => .sp
  | other => .reg other

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Maps a 32-bit sub-register to its enclosing 64-bit general-purpose register. -/
def reg32To64 (r : Reg32) : Reg64 :=
  match r with
  | .w0 => .x0   | .w1 => .x1   | .w2 => .x2   | .w3 => .x3
  | .w4 => .x4   | .w5 => .x5   | .w6 => .x6   | .w7 => .x7
  | .w8 => .x8   | .w9 => .x9   | .w10 => .x10 | .w11 => .x11
  | .w12 => .x12 | .w13 => .x13 | .w14 => .x14 | .w15 => .x15
  | .w16 => .x16 | .w17 => .x17 | .w18 => .x18 | .w19 => .x19
  | .w20 => .x20 | .w21 => .x21 | .w22 => .x22 | .w23 => .x23
  | .w24 => .x24 | .w25 => .x25 | .w26 => .x26 | .w27 => .x27
  | .w28 => .x28 | .w29 => .x29 | .w30 => .x30
  | .wzr => .xzr | .wsp => .sp

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Maps a 64-bit general-purpose register to its 32-bit sub-register. -/
def reg64To32 (r : Reg64) : Reg32 :=
  match r with
  | .x0 => .w0   | .x1 => .w1   | .x2 => .w2   | .x3 => .w3
  | .x4 => .w4   | .x5 => .w5   | .x6 => .w6   | .x7 => .w7
  | .x8 => .w8   | .x9 => .w9   | .x10 => .w10 | .x11 => .w11
  | .x12 => .w12 | .x13 => .w13 | .x14 => .w14 | .x15 => .w15
  | .x16 => .w16 | .x17 => .w17 | .x18 => .w18 | .x19 => .w19
  | .x20 => .w20 | .x21 => .w21 | .x22 => .w22 | .x23 => .w23
  | .x24 => .w24 | .x25 => .w25 | .x26 => .w26 | .x27 => .w27
  | .x28 => .w28 | .x29 => .w29 | .x30 => .w30
  | .xzr => .wzr | .sp => .wsp

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Proves reg64To32 is a left inverse of reg32To64. -/
theorem reg64To32_reg32To64 (r : Reg32) : reg64To32 (reg32To64 r) = r := by
  cases r <;> rfl

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Proves reg32To64 is a left inverse of reg64To32. -/
theorem reg32To64_reg64To32 (r : Reg64) : reg32To64 (reg64To32 r) = r := by
  cases r <;> rfl

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Returns the Fin 31 register index for standard general registers x0-x30, or none for xzr and sp. -/
def regIndex (r : Reg64) : Option (Fin 31) :=
  match r with
  | .x0 => some ⟨0, by decide⟩   | .x1 => some ⟨1, by decide⟩
  | .x2 => some ⟨2, by decide⟩   | .x3 => some ⟨3, by decide⟩
  | .x4 => some ⟨4, by decide⟩   | .x5 => some ⟨5, by decide⟩
  | .x6 => some ⟨6, by decide⟩   | .x7 => some ⟨7, by decide⟩
  | .x8 => some ⟨8, by decide⟩   | .x9 => some ⟨9, by decide⟩
  | .x10 => some ⟨10, by decide⟩ | .x11 => some ⟨11, by decide⟩
  | .x12 => some ⟨12, by decide⟩ | .x13 => some ⟨13, by decide⟩
  | .x14 => some ⟨14, by decide⟩ | .x15 => some ⟨15, by decide⟩
  | .x16 => some ⟨16, by decide⟩ | .x17 => some ⟨17, by decide⟩
  | .x18 => some ⟨18, by decide⟩ | .x19 => some ⟨19, by decide⟩
  | .x20 => some ⟨20, by decide⟩ | .x21 => some ⟨21, by decide⟩
  | .x22 => some ⟨22, by decide⟩ | .x23 => some ⟨23, by decide⟩
  | .x24 => some ⟨24, by decide⟩ | .x25 => some ⟨25, by decide⟩
  | .x26 => some ⟨26, by decide⟩ | .x27 => some ⟨27, by decide⟩
  | .x28 => some ⟨28, by decide⟩ | .x29 => some ⟨29, by decide⟩
  | .x30 => some ⟨30, by decide⟩
  | .xzr => none
  | .sp => none

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Returns the Fin 31 register index for standard sub-registers w0-w30, or none for wzr and wsp. -/
def reg32Index (r : Reg32) : Option (Fin 31) :=
  regIndex (reg32To64 r)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Constructs a 64-bit general-purpose register from a Fin 31 index (0 to 30). -/
def reg64OfFin31 (i : Fin 31) : Reg64 :=
  match i.val with
  | 0 => .x0   | 1 => .x1   | 2 => .x2   | 3 => .x3
  | 4 => .x4   | 5 => .x5   | 6 => .x6   | 7 => .x7
  | 8 => .x8   | 9 => .x9   | 10 => .x10 | 11 => .x11
  | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15
  | 16 => .x16 | 17 => .x17 | 18 => .x18 | 19 => .x19
  | 20 => .x20 | 21 => .x21 | 22 => .x22 | 23 => .x23
  | 24 => .x24 | 25 => .x25 | 26 => .x26 | 27 => .x27
  | 28 => .x28 | 29 => .x29 | _ => .x30

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Constructs a 32-bit sub-register from a Fin 31 index (0 to 30). -/
def reg32OfFin31 (i : Fin 31) : Reg32 :=
  reg64To32 (reg64OfFin31 i)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: regIndex inverses reg64OfFin31. -/
theorem regIndex_reg64OfFin31 (i : Fin 31) : regIndex (reg64OfFin31 i) = some i := by
  match i with
  | ⟨0, _⟩ => rfl  | ⟨1, _⟩ => rfl  | ⟨2, _⟩ => rfl  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl  | ⟨5, _⟩ => rfl  | ⟨6, _⟩ => rfl  | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl  | ⟨9, _⟩ => rfl  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl
  | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl | ⟨15, _⟩ => rfl
  | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl
  | ⟨24, _⟩ => rfl | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨28, _⟩ => rfl | ⟨29, _⟩ => rfl | ⟨30, _⟩ => rfl
  | ⟨n+31, h⟩ => omega

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: reg32Index inverses reg32OfFin31. -/
theorem reg32Index_reg32OfFin31 (i : Fin 31) : reg32Index (reg32OfFin31 i) = some i := by
  unfold reg32Index reg32OfFin31
  rw [reg32To64_reg64To32]
  exact regIndex_reg64OfFin31 i

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: reg64OfFin31 inverses regIndex. -/
theorem reg64OfFin31_regIndex (r : Reg64) (i : Fin 31) (h : regIndex r = some i) : reg64OfFin31 i = r := by
  revert i h
  cases r <;> intro i h
  all_goals
    first
    | contradiction
    | (injection h with h'; subst h'; rfl)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: reg32OfFin31 inverses reg32Index. -/
theorem reg32OfFin31_reg32Index (r : Reg32) (i : Fin 31) (h : reg32Index r = some i) : reg32OfFin31 i = r := by
  have h64 : reg64OfFin31 i = reg32To64 r := reg64OfFin31_regIndex (reg32To64 r) i h
  unfold reg32OfFin31
  rw [h64]
  exact reg64To32_reg32To64 r

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Returns the standard 5-bit instruction encoding code (0 to 31) for a 64-bit register. -/
def Reg64.code (r : Reg64) : UInt8 :=
  match r with
  | .x0 => 0   | .x1 => 1   | .x2 => 2   | .x3 => 3
  | .x4 => 4   | .x5 => 5   | .x6 => 6   | .x7 => 7
  | .x8 => 8   | .x9 => 9   | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19
  | .x20 => 20 | .x21 => 21 | .x22 => 22 | .x23 => 23
  | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27
  | .x28 => 28 | .x29 => 29 | .x30 => 30
  | .xzr => 31 | .sp => 31

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Returns the standard 5-bit instruction encoding code (0 to 31) for a 32-bit register. -/
def Reg32.code (r : Reg32) : UInt8 :=
  (reg32To64 r).code

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Decodes a 5-bit register code in a data-processing / arithmetic context (code 31 is xzr). -/
def decodeReg64Data (code : UInt8) : Reg64 :=
  match code &&& 0x1F with
  | 0 => .x0   | 1 => .x1   | 2 => .x2   | 3 => .x3
  | 4 => .x4   | 5 => .x5   | 6 => .x6   | 7 => .x7
  | 8 => .x8   | 9 => .x9   | 10 => .x10 | 11 => .x11
  | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15
  | 16 => .x16 | 17 => .x17 | 18 => .x18 | 19 => .x19
  | 20 => .x20 | 21 => .x21 | 22 => .x22 | 23 => .x23
  | 24 => .x24 | 25 => .x25 | 26 => .x26 | 27 => .x27
  | 28 => .x28 | 29 => .x29 | 30 => .x30
  | _ => .xzr

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Decodes a 5-bit register code in a stack pointer / load-store base context (code 31 is sp). -/
def decodeReg64Sp (code : UInt8) : Reg64 :=
  match code &&& 0x1F with
  | 0 => .x0   | 1 => .x1   | 2 => .x2   | 3 => .x3
  | 4 => .x4   | 5 => .x5   | 6 => .x6   | 7 => .x7
  | 8 => .x8   | 9 => .x9   | 10 => .x10 | 11 => .x11
  | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15
  | 16 => .x16 | 17 => .x17 | 18 => .x18 | 19 => .x19
  | 20 => .x20 | 21 => .x21 | 22 => .x22 | 23 => .x23
  | 24 => .x24 | 25 => .x25 | 26 => .x26 | 27 => .x27
  | 28 => .x28 | 29 => .x29 | 30 => .x30
  | _ => .sp

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Decodes a 5-bit register code in a 32-bit data context (code 31 is wzr). -/
def decodeReg32Data (code : UInt8) : Reg32 :=
  reg64To32 (decodeReg64Data code)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Decodes a 5-bit register code in a 32-bit stack context (code 31 is wsp). -/
def decodeReg32Sp (code : UInt8) : Reg32 :=
  reg64To32 (decodeReg64Sp code)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: decodeReg64Data inverts Reg64.code for all registers other than sp. -/
theorem decodeReg64Data_code (r : Reg64) (h : r ≠ .sp) : decodeReg64Data (r.code) = r := by
  cases r <;> try rfl
  contradiction

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: decodeReg64Sp inverts Reg64.code for all registers other than xzr. -/
theorem decodeReg64Sp_code (r : Reg64) (h : r ≠ .xzr) : decodeReg64Sp (r.code) = r := by
  cases r <;> try rfl
  contradiction

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: decodeReg32Data inverts Reg32.code for all registers other than wsp. -/
theorem decodeReg32Data_code (r : Reg32) (h : r ≠ .wsp) : decodeReg32Data (r.code) = r := by
  unfold decodeReg32Data Reg32.code
  have h64 : reg32To64 r ≠ .sp := by
    intro h_sp
    cases r <;> try contradiction
  have h_dec := decodeReg64Data_code (reg32To64 r) h64
  rw [h_dec]
  exact reg64To32_reg32To64 r

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: decodeReg32Sp inverts Reg32.code for all registers other than wzr. -/
theorem decodeReg32Sp_code (r : Reg32) (h : r ≠ .wzr) : decodeReg32Sp (r.code) = r := by
  unfold decodeReg32Sp Reg32.code
  have h64 : reg32To64 r ≠ .xzr := by
    intro h_xzr
    cases r <;> try contradiction
  have h_dec := decodeReg64Sp_code (reg32To64 r) h64
  rw [h_dec]
  exact reg64To32_reg32To64 r

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Zero-extends a 32-bit unsigned integer to a 64-bit unsigned integer according to AArch64 hardware semantics. -/
def zeroExtend32 (val : UInt32) : UInt64 :=
  val.toUInt64

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Theorem characterizing 32-bit zero-extension. -/
theorem zeroExtend32_spec (val : UInt32) : zeroExtend32 val = val.toUInt64 := rfl

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Negative condition flag mask (bit 31 of PSTATE.NZCV). -/
def nzcvNMask : UInt32 := 0x80000000

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Zero condition flag mask (bit 30 of PSTATE.NZCV). -/
def nzcvZMask : UInt32 := 0x40000000

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Carry condition flag mask (bit 29 of PSTATE.NZCV). -/
def nzcvCMask : UInt32 := 0x20000000

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Overflow condition flag mask (bit 28 of PSTATE.NZCV). -/
def nzcvVMask : UInt32 := 0x10000000

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Combined condition flags mask for bits 31:28 of PSTATE.NZCV. -/
def nzcvAllMask : UInt32 := 0xF0000000

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Architectural condition flags (N: Negative, Z: Zero, C: Carry, V: Overflow). -/
structure NZCV where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Packs NZCV flags into bits 31:28 of a UInt32 word. -/
def NZCV.toUInt32 (nzcv : NZCV) : UInt32 :=
  (if nzcv.n then nzcvNMask else 0) |||
  (if nzcv.z then nzcvZMask else 0) |||
  (if nzcv.c then nzcvCMask else 0) |||
  (if nzcv.v then nzcvVMask else 0)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Unpacks NZCV flags from bits 31:28 of a UInt32 word. -/
def NZCV.ofUInt32 (val : UInt32) : NZCV :=
  { n := (val &&& nzcvNMask) != 0
  , z := (val &&& nzcvZMask) != 0
  , c := (val &&& nzcvCMask) != 0
  , v := (val &&& nzcvVMask) != 0 }

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: ofUInt32 inverts toUInt32. -/
theorem NZCV.ofUInt32_toUInt32 (nzcv : NZCV) : NZCV.ofUInt32 (NZCV.toUInt32 nzcv) = nzcv := by
  cases nzcv with | mk n z c v =>
  cases n <;> cases z <;> cases c <;> cases v <;> decide

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Condition codes tested by conditional branches and select instructions. -/
inductive Cond where
  | EQ | NE | CS | CC | MI | PL | VS | VC
  | HI | LS | GE | LT | GT | LE | AL | NV
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Returns the 4-bit condition code field (0 to 15) for a condition. -/
def Cond.code (c : Cond) : UInt8 :=
  match c with
  | .EQ => 0  | .NE => 1  | .CS => 2  | .CC => 3
  | .MI => 4  | .PL => 5  | .VS => 6  | .VC => 7
  | .HI => 8  | .LS => 9  | .GE => 10 | .LT => 11
  | .GT => 12 | .LE => 13 | .AL => 14 | .NV => 15

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Decodes a 4-bit condition code into a Cond value. -/
def Cond.ofCode (code : UInt8) : Cond :=
  match code &&& 0xF with
  | 0  => .EQ  | 1  => .NE  | 2  => .CS  | 3  => .CC
  | 4  => .MI  | 5  => .PL  | 6  => .VS  | 7  => .VC
  | 8  => .HI  | 9  => .LS  | 10 => .GE  | 11 => .LT
  | 12 => .GT  | 13 => .LE  | 14 => .AL  | _  => .NV

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Round-trip theorem: ofCode inverts Cond.code. -/
theorem Cond.ofCode_code (c : Cond) : Cond.ofCode (c.code) = c := by
  cases c <;> decide

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Evaluates a condition code against the NZCV condition flags. -/
def evalCond (cond : Cond) (nzcv : NZCV) : Bool :=
  match cond with
  | .EQ => nzcv.z
  | .NE => !nzcv.z
  | .CS => nzcv.c
  | .CC => !nzcv.c
  | .MI => nzcv.n
  | .PL => !nzcv.n
  | .VS => nzcv.v
  | .VC => !nzcv.v
  | .HI => nzcv.c && !nzcv.z
  | .LS => !(nzcv.c && !nzcv.z)
  | .GE => nzcv.n == nzcv.v
  | .LT => nzcv.n != nzcv.v
  | .GT => !nzcv.z && (nzcv.n == nzcv.v)
  | .LE => !(!nzcv.z && (nzcv.n == nzcv.v))
  | .AL => true
  | .NV => true

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Evaluates a condition code directly against raw UInt32 NZCV flag bits. -/
def evalCondUInt32 (cond : Cond) (nzcvBits : UInt32) : Bool :=
  evalCond cond (NZCV.ofUInt32 nzcvBits)

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Equivalence between evalCond and evalCondUInt32 over packed flags. -/
theorem evalCondUInt32_eq (cond : Cond) (nzcv : NZCV) :
    evalCondUInt32 cond (NZCV.toUInt32 nzcv) = evalCond cond nzcv := by
  unfold evalCondUInt32
  rw [NZCV.ofUInt32_toUInt32]

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Inverts a condition code to its opposite condition. -/
def Cond.invert (c : Cond) : Cond :=
  match c with
  | .EQ => .NE | .NE => .EQ
  | .CS => .CC | .CC => .CS
  | .MI => .PL | .PL => .MI
  | .VS => .VC | .VC => .VS
  | .HI => .LS | .LS => .HI
  | .GE => .LT | .LT => .GE
  | .GT => .LE | .LE => .GT
  | .AL => .NV | .NV => .AL

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Double inversion is the identity on condition codes. -/
theorem Cond.invert_invert (c : Cond) : Cond.invert (Cond.invert c) = c := by
  cases c <;> decide

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Formats a 64-bit general-purpose register into lowercase text. -/
def Reg64.toString : Reg64 → String
  | .x0  => "x0"  | .x1  => "x1"  | .x2  => "x2"  | .x3  => "x3"
  | .x4  => "x4"  | .x5  => "x5"  | .x6  => "x6"  | .x7  => "x7"
  | .x8  => "x8"  | .x9  => "x9"  | .x10 => "x10" | .x11 => "x11"
  | .x12 => "x12" | .x13 => "x13" | .x14 => "x14" | .x15 => "x15"
  | .x16 => "x16" | .x17 => "x17" | .x18 => "x18" | .x19 => "x19"
  | .x20 => "x20" | .x21 => "x21" | .x22 => "x22" | .x23 => "x23"
  | .x24 => "x24" | .x25 => "x25" | .x26 => "x26" | .x27 => "x27"
  | .x28 => "x28" | .x29 => "x29" | .x30 => "x30"
  | .xzr => "xzr" | .sp  => "sp"

/- REF: docs/TARGETS/ARM64.md#registers -/
instance : ToString Reg64 where
  toString := Reg64.toString

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Formats a 32-bit sub-register into lowercase text. -/
def Reg32.toString : Reg32 → String
  | .w0  => "w0"  | .w1  => "w1"  | .w2  => "w2"  | .w3  => "w3"
  | .w4  => "w4"  | .w5  => "w5"  | .w6  => "w6"  | .w7  => "w7"
  | .w8  => "w8"  | .w9  => "w9"  | .w10 => "w10" | .w11 => "w11"
  | .w12 => "w12" | .w13 => "w13" | .w14 => "w14" | .w15 => "w15"
  | .w16 => "w16" | .w17 => "w17" | .w18 => "w18" | .w19 => "w19"
  | .w20 => "w20" | .w21 => "w21" | .w22 => "w22" | .w23 => "w23"
  | .w24 => "w24" | .w25 => "w25" | .w26 => "w26" | .w27 => "w27"
  | .w28 => "w28" | .w29 => "w29" | .w30 => "w30"
  | .wzr => "wzr" | .wsp => "wsp"

/- REF: docs/TARGETS/ARM64.md#registers -/
instance : ToString Reg32 where
  toString := Reg32.toString

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Formats a RegOrSp into lowercase text. -/
def RegOrSp.toString : RegOrSp → String
  | .reg r => r.toString
  | .sp => "sp"

/- REF: docs/TARGETS/ARM64.md#registers -/
instance : ToString RegOrSp where
  toString := RegOrSp.toString

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Formats a condition code into lowercase mnemonic text. -/
def Cond.toString : Cond → String
  | .EQ => "eq" | .NE => "ne" | .CS => "cs" | .CC => "cc"
  | .MI => "mi" | .PL => "pl" | .VS => "vs" | .VC => "vc"
  | .HI => "hi" | .LS => "ls" | .GE => "ge" | .LT => "lt"
  | .GT => "gt" | .LE => "le" | .AL => "al" | .NV => "nv"

/- REF: docs/TARGETS/ARM64.md#registers -/
instance : ToString Cond where
  toString := Cond.toString

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Formats NZCV flags into a readable status string. -/
def NZCV.toString (nzcv : NZCV) : String :=
  s!"N:{if nzcv.n then 1 else 0} Z:{if nzcv.z then 1 else 0} C:{if nzcv.c then 1 else 0} V:{if nzcv.v then 1 else 0}"

/- REF: docs/TARGETS/ARM64.md#registers -/
instance : ToString NZCV where
  toString := NZCV.toString

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- AAPCS64 standard argument / return value registers x0-x7. -/
def aapcs64ArgRegs : List Reg64 :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- AAPCS64 standard callee-saved general registers x19-x28. -/
def aapcs64CalleeSavedRegs : List Reg64 :=
  [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- AAPCS64 Frame Pointer register x29. -/
def fp : Reg64 := .x29

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- AAPCS64 Link Register x30 (target of BL/BLR). -/
def lr : Reg64 := .x30

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Intra-procedure call temporary register 0 (x16). -/
def ip0 : Reg64 := .x16

/- REF: docs/TARGETS/ARM64.md#registers -/
/-- Intra-procedure call temporary register 1 (x17). -/
def ip1 : Reg64 := .x17

end Gasm.Targets.AArch64

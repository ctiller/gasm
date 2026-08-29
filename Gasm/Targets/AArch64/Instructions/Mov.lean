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
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.Machine
import Gasm.Targets.AArch64.Uop
import Gasm.Targets.AArch64.Instructions.Base

namespace Gasm.Targets.AArch64.Instructions

open Gasm.Core
open Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
/-- MOV (register): Copies general-purpose register operand into destination register. -/
structure MovReg where
  is64 : Bool
  rd   : Reg64
  rm   : Reg64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
instance : AArch64Instruction MovReg where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (1 : UInt32) <<< 29
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let rnCode := (.xzr : Reg64).code.toUInt32 <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x0A : UInt32) <<< 24) ||| rmCode ||| rnCode ||| rdCode

  step i s :=
    if i.is64 then
      s.setReg64 i.rd (s.getReg64 i.rm) |>.advancePc
    else
      s.setReg64 i.rd (s.getReg64 i.rm &&& 0xFFFFFFFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "MOV_REG", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    s!"mov {formatReg i.is64 i.rd}, {formatReg i.is64 i.rm}"

  roundtripCases := [
    { is64 := true, rd := .x0, rm := .x1 },
    { is64 := false, rd := .x2, rm := .x3 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
/-- MOVZ: Move wide with zero. -/
structure Movz where
  is64  : Bool
  rd    : Reg64
  imm   : UInt16
  shift : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
instance : AArch64Instruction Movz where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (2 : UInt32) <<< 29
    let hw := (i.shift.toUInt32 &&& 3) <<< 21
    let imm16 := (i.imm.toUInt32 &&& 0xFFFF) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x25 : UInt32) <<< 23) ||| hw ||| imm16 ||| rdCode

  step i s :=
    let shiftBits : UInt64 := (i.shift.toUInt64 &&& 3) * 16
    let val := (i.imm.toUInt64) <<< shiftBits
    if i.is64 then
      s.setReg64 i.rd val |>.advancePc
    else
      s.setReg64 i.rd (val &&& 0xFFFFFFFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "MOVZ", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.shift == 0 then "" else s!", lsl #{i.shift.toNat * 16}"
    s!"movz {formatReg i.is64 i.rd}, #{i.imm}{sh}"

  roundtripCases := [
    { is64 := true, rd := .x0, imm := 42, shift := 0 },
    { is64 := false, rd := .x1, imm := 100, shift := 0 },
    { is64 := true, rd := .x2, imm := 0x0900, shift := 1 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
/-- MOVN: Move wide with NOT. -/
structure Movn where
  is64  : Bool
  rd    : Reg64
  imm   : UInt16
  shift : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
instance : AArch64Instruction Movn where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let hw := (i.shift.toUInt32 &&& 3) <<< 21
    let imm16 := (i.imm.toUInt32 &&& 0xFFFF) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| ((0x25 : UInt32) <<< 23) ||| hw ||| imm16 ||| rdCode

  step i s :=
    let shiftBits : UInt64 := (i.shift.toUInt64 &&& 3) * 16
    let val := ~~~((i.imm.toUInt64) <<< shiftBits)
    if i.is64 then
      s.setReg64 i.rd val |>.advancePc
    else
      s.setReg64 i.rd (val &&& 0xFFFFFFFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "MOVN", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.shift == 0 then "" else s!", lsl #{i.shift.toNat * 16}"
    s!"movn {formatReg i.is64 i.rd}, #{i.imm}{sh}"

  roundtripCases := [
    { is64 := true, rd := .x3, imm := 1, shift := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
/-- MOVK: Move wide with keep. -/
structure Movk where
  is64  : Bool
  rd    : Reg64
  imm   : UInt16
  shift : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
instance : AArch64Instruction Movk where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (3 : UInt32) <<< 29
    let hw := (i.shift.toUInt32 &&& 3) <<< 21
    let imm16 := (i.imm.toUInt32 &&& 0xFFFF) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x25 : UInt32) <<< 23) ||| hw ||| imm16 ||| rdCode

  step i s :=
    let shiftBits : UInt64 := (i.shift.toUInt64 &&& 3) * 16
    let mask := ~~~((0xFFFF : UInt64) <<< shiftBits)
    let insertVal := (i.imm.toUInt64) <<< shiftBits
    let cur := s.getReg64 i.rd
    let res := (cur &&& mask) ||| insertVal
    if i.is64 then
      s.setReg64 i.rd res |>.advancePc
    else
      s.setReg64 i.rd (res &&& 0xFFFFFFFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "MOVK", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rd], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.shift == 0 then "" else s!", lsl #{i.shift.toNat * 16}"
    s!"movk {formatReg i.is64 i.rd}, #{i.imm}{sh}"

  roundtripCases := [
    { is64 := true, rd := .x4, imm := 0x1234, shift := 1 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
/-- All roundtrip test cases for the MoveWide instruction family. -/
def moveWideFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := Movz)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Movn)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Movk)).map AnyAArch64Instruction.mk

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
/-- All roundtrip test cases for the MOV instruction family (including register and wide moves). -/
def movFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := MovReg)).map AnyAArch64Instruction.mk ++
  moveWideFamilyCases

-- Smart constructors

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
def movReg64 (rd rm : Reg64) : MovReg :=
  { is64 := true, rd := rd, rm := rm }

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
def movReg32 (rd rm : Reg32) : MovReg :=
  { is64 := false, rd := reg32To64 rd, rm := reg32To64 rm }

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
def movz64 (rd : Reg64) (imm : UInt16) (shift : UInt8 := 0) : Movz :=
  { is64 := true, rd := rd, imm := imm, shift := shift }

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
def movz32 (rd : Reg32) (imm : UInt16) (shift : UInt8 := 0) : Movz :=
  { is64 := false, rd := reg32To64 rd, imm := imm, shift := shift }

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
def movk64 (rd : Reg64) (imm : UInt16) (shift : UInt8 := 0) : Movk :=
  { is64 := true, rd := rd, imm := imm, shift := shift }

/- REF: docs/TARGETS/ARM64.md#6-movewide-family -/
def movk32 (rd : Reg32) (imm : UInt16) (shift : UInt8 := 0) : Movk :=
  { is64 := false, rd := reg32To64 rd, imm := imm, shift := shift }

end Gasm.Targets.AArch64.Instructions

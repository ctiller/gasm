/-
Copyright 2026 Google LLC

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

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
/-- SUB/SUBS/CMP (immediate): Subtracts an immediate value from a register, optionally updating condition flags. -/
structure SubImm where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  imm      : UInt64
  shift12  : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
instance : AArch64Instruction SubImm where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let op : UInt32 := (1 : UInt32) <<< 30
    let s  : UInt32 := if i.setFlags then (1 : UInt32) <<< 29 else 0
    let sh : UInt32 := if i.shift12 then (1 : UInt32) <<< 22 else 0
    let imm12 := (i.imm.toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| op ||| s ||| ((0x11 : UInt32) <<< 24) ||| sh ||| imm12 ||| rnCode ||| rdCode

  step i s :=
    let val := if i.shift12 then i.imm <<< 12 else i.imm
    if i.is64 then
      let a := s.getReg64 i.rn
      let res := a - val
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsSub64 a val else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := val.toUInt32
      let res := a - b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsSub32 a b else s'
      s''.advancePc

  toUops i :=
    [{ mnemonic := "SUB_IMM", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rn], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.shift12 then ", lsl #12" else ""
    if i.setFlags && i.rd == .xzr then
      s!"cmp {formatReg i.is64 i.rn}, #{i.imm}{sh}"
    else
      let op := if i.setFlags then "subs" else "sub"
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, #{i.imm}{sh}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, imm := 16, shift12 := false },
    { is64 := false, setFlags := false, rd := .x2, rn := .x3, imm := 100, shift12 := false },
    { is64 := true, setFlags := true, rd := .xzr, rn := .x4, imm := 32, shift12 := false },
    { is64 := false, setFlags := true, rd := .xzr, rn := .x5, imm := 8, shift12 := false }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
/-- SUB/SUBS/CMP (shifted register): Subtracts a shifted register value from a register, optionally updating condition flags. -/
structure SubReg where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  rm       : Reg64
  shift    : ShiftType := .LSL
  amount   : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
instance : AArch64Instruction SubReg where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let op : UInt32 := (1 : UInt32) <<< 30
    let s  : UInt32 := if i.setFlags then (1 : UInt32) <<< 29 else 0
    let sh := shiftTypeCode i.shift <<< 22
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let imm6 := (i.amount.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| op ||| s ||| ((0x0B : UInt32) <<< 24) ||| sh ||| rmCode ||| imm6 ||| rnCode ||| rdCode

  step i s :=
    if i.is64 then
      let a := s.getReg64 i.rn
      let b := i.shift.apply (s.getReg64 i.rm) i.amount.toNat
      let res := a - b
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsSub64 a b else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := (i.shift.apply (s.getReg64 i.rm) i.amount.toNat).toUInt32
      let res := a - b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsSub32 a b else s'
      s''.advancePc

  toUops i :=
    let isShifted := i.amount > 0 || i.shift != .LSL
    let slots := if isShifted then [.slot1] else [.slot0, .slot1]
    let lat := if isShifted then 2 else 1
    [{ mnemonic := "SUB_REG", uopClass := if isShifted then .intShift else .intALU, eligibleSlots := slots, latencyCycles := lat, reciprocalThroughput := if isShifted then 1.0 else 0.5, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.amount == 0 then "" else s!", {i.shift} #{i.amount}"
    if i.setFlags && i.rd == .xzr then
      s!"cmp {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"
    else
      let op := if i.setFlags then "subs" else "sub"
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, rm := .x2, shift := .LSL, amount := 0 },
    { is64 := true, setFlags := true, rd := .xzr, rn := .x1, rm := .x2, shift := .LSL, amount := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
/-- SUB/SUBS/CMP (extended register): Subtracts an extended register value from a register, optionally updating condition flags. -/
structure SubExt where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  rm       : Reg64
  ext      : ExtendType := .UXTX
  amount   : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
instance : AArch64Instruction SubExt where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let op : UInt32 := (1 : UInt32) <<< 30
    let s  : UInt32 := if i.setFlags then (1 : UInt32) <<< 29 else 0
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let opt := extendTypeCode i.ext <<< 13
    let imm3 := (i.amount.toUInt32 &&& 7) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| op ||| s ||| ((0x0B : UInt32) <<< 24) ||| ((1 : UInt32) <<< 21) ||| rmCode ||| opt ||| imm3 ||| rnCode ||| rdCode

  step i s :=
    let extended := (i.ext.apply (s.getReg64 i.rm)) <<< i.amount.toNat.toUInt64
    if i.is64 then
      let a := s.getReg64 i.rn
      let res := a - extended
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsSub64 a extended else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := extended.toUInt32
      let res := a - b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsSub32 a b else s'
      s''.advancePc

  toUops i :=
    [{ mnemonic := "SUB_EXT", uopClass := .intALU, eligibleSlots := [.slot1], latencyCycles := 2, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let opt := if i.amount == 0 then s!", {i.ext}" else s!", {i.ext} #{i.amount}"
    let op := if i.setFlags then "subs" else "sub"
    s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg false i.rm}{opt}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, rm := .x2, ext := .UXTX, amount := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
/-- All roundtrip test cases for the SUB instruction family. -/
def subFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := SubImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := SubReg)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := SubExt)).map AnyAArch64Instruction.mk

-- Smart constructors

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def subImm64 (rd rn : Reg64) (imm : UInt64) (shift12 : Bool := false) : SubImm :=
  { is64 := true, setFlags := false, rd := rd, rn := rn, imm := imm, shift12 := shift12 }

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def subImm32 (rd rn : Reg32) (imm : UInt64) (shift12 : Bool := false) : SubImm :=
  { is64 := false, setFlags := false, rd := reg32To64 rd, rn := reg32To64 rn, imm := imm, shift12 := shift12 }

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def cmpImm64 (rn : Reg64) (imm : UInt64) (shift12 : Bool := false) : SubImm :=
  { is64 := true, setFlags := true, rd := .xzr, rn := rn, imm := imm, shift12 := shift12 }

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def cmpImm32 (rn : Reg32) (imm : UInt64) (shift12 : Bool := false) : SubImm :=
  { is64 := false, setFlags := true, rd := .xzr, rn := reg32To64 rn, imm := imm, shift12 := shift12 }

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def subReg64 (rd rn rm : Reg64) (shift : ShiftType := .LSL) (amount : UInt8 := 0) : SubReg :=
  { is64 := true, setFlags := false, rd := rd, rn := rn, rm := rm, shift := shift, amount := amount }

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def subReg32 (rd rn rm : Reg32) (shift : ShiftType := .LSL) (amount : UInt8 := 0) : SubReg :=
  { is64 := false, setFlags := false, rd := reg32To64 rd, rn := reg32To64 rn, rm := reg32To64 rm, shift := shift, amount := amount }

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def cmpReg64 (rn rm : Reg64) (shift : ShiftType := .LSL) (amount : UInt8 := 0) : SubReg :=
  { is64 := true, setFlags := true, rd := .xzr, rn := rn, rm := rm, shift := shift, amount := amount }

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def cmpReg32 (rn rm : Reg32) (shift : ShiftType := .LSL) (amount : UInt8 := 0) : SubReg :=
  { is64 := false, setFlags := true, rd := .xzr, rn := reg32To64 rn, rm := reg32To64 rm, shift := shift, amount := amount }

end Gasm.Targets.AArch64.Instructions

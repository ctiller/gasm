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

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
/-- ADD/ADDS/CMN (immediate): Adds an immediate value to a register, optionally updating condition flags. -/
structure AddImm where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  imm      : UInt64
  shift12  : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
instance : AArch64Instruction AddImm where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let s  : UInt32 := if i.setFlags then (1 : UInt32) <<< 29 else 0
    let sh : UInt32 := if i.shift12 then (1 : UInt32) <<< 22 else 0
    let imm12 := (i.imm.toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| s ||| ((0x11 : UInt32) <<< 24) ||| sh ||| imm12 ||| rnCode ||| rdCode

  step i s :=
    let val := if i.shift12 then i.imm <<< 12 else i.imm
    if i.is64 then
      let a := s.getReg64 i.rn
      let res := a + val
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsAdd64 a val else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := val.toUInt32
      let res := a + b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsAdd32 a b else s'
      s''.advancePc

  toUops i :=
    [{ mnemonic := "ADD_IMM", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rn], dstRegs := [i.rd] }]

  toAssembly i :=
    let op := if i.setFlags then (if i.rd == .xzr then "cmn" else "adds") else "add"
    let sh := if i.shift12 then ", lsl #12" else ""
    if i.setFlags && i.rd == .xzr then
      s!"cmn {formatReg i.is64 i.rn}, #{i.imm}{sh}"
    else
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, #{i.imm}{sh}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, imm := 16, shift12 := false },
    { is64 := false, setFlags := false, rd := .x2, rn := .x3, imm := 100, shift12 := false },
    { is64 := true, setFlags := true, rd := .x4, rn := .x5, imm := 0, shift12 := true }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
/-- ADD/ADDS/CMN (shifted register): Adds a shifted register value to a register, optionally updating condition flags. -/
structure AddReg where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  rm       : Reg64
  shift    : ShiftType := .LSL
  amount   : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
instance : AArch64Instruction AddReg where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let s  : UInt32 := if i.setFlags then (1 : UInt32) <<< 29 else 0
    let sh := shiftTypeCode i.shift <<< 22
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let imm6 := (i.amount.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| s ||| ((0x0B : UInt32) <<< 24) ||| sh ||| rmCode ||| imm6 ||| rnCode ||| rdCode

  step i s :=
    if i.is64 then
      let a := s.getReg64 i.rn
      let b := i.shift.apply (s.getReg64 i.rm) i.amount.toNat
      let res := a + b
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsAdd64 a b else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := (i.shift.apply (s.getReg64 i.rm) i.amount.toNat).toUInt32
      let res := a + b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsAdd32 a b else s'
      s''.advancePc

  toUops i :=
    let isShifted := i.amount > 0 || i.shift != .LSL
    let slots := if isShifted then [.slot1] else [.slot0, .slot1]
    let lat := if isShifted then 2 else 1
    [{ mnemonic := "ADD_REG", uopClass := if isShifted then .intShift else .intALU, eligibleSlots := slots, latencyCycles := lat, reciprocalThroughput := if isShifted then 1.0 else 0.5, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.amount == 0 then "" else s!", {i.shift} #{i.amount}"
    if i.setFlags && i.rd == .xzr then
      s!"cmn {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"
    else
      let op := if i.setFlags then "adds" else "add"
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, rm := .x2, shift := .LSL, amount := 0 },
    { is64 := false, setFlags := false, rd := .x3, rn := .x4, rm := .x5, shift := .LSR, amount := 2 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
/-- ADD/ADDS/CMN (extended register): Adds an extended register value to a register, optionally updating condition flags. -/
structure AddExt where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  rm       : Reg64
  ext      : ExtendType := .UXTX
  amount   : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
instance : AArch64Instruction AddExt where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let s  : UInt32 := if i.setFlags then (1 : UInt32) <<< 29 else 0
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let opt := extendTypeCode i.ext <<< 13
    let imm3 := (i.amount.toUInt32 &&& 7) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| s ||| ((0x0B : UInt32) <<< 24) ||| ((1 : UInt32) <<< 21) ||| rmCode ||| opt ||| imm3 ||| rnCode ||| rdCode

  step i s :=
    let extended := (i.ext.apply (s.getReg64 i.rm)) <<< i.amount.toNat.toUInt64
    if i.is64 then
      let a := s.getReg64 i.rn
      let res := a + extended
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsAdd64 a extended else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := extended.toUInt32
      let res := a + b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsAdd32 a b else s'
      s''.advancePc

  toUops i :=
    [{ mnemonic := "ADD_EXT", uopClass := .intALU, eligibleSlots := [.slot1], latencyCycles := 2, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let opt := if i.amount == 0 then s!", {i.ext}" else s!", {i.ext} #{i.amount}"
    let op := if i.setFlags then "adds" else "add"
    s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg false i.rm}{opt}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, rm := .x2, ext := .UXTX, amount := 0 },
    { is64 := false, setFlags := false, rd := .x3, rn := .x4, rm := .x5, ext := .UXTW, amount := 2 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
/-- All roundtrip test cases for the ADD instruction family. -/
def addFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := AddImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := AddReg)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := AddExt)).map AnyAArch64Instruction.mk

-- Smart constructors

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def addImm64 (rd rn : Reg64) (imm : UInt64) (shift12 : Bool := false) : AddImm :=
  { is64 := true, setFlags := false, rd := rd, rn := rn, imm := imm, shift12 := shift12 }

/- REF: docs/TARGETS/ARM64.md#1-addsubimm-family -/
def addImm32 (rd rn : Reg32) (imm : UInt64) (shift12 : Bool := false) : AddImm :=
  { is64 := false, setFlags := false, rd := reg32To64 rd, rn := reg32To64 rn, imm := imm, shift12 := shift12 }

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def addReg64 (rd rn rm : Reg64) (shift : ShiftType := .LSL) (amount : UInt8 := 0) : AddReg :=
  { is64 := true, setFlags := false, rd := rd, rn := rn, rm := rm, shift := shift, amount := amount }

/- REF: docs/TARGETS/ARM64.md#2-addsubreg-family -/
def addReg32 (rd rn rm : Reg32) (shift : ShiftType := .LSL) (amount : UInt8 := 0) : AddReg :=
  { is64 := false, setFlags := false, rd := reg32To64 rd, rn := reg32To64 rn, rm := reg32To64 rm, shift := shift, amount := amount }

end Gasm.Targets.AArch64.Instructions

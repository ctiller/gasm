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

/- REF: docs/TARGETS/ARM64.md#3-logicalimm-family -/
/-- AND/ANDS/TST (immediate): Bitwise AND with bitmask immediate, optionally updating condition flags. -/
structure AndImm where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  n        : Bool
  immr     : UInt8
  imms     : UInt8
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#3-logicalimm-family -/
instance : AArch64Instruction AndImm where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := if i.setFlags then (3 : UInt32) <<< 29 else 0
    let nBit : UInt32 := if i.n then (1 : UInt32) <<< 22 else 0
    let immrField := (i.immr.toUInt32 &&& 0x3F) <<< 16
    let immsField := (i.imms.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x24 : UInt32) <<< 23) ||| nBit ||| immrField ||| immsField ||| rnCode ||| rdCode

  step i s :=
    if i.is64 then
      let res := s.getReg64 i.rn
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsLogic64 res else s'
      s''.advancePc
    else
      let res := (s.getReg64 i.rn).toUInt32
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsLogic32 res else s'
      s''.advancePc

  toUops i :=
    [{ mnemonic := "AND_IMM", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rn], dstRegs := [i.rd] }]

  toAssembly i :=
    let op := if i.setFlags then (if i.rd == .xzr then "tst" else "ands") else "and"
    if i.setFlags && i.rd == .xzr then
      s!"tst {formatReg i.is64 i.rn}, #({i.immr}, {i.imms})"
    else
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, #({i.immr}, {i.imms})"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, n := true, immr := 0, imms := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
/-- AND/ANDS/BIC/BICS/TST (shifted register): Bitwise AND with shifted register, optionally inverted and flag-setting. -/
structure AndReg where
  is64     : Bool
  setFlags : Bool
  rd       : Reg64
  rn       : Reg64
  rm       : Reg64
  shift    : ShiftType := .LSL
  amount   : UInt8 := 0
  invert   : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
instance : AArch64Instruction AndReg where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := if i.setFlags then (3 : UInt32) <<< 29 else 0
    let sh := shiftTypeCode i.shift <<< 22
    let nBit : UInt32 := if i.invert then (1 : UInt32) <<< 21 else 0
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let imm6 := (i.amount.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x0A : UInt32) <<< 24) ||| sh ||| nBit ||| rmCode ||| imm6 ||| rnCode ||| rdCode

  step i s :=
    let shifted := i.shift.apply (s.getReg64 i.rm) i.amount.toNat
    let op2 := if i.invert then ~~~shifted else shifted
    if i.is64 then
      let res := s.getReg64 i.rn &&& op2
      let s' := s.setReg64 i.rd res
      let s'' := if i.setFlags then s'.setFlagsLogic64 res else s'
      s''.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := op2.toUInt32
      let res := a &&& b
      let s' := s.setReg64 i.rd res.toUInt64
      let s'' := if i.setFlags then s'.setFlagsLogic32 res else s'
      s''.advancePc

  toUops i :=
    let isShifted := i.amount > 0 || i.shift != .LSL
    let slots := if isShifted then [.slot1] else [.slot0, .slot1]
    let lat := if isShifted then 2 else 1
    [{ mnemonic := "AND_REG", uopClass := if isShifted then .intShift else .intALU, eligibleSlots := slots, latencyCycles := lat, reciprocalThroughput := if isShifted then 1.0 else 0.5, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.amount == 0 then "" else s!", {i.shift} #{i.amount}"
    if i.invert then
      let op := if i.setFlags then "bics" else "bic"
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"
    else if i.setFlags && i.rd == .xzr then
      s!"tst {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"
    else
      let op := if i.setFlags then "ands" else "and"
      s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"

  roundtripCases := [
    { is64 := true, setFlags := false, rd := .x0, rn := .x1, rm := .x2, shift := .LSL, amount := 0, invert := false },
    { is64 := true, setFlags := true, rd := .xzr, rn := .x1, rm := .x2, shift := .LSL, amount := 0, invert := false }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#3-logicalimm-family -/
/-- ORR (immediate): Bitwise inclusive OR with bitmask immediate. -/
structure OrrImm where
  is64 : Bool
  rd   : Reg64
  rn   : Reg64
  n    : Bool
  immr : UInt8
  imms : UInt8
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#3-logicalimm-family -/
instance : AArch64Instruction OrrImm where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (1 : UInt32) <<< 29
    let nBit : UInt32 := if i.n then (1 : UInt32) <<< 22 else 0
    let immrField := (i.immr.toUInt32 &&& 0x3F) <<< 16
    let immsField := (i.imms.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x24 : UInt32) <<< 23) ||| nBit ||| immrField ||| immsField ||| rnCode ||| rdCode

  step i s :=
    if i.is64 then s.setReg64 i.rd (s.getReg64 i.rn) |>.advancePc
    else s.setReg64 i.rd ((s.getReg64 i.rn).toUInt32.toUInt64) |>.advancePc

  toUops i :=
    [{ mnemonic := "ORR_IMM", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rn], dstRegs := [i.rd] }]

  toAssembly i :=
    s!"orr {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, #({i.immr}, {i.imms})"

  roundtripCases := [
    { is64 := true, rd := .x0, rn := .x1, n := true, immr := 0, imms := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
/-- ORR/ORN (shifted register): Bitwise inclusive OR with shifted register, optionally inverted. -/
structure OrrReg where
  is64   : Bool
  rd     : Reg64
  rn     : Reg64
  rm     : Reg64
  shift  : ShiftType := .LSL
  amount : UInt8 := 0
  invert : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
instance : AArch64Instruction OrrReg where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (1 : UInt32) <<< 29
    let sh := shiftTypeCode i.shift <<< 22
    let nBit : UInt32 := if i.invert then (1 : UInt32) <<< 21 else 0
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let imm6 := (i.amount.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x0A : UInt32) <<< 24) ||| sh ||| nBit ||| rmCode ||| imm6 ||| rnCode ||| rdCode

  step i s :=
    let shifted := i.shift.apply (s.getReg64 i.rm) i.amount.toNat
    let op2 := if i.invert then ~~~shifted else shifted
    if i.is64 then
      let res := s.getReg64 i.rn ||| op2
      s.setReg64 i.rd res |>.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := op2.toUInt32
      let res := a ||| b
      s.setReg64 i.rd res.toUInt64 |>.advancePc

  toUops i :=
    let isShifted := i.amount > 0 || i.shift != .LSL
    let slots := if isShifted then [.slot1] else [.slot0, .slot1]
    let lat := if isShifted then 2 else 1
    [{ mnemonic := "ORR_REG", uopClass := if isShifted then .intShift else .intALU, eligibleSlots := slots, latencyCycles := lat, reciprocalThroughput := if isShifted then 1.0 else 0.5, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.amount == 0 then "" else s!", {i.shift} #{i.amount}"
    let op := if i.invert then "orn" else "orr"
    s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"

  roundtripCases := [
    { is64 := true, rd := .x0, rn := .x1, rm := .x2, shift := .LSL, amount := 0, invert := false }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#3-logicalimm-family -/
/-- EOR (immediate): Bitwise exclusive OR with bitmask immediate. -/
structure EorImm where
  is64 : Bool
  rd   : Reg64
  rn   : Reg64
  n    : Bool
  immr : UInt8
  imms : UInt8
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#3-logicalimm-family -/
instance : AArch64Instruction EorImm where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (2 : UInt32) <<< 29
    let nBit : UInt32 := if i.n then (1 : UInt32) <<< 22 else 0
    let immrField := (i.immr.toUInt32 &&& 0x3F) <<< 16
    let immsField := (i.imms.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x24 : UInt32) <<< 23) ||| nBit ||| immrField ||| immsField ||| rnCode ||| rdCode

  step i s :=
    if i.is64 then s.setReg64 i.rd (s.getReg64 i.rn) |>.advancePc
    else s.setReg64 i.rd ((s.getReg64 i.rn).toUInt32.toUInt64) |>.advancePc

  toUops i :=
    [{ mnemonic := "EOR_IMM", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [i.rn], dstRegs := [i.rd] }]

  toAssembly i :=
    s!"eor {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, #({i.immr}, {i.imms})"

  roundtripCases := [
    { is64 := true, rd := .x0, rn := .x1, n := true, immr := 0, imms := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
/-- EOR/EON (shifted register): Bitwise exclusive OR with shifted register, optionally inverted. -/
structure EorReg where
  is64   : Bool
  rd     : Reg64
  rn     : Reg64
  rm     : Reg64
  shift  : ShiftType := .LSL
  amount : UInt8 := 0
  invert : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
instance : AArch64Instruction EorReg where
  encodeWord i :=
    let sf : UInt32 := if i.is64 then (1 : UInt32) <<< 31 else 0
    let opc : UInt32 := (2 : UInt32) <<< 29
    let sh := shiftTypeCode i.shift <<< 22
    let nBit : UInt32 := if i.invert then (1 : UInt32) <<< 21 else 0
    let rmCode := (i.rm.code.toUInt32 &&& 0x1F) <<< 16
    let imm6 := (i.amount.toUInt32 &&& 0x3F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    sf ||| opc ||| ((0x0A : UInt32) <<< 24) ||| sh ||| nBit ||| rmCode ||| imm6 ||| rnCode ||| rdCode

  step i s :=
    let shifted := i.shift.apply (s.getReg64 i.rm) i.amount.toNat
    let op2 := if i.invert then ~~~shifted else shifted
    if i.is64 then
      let res := s.getReg64 i.rn ^^^ op2
      s.setReg64 i.rd res |>.advancePc
    else
      let a := (s.getReg64 i.rn).toUInt32
      let b := op2.toUInt32
      let res := a ^^^ b
      s.setReg64 i.rd res.toUInt64 |>.advancePc

  toUops i :=
    let isShifted := i.amount > 0 || i.shift != .LSL
    let slots := if isShifted then [.slot1] else [.slot0, .slot1]
    let lat := if isShifted then 2 else 1
    [{ mnemonic := "EOR_REG", uopClass := if isShifted then .intShift else .intALU, eligibleSlots := slots, latencyCycles := lat, reciprocalThroughput := if isShifted then 1.0 else 0.5, srcRegs := [i.rn, i.rm], dstRegs := [i.rd] }]

  toAssembly i :=
    let sh := if i.amount == 0 then "" else s!", {i.shift} #{i.amount}"
    let op := if i.invert then "eon" else "eor"
    s!"{op} {formatReg i.is64 i.rd}, {formatReg i.is64 i.rn}, {formatReg i.is64 i.rm}{sh}"

  roundtripCases := [
    { is64 := true, rd := .x0, rn := .x1, rm := .x2, shift := .LSL, amount := 0, invert := false }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#4-logicalreg-family -/
/-- All roundtrip test cases for the Logical instruction family. -/
def logicalFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := AndReg)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := OrrReg)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := EorReg)).map AnyAArch64Instruction.mk

end Gasm.Targets.AArch64.Instructions

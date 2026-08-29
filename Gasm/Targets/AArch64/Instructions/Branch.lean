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

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
/-- B: Direct unconditional branch to PC-relative offset. -/
structure B where
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
instance : AArch64Instruction B where
  encodeWord i :=
    let imm26 := ((i.offset.toUInt64 >>> 2).toUInt32 &&& 0x3FFFFFF)
    ((0x05 : UInt32) <<< 26) ||| imm26

  step i s :=
    { s with pc := s.pc + i.offset.toUInt64 }

  toUops _ :=
    [{ mnemonic := "B", uopClass := .branch, eligibleSlots := [.slot0], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [], dstRegs := [], isBranch := true }]

  toAssembly i :=
    if i.offset.toInt == 0 then "b ."
    else s!"b #{i.offset.toInt}"

  roundtripCases := [
    { offset := 16 },
    { offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
/-- BL: Branch with link (calls subroutine, stores return address in X30). -/
structure Bl where
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
instance : AArch64Instruction Bl where
  encodeWord i :=
    let imm26 := ((i.offset.toUInt64 >>> 2).toUInt32 &&& 0x3FFFFFF)
    ((1 : UInt32) <<< 31) ||| ((0x05 : UInt32) <<< 26) ||| imm26

  step i s :=
    s.setReg64 .x30 (s.pc + 4) |>.branch (s.pc + i.offset.toUInt64)

  toUops _ :=
    [{ mnemonic := "BL", uopClass := .branch, eligibleSlots := [.slot0], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [], dstRegs := [.x30], isBranch := true }]

  toAssembly i :=
    s!"bl #{i.offset.toInt}"

  roundtripCases := [
    { offset := 32 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#12-branchcond-family -/
/-- B.cond: Conditional branch based on PSTATE flags. -/
structure BCond where
  cond   : Cond
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#12-branchcond-family -/
instance : AArch64Instruction BCond where
  encodeWord i :=
    let imm19 := ((i.offset.toUInt64 >>> 2).toUInt32 &&& 0x7FFFF) <<< 5
    let condCode := i.cond.code.toUInt32 &&& 0xF
    ((0x54 : UInt32) <<< 24) ||| imm19 ||| condCode

  step i s :=
    if evalCond i.cond s.nzcv then s.branch (s.pc + i.offset.toUInt64)
    else s.advancePc

  toUops _ :=
    [{ mnemonic := "B_COND", uopClass := .branch, eligibleSlots := [.slot0], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [], dstRegs := [], isBranch := true }]

  toAssembly i :=
    s!"b.{i.cond.toString} #{i.offset.toInt}"

  roundtripCases := [
    { cond := .EQ, offset := 0 },
    { cond := .NE, offset := 16 },
    { cond := .GE, offset := 32 },
    { cond := .LT, offset := (-16) }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#13-branchreg-family -/
/-- RET: Subroutine return to address in register (defaults to X30). -/
structure Ret where
  rn : Reg64 := .x30
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#13-branchreg-family -/
instance : AArch64Instruction Ret where
  encodeWord i :=
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    (0xD65F0000 : UInt32) ||| ((2 : UInt32) <<< 10) ||| rnCode

  step i s :=
    s.branch (s.getReg64 i.rn)

  toUops i :=
    [{ mnemonic := "RET", uopClass := .branch, eligibleSlots := [.slot0], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [], isBranch := true }]

  toAssembly i :=
    if i.rn == .x30 then "ret" else s!"ret {i.rn}"

  roundtripCases := [
    { rn := .x30 },
    { rn := .x0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
/-- ADR: Computes PC-relative address within ±1MB. -/
structure Adr where
  rd     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
instance : AArch64Instruction Adr where
  encodeWord i :=
    let imm21 := i.offset.toUInt64.toUInt32 &&& 0x1FFFFF
    let immlo := (imm21 &&& 3) <<< 29
    let immhi := ((imm21 >>> 2) &&& 0x7FFFF) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    immlo ||| ((0x10 : UInt32) <<< 24) ||| immhi ||| rdCode

  step i s :=
    s.setReg64 i.rd (s.pc + i.offset.toUInt64) |>.advancePc

  toUops i :=
    [{ mnemonic := "ADR", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [], dstRegs := [i.rd] }]

  toAssembly i :=
    s!"adr {i.rd}, #{i.offset.toInt}"

  roundtripCases := [
    { rd := .x0, offset := 16 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
/-- ADRP: Computes page-aligned PC-relative address within ±4GB. -/
structure Adrp where
  rd     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
instance : AArch64Instruction Adrp where
  encodeWord i :=
    let imm21 := (i.offset.toUInt64 >>> 12).toUInt32 &&& 0x1FFFFF
    let immlo := (imm21 &&& 3) <<< 29
    let immhi := ((imm21 >>> 2) &&& 0x7FFFF) <<< 5
    let rdCode := i.rd.code.toUInt32 &&& 0x1F
    ((1 : UInt32) <<< 31) ||| immlo ||| ((0x10 : UInt32) <<< 24) ||| immhi ||| rdCode

  step i s :=
    let base := s.pc &&& ~~~0xFFF
    s.setReg64 i.rd (base + i.offset.toUInt64) |>.advancePc

  toUops i :=
    [{ mnemonic := "ADRP", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [], dstRegs := [i.rd] }]

  toAssembly i :=
    s!"adrp {i.rd}, #{i.offset.toInt}"

  roundtripCases := [
    { rd := .x0, offset := 4096 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
/-- All roundtrip test cases for the Branch instruction family. -/
def branchFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := B)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Bl)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := BCond)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Ret)).map AnyAArch64Instruction.mk

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
/-- All roundtrip test cases for the ADR/ADRP instruction family. -/
def adrFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := Adr)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Adrp)).map AnyAArch64Instruction.mk

-- Smart constructors

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
def bInstr (offset : Int64) : B := { offset := offset }

/- REF: docs/TARGETS/ARM64.md#11-branchimm-family -/
def blInstr (offset : Int64) : Bl := { offset := offset }

/- REF: docs/TARGETS/ARM64.md#12-branchcond-family -/
def bCondInstr (cond : Cond) (offset : Int64) : BCond := { cond := cond, offset := offset }

/- REF: docs/TARGETS/ARM64.md#13-branchreg-family -/
def retInstr (rn : Reg64 := .x30) : Ret := { rn := rn }

/- REF: docs/TARGETS/ARM64.md#14-adr-family -/
def adrInstr (rd : Reg64) (offset : Int64) : Adr := { rd := rd, offset := offset }

end Gasm.Targets.AArch64.Instructions

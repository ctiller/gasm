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

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
/-- Simulated kernel syscall entry point VMA for AArch64 Linux simulation. -/
def linuxSyscallEntry : UInt64 := 0x80000000

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
structure Svc where
  imm : UInt16 := 0
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
instance : AArch64Instruction Svc where
  encodeWord i :=
    let imm16 := (i.imm.toUInt32 &&& 0xFFFF) <<< 5
    0xD4000001 ||| imm16

  step i s :=
    if i.imm == 0 then
      let nextPc := s.pc + 4
      { s with pc := linuxSyscallEntry, syscallReturnPc := nextPc }
    else
      s.advancePc

  toUops _ :=
    [{ mnemonic := "SVC", uopClass := .system, eligibleSlots := [.slot0], latencyCycles := 8, reciprocalThroughput := 8.0, srcRegs := [.x8, .x0], dstRegs := [.x0] }]

  toAssembly i :=
    s!"svc #{i.imm}"

  roundtripCases := [
    { imm := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
/-- HLT: Halting breakpoint instruction (used for ARM Semihosting calls with imm 0xF000). -/
structure Hlt where
  imm : UInt16 := 0xF000
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
instance : AArch64Instruction Hlt where
  encodeWord i :=
    let imm16 := (i.imm.toUInt32 &&& 0xFFFF) <<< 5
    0xD4400000 ||| imm16

  step i s :=
    if i.imm == 0xF000 then
      let exitCode := s.readMem .w64 (s.getReg64 .x1 + 8)
      s.terminate exitCode.toUInt32 |>.advancePc
    else
      s.setFault .permissionFault

  toUops _ :=
    [{ mnemonic := "HLT", uopClass := .system, eligibleSlots := [.slot0], latencyCycles := 8, reciprocalThroughput := 8.0, srcRegs := [.x0, .x1], dstRegs := [] }]

  toAssembly i :=
    s!"hlt #{i.imm}"

  roundtripCases := [
    { imm := 0xF000 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
/-- NOP: No-operation instruction (architecturally encoded as HINT 0). -/
structure Nop where
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
instance : AArch64Instruction Nop where
  encodeWord _ := 0xD503201F
  step _ s := s.advancePc
  toUops _ :=
    [{ mnemonic := "NOP", uopClass := .intALU, eligibleSlots := [.slot0, .slot1], latencyCycles := 1, reciprocalThroughput := 0.5, srcRegs := [], dstRegs := [] }]
  toAssembly _ := "nop"
  roundtripCases := [ {} ]
  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
/-- All roundtrip test cases for the System instruction family. -/
def systemFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := Nop)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Svc)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := Hlt)).map AnyAArch64Instruction.mk

-- Smart constructors

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
def svcInstr (imm : UInt16 := 0) : Svc := { imm := imm }

/- REF: docs/TARGETS/ARM64.md#15-system-family -/
def hltInstr (imm : UInt16 := 0xF000) : Hlt := { imm := imm }

end Gasm.Targets.AArch64.Instructions

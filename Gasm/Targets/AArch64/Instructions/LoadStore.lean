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

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- LDR (immediate unsigned scaled): Loads a 32-bit or 64-bit word from memory at base + unsigned scaled offset. -/
structure LdrImm where
  is64   : Bool
  rt     : Reg64
  rn     : Reg64
  offset : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction LdrImm where
  encodeWord i :=
    let size : UInt32 := if i.is64 then (3 : UInt32) <<< 30 else (2 : UInt32) <<< 30
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm12 := ((i.offset / scale).toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    size ||| ((0x39 : UInt32) <<< 24) ||| ((1 : UInt32) <<< 22) ||| imm12 ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset
    if i.is64 then s.setReg64 i.rt (s.readMem .w64 addr) |>.advancePc
    else s.setReg64 i.rt (s.readMem .w32 addr) |>.advancePc

  toUops i :=
    [{ mnemonic := "LDR_IMM", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt], isLoad := true }]

  toAssembly i :=
    if i.offset == 0 then s!"ldr {formatReg i.is64 i.rt}, [{i.rn}]"
    else s!"ldr {formatReg i.is64 i.rt}, [{i.rn}, #{i.offset}]"

  roundtripCases := [
    { is64 := true, rt := .x0, rn := .sp, offset := 0 },
    { is64 := false, rt := .x1, rn := .sp, offset := 8 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- STR (immediate unsigned scaled): Stores a 32-bit or 64-bit word to memory at base + unsigned scaled offset. -/
structure StrImm where
  is64   : Bool
  rt     : Reg64
  rn     : Reg64
  offset : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction StrImm where
  encodeWord i :=
    let size : UInt32 := if i.is64 then (3 : UInt32) <<< 30 else (2 : UInt32) <<< 30
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm12 := ((i.offset / scale).toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    size ||| ((0x39 : UInt32) <<< 24) ||| imm12 ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset
    if i.is64 then s.writeMem .w64 addr (s.getReg64 i.rt) |>.advancePc
    else s.writeMem .w32 addr (s.getReg64 i.rt &&& 0xFFFFFFFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "STR_IMM", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt], dstRegs := [], isStore := true }]

  toAssembly i :=
    if i.offset == 0 then s!"str {formatReg i.is64 i.rt}, [{i.rn}]"
    else s!"str {formatReg i.is64 i.rt}, [{i.rn}, #{i.offset}]"

  roundtripCases := [
    { is64 := true, rt := .x0, rn := .sp, offset := 0 },
    { is64 := false, rt := .x1, rn := .sp, offset := 8 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- LDRB (immediate): Loads a byte from memory with zero-extension. -/
structure LdrbImm where
  rt     : Reg64
  rn     : Reg64
  offset : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction LdrbImm where
  encodeWord i :=
    let imm12 := (i.offset.toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    ((0x39 : UInt32) <<< 24) ||| ((1 : UInt32) <<< 22) ||| imm12 ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset
    s.setReg64 i.rt (s.readMem .w8 addr) |>.advancePc

  toUops i :=
    [{ mnemonic := "LDRB_IMM", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt], isLoad := true }]

  toAssembly i :=
    if i.offset == 0 then s!"ldrb {formatReg false i.rt}, [{i.rn}]"
    else s!"ldrb {formatReg false i.rt}, [{i.rn}, #{i.offset}]"

  roundtripCases := [
    { rt := .x2, rn := .x3, offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- STRB (immediate): Stores a byte to memory. -/
structure StrbImm where
  rt     : Reg64
  rn     : Reg64
  offset : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction StrbImm where
  encodeWord i :=
    let imm12 := (i.offset.toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    ((0x39 : UInt32) <<< 24) ||| imm12 ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset
    s.writeMem .w8 addr (s.getReg64 i.rt &&& 0xFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "STRB_IMM", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt], dstRegs := [], isStore := true }]

  toAssembly i :=
    if i.offset == 0 then s!"strb {formatReg false i.rt}, [{i.rn}]"
    else s!"strb {formatReg false i.rt}, [{i.rn}, #{i.offset}]"

  roundtripCases := [
    { rt := .x2, rn := .x3, offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- LDRH (immediate): Loads a 16-bit halfword from memory with zero-extension. -/
structure LdrhImm where
  rt     : Reg64
  rn     : Reg64
  offset : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction LdrhImm where
  encodeWord i :=
    let imm12 := ((i.offset / 2).toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    ((1 : UInt32) <<< 30) ||| ((0x39 : UInt32) <<< 24) ||| ((1 : UInt32) <<< 22) ||| imm12 ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset
    s.setReg64 i.rt (s.readMem .w16 addr) |>.advancePc

  toUops i :=
    [{ mnemonic := "LDRH_IMM", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt], isLoad := true }]

  toAssembly i :=
    if i.offset == 0 then s!"ldrh {formatReg false i.rt}, [{i.rn}]"
    else s!"ldrh {formatReg false i.rt}, [{i.rn}, #{i.offset}]"

  roundtripCases := [
    { rt := .x4, rn := .x5, offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- STRH (immediate): Stores a 16-bit halfword to memory. -/
structure StrhImm where
  rt     : Reg64
  rn     : Reg64
  offset : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction StrhImm where
  encodeWord i :=
    let imm12 := ((i.offset / 2).toUInt32 &&& 0xFFF) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    ((1 : UInt32) <<< 30) ||| ((0x39 : UInt32) <<< 24) ||| imm12 ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset
    s.writeMem .w16 addr (s.getReg64 i.rt &&& 0xFFFF) |>.advancePc

  toUops i :=
    [{ mnemonic := "STRH_IMM", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt], dstRegs := [], isStore := true }]

  toAssembly i :=
    if i.offset == 0 then s!"strh {formatReg false i.rt}, [{i.rn}]"
    else s!"strh {formatReg false i.rt}, [{i.rn}, #{i.offset}]"

  roundtripCases := [
    { rt := .x4, rn := .x5, offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- LDR (post-indexed): Loads a register and post-increments base. -/
structure LdrPost where
  is64   : Bool
  rt     : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction LdrPost where
  encodeWord i :=
    let size : UInt32 := if i.is64 then (3 : UInt32) <<< 30 else (2 : UInt32) <<< 30
    let imm9 := (i.offset.toUInt64.toUInt32 &&& 0x1FF) <<< 12
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    size ||| ((0x38 : UInt32) <<< 24) ||| ((1 : UInt32) <<< 22) ||| imm9 ||| ((1 : UInt32) <<< 10) ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn
    let nextRn := addr + i.offset.toUInt64
    let s' := if i.is64 then s.setReg64 i.rt (s.readMem .w64 addr) else s.setReg64 i.rt (s.readMem .w32 addr)
    s'.setReg64 i.rn nextRn |>.advancePc

  toUops i :=
    [{ mnemonic := "LDR_POST", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt, i.rn], isLoad := true }]

  toAssembly i :=
    s!"ldr {formatReg i.is64 i.rt}, [{i.rn}], #{i.offset.toInt}"

  roundtripCases := [
    { is64 := true, rt := .x0, rn := .x1, offset := 8 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- STR (post-indexed): Stores a register and post-increments base. -/
structure StrPost where
  is64   : Bool
  rt     : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction StrPost where
  encodeWord i :=
    let size : UInt32 := if i.is64 then (3 : UInt32) <<< 30 else (2 : UInt32) <<< 30
    let imm9 := (i.offset.toUInt64.toUInt32 &&& 0x1FF) <<< 12
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    size ||| ((0x38 : UInt32) <<< 24) ||| imm9 ||| ((1 : UInt32) <<< 10) ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn
    let nextRn := addr + i.offset.toUInt64
    let s' := if i.is64 then s.writeMem .w64 addr (s.getReg64 i.rt) else s.writeMem .w32 addr (s.getReg64 i.rt &&& 0xFFFFFFFF)
    s'.setReg64 i.rn nextRn |>.advancePc

  toUops i :=
    [{ mnemonic := "STR_POST", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt], dstRegs := [i.rn], isStore := true }]

  toAssembly i :=
    s!"str {formatReg i.is64 i.rt}, [{i.rn}], #{i.offset.toInt}"

  roundtripCases := [
    { is64 := true, rt := .x0, rn := .x1, offset := 8 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- LDR (pre-indexed): Pre-increments base and loads register. -/
structure LdrPre where
  is64   : Bool
  rt     : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction LdrPre where
  encodeWord i :=
    let size : UInt32 := if i.is64 then (3 : UInt32) <<< 30 else (2 : UInt32) <<< 30
    let imm9 := (i.offset.toUInt64.toUInt32 &&& 0x1FF) <<< 12
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    size ||| ((0x38 : UInt32) <<< 24) ||| ((1 : UInt32) <<< 22) ||| imm9 ||| ((3 : UInt32) <<< 10) ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset.toUInt64
    let s' := if i.is64 then s.setReg64 i.rt (s.readMem .w64 addr) else s.setReg64 i.rt (s.readMem .w32 addr)
    s'.setReg64 i.rn addr |>.advancePc

  toUops i :=
    [{ mnemonic := "LDR_PRE", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt, i.rn], isLoad := true }]

  toAssembly i :=
    s!"ldr {formatReg i.is64 i.rt}, [{i.rn}, #{i.offset.toInt}]!"

  roundtripCases := [
    { is64 := true, rt := .x0, rn := .x1, offset := 8 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- STR (pre-indexed): Pre-increments base and stores register. -/
structure StrPre where
  is64   : Bool
  rt     : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction StrPre where
  encodeWord i :=
    let size : UInt32 := if i.is64 then (3 : UInt32) <<< 30 else (2 : UInt32) <<< 30
    let imm9 := (i.offset.toUInt64.toUInt32 &&& 0x1FF) <<< 12
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    size ||| ((0x38 : UInt32) <<< 24) ||| imm9 ||| ((3 : UInt32) <<< 10) ||| rnCode ||| rtCode

  step i s :=
    let addr := s.getReg64 i.rn + i.offset.toUInt64
    let s' := if i.is64 then s.writeMem .w64 addr (s.getReg64 i.rt) else s.writeMem .w32 addr (s.getReg64 i.rt &&& 0xFFFFFFFF)
    s'.setReg64 i.rn addr |>.advancePc

  toUops i :=
    [{ mnemonic := "STR_PRE", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt], dstRegs := [i.rn], isStore := true }]

  toAssembly i :=
    s!"str {formatReg i.is64 i.rt}, [{i.rn}, #{i.offset.toInt}]!"

  roundtripCases := [
    { is64 := true, rt := .x0, rn := .x1, offset := 8 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- LDR (literal): Loads register relative to PC. -/
structure LdrLit where
  is64   : Bool
  rt     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
instance : AArch64Instruction LdrLit where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (1 : UInt32) <<< 30 else 0
    let imm19 := ((i.offset.toUInt64 >>> 2).toUInt32 &&& 0x7FFFF) <<< 5
    let rtCode := i.rt.code.toUInt32 &&& 0x1F
    opc ||| ((0x18 : UInt32) <<< 24) ||| imm19 ||| rtCode

  step i s :=
    let addr := s.pc + i.offset.toUInt64
    if i.is64 then s.setReg64 i.rt (s.readMem .w64 addr) |>.advancePc
    else s.setReg64 i.rt (s.readMem .w32 addr) |>.advancePc

  toUops i :=
    [{ mnemonic := "LDR_LIT", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [], dstRegs := [i.rt], isLoad := true }]

  toAssembly i :=
    s!"ldr {formatReg i.is64 i.rt}, [pc, #{i.offset.toInt}]"

  roundtripCases := [
    { is64 := true, rt := .x0, offset := 16 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- LDP (post-indexed): Loads pair of registers and post-increments base. -/
structure LdpPost where
  is64   : Bool
  rt1    : Reg64
  rt2    : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
instance : AArch64Instruction LdpPost where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (2 : UInt32) <<< 30 else 0
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm7 := ((i.offset.toUInt64 / scale).toUInt32 &&& 0x7F) <<< 15
    let rt2Code := (i.rt2.code.toUInt32 &&& 0x1F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rt1Code := i.rt1.code.toUInt32 &&& 0x1F
    opc ||| ((0x14 : UInt32) <<< 25) ||| ((1 : UInt32) <<< 23) ||| ((1 : UInt32) <<< 22) ||| imm7 ||| rt2Code ||| rnCode ||| rt1Code

  step i s :=
    let addr := s.getReg64 i.rn
    let nextRn := addr + i.offset.toUInt64
    let stride : UInt64 := if i.is64 then 8 else 4
    let w : MemWidth := if i.is64 then .w64 else .w32
    let val1 := s.readMem w addr
    let val2 := s.readMem w (addr + stride)
    let s1 := s.setReg64 i.rt1 val1
    let s2 := s1.setReg64 i.rt2 val2
    s2.setReg64 i.rn nextRn |>.advancePc

  toUops i :=
    [ { mnemonic := "LDP_POST1", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt1, i.rn], isLoad := true },
      { mnemonic := "LDP_POST2", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt2], isLoad := true } ]

  toAssembly i :=
    s!"ldp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}], #{i.offset.toInt}"

  roundtripCases := [
    { is64 := true, rt1 := .x29, rt2 := .x30, rn := .sp, offset := 16 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- STP (post-indexed): Stores pair of registers and post-increments base. -/
structure StpPost where
  is64   : Bool
  rt1    : Reg64
  rt2    : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
instance : AArch64Instruction StpPost where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (2 : UInt32) <<< 30 else 0
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm7 := ((i.offset.toUInt64 / scale).toUInt32 &&& 0x7F) <<< 15
    let rt2Code := (i.rt2.code.toUInt32 &&& 0x1F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rt1Code := i.rt1.code.toUInt32 &&& 0x1F
    opc ||| ((0x14 : UInt32) <<< 25) ||| ((1 : UInt32) <<< 23) ||| imm7 ||| rt2Code ||| rnCode ||| rt1Code

  step i s :=
    let addr := s.getReg64 i.rn
    let nextRn := addr + i.offset.toUInt64
    let stride : UInt64 := if i.is64 then 8 else 4
    let w : MemWidth := if i.is64 then .w64 else .w32
    let val1 := s.getReg64 i.rt1
    let val2 := s.getReg64 i.rt2
    let s1 := s.writeMem w addr (if i.is64 then val1 else val1 &&& 0xFFFFFFFF)
    let s2 := s1.writeMem w (addr + stride) (if i.is64 then val2 else val2 &&& 0xFFFFFFFF)
    s2.setReg64 i.rn nextRn |>.advancePc

  toUops i :=
    [ { mnemonic := "STP_POST1", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt1], dstRegs := [i.rn], isStore := true },
      { mnemonic := "STP_POST2", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt2], dstRegs := [], isStore := true } ]

  toAssembly i :=
    s!"stp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}], #{i.offset.toInt}"

  roundtripCases := [
    { is64 := true, rt1 := .x29, rt2 := .x30, rn := .sp, offset := 16 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- LDP (pre-indexed): Pre-increments base and loads pair of registers. -/
structure LdpPre where
  is64   : Bool
  rt1    : Reg64
  rt2    : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
instance : AArch64Instruction LdpPre where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (2 : UInt32) <<< 30 else 0
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm7 := ((i.offset.toUInt64 / scale).toUInt32 &&& 0x7F) <<< 15
    let rt2Code := (i.rt2.code.toUInt32 &&& 0x1F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rt1Code := i.rt1.code.toUInt32 &&& 0x1F
    opc ||| ((0x14 : UInt32) <<< 25) ||| ((3 : UInt32) <<< 23) ||| ((1 : UInt32) <<< 22) ||| imm7 ||| rt2Code ||| rnCode ||| rt1Code

  step i s :=
    let addr := s.getReg64 i.rn + i.offset.toUInt64
    let stride : UInt64 := if i.is64 then 8 else 4
    let w : MemWidth := if i.is64 then .w64 else .w32
    let val1 := s.readMem w addr
    let val2 := s.readMem w (addr + stride)
    let s1 := s.setReg64 i.rt1 val1
    let s2 := s1.setReg64 i.rt2 val2
    s2.setReg64 i.rn addr |>.advancePc

  toUops i :=
    [ { mnemonic := "LDP_PRE1", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt1, i.rn], isLoad := true },
      { mnemonic := "LDP_PRE2", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt2], isLoad := true } ]

  toAssembly i :=
    s!"ldp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}, #{i.offset.toInt}]!"

  roundtripCases := [
    { is64 := true, rt1 := .x29, rt2 := .x30, rn := .sp, offset := (-16) }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- STP (pre-indexed): Pre-increments base and stores pair of registers. -/
structure StpPre where
  is64   : Bool
  rt1    : Reg64
  rt2    : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
instance : AArch64Instruction StpPre where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (2 : UInt32) <<< 30 else 0
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm7 := ((i.offset.toUInt64 / scale).toUInt32 &&& 0x7F) <<< 15
    let rt2Code := (i.rt2.code.toUInt32 &&& 0x1F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rt1Code := i.rt1.code.toUInt32 &&& 0x1F
    opc ||| ((0x14 : UInt32) <<< 25) ||| ((3 : UInt32) <<< 23) ||| imm7 ||| rt2Code ||| rnCode ||| rt1Code

  step i s :=
    let addr := s.getReg64 i.rn + i.offset.toUInt64
    let stride : UInt64 := if i.is64 then 8 else 4
    let w : MemWidth := if i.is64 then .w64 else .w32
    let val1 := s.getReg64 i.rt1
    let val2 := s.getReg64 i.rt2
    let s1 := s.writeMem w addr (if i.is64 then val1 else val1 &&& 0xFFFFFFFF)
    let s2 := s1.writeMem w (addr + stride) (if i.is64 then val2 else val2 &&& 0xFFFFFFFF)
    s2.setReg64 i.rn addr |>.advancePc

  toUops i :=
    [ { mnemonic := "STP_PRE1", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt1], dstRegs := [i.rn], isStore := true },
      { mnemonic := "STP_PRE2", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt2], dstRegs := [], isStore := true } ]

  toAssembly i :=
    s!"stp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}, #{i.offset.toInt}]!"

  roundtripCases := [
    { is64 := true, rt1 := .x29, rt2 := .x30, rn := .sp, offset := (-16) }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- LDP (offset): Loads pair of registers at base + signed scaled offset. -/
structure LdpOffset where
  is64   : Bool
  rt1    : Reg64
  rt2    : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
instance : AArch64Instruction LdpOffset where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (2 : UInt32) <<< 30 else 0
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm7 := ((i.offset.toUInt64 / scale).toUInt32 &&& 0x7F) <<< 15
    let rt2Code := (i.rt2.code.toUInt32 &&& 0x1F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rt1Code := i.rt1.code.toUInt32 &&& 0x1F
    opc ||| ((0x14 : UInt32) <<< 25) ||| ((2 : UInt32) <<< 23) ||| ((1 : UInt32) <<< 22) ||| imm7 ||| rt2Code ||| rnCode ||| rt1Code

  step i s :=
    let addr := s.getReg64 i.rn + i.offset.toUInt64
    let stride : UInt64 := if i.is64 then 8 else 4
    let w : MemWidth := if i.is64 then .w64 else .w32
    let val1 := s.readMem w addr
    let val2 := s.readMem w (addr + stride)
    let s1 := s.setReg64 i.rt1 val1
    let s2 := s1.setReg64 i.rt2 val2
    s2.advancePc

  toUops i :=
    [ { mnemonic := "LDP_UOP1", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt1], isLoad := true },
      { mnemonic := "LDP_UOP2", uopClass := .load, eligibleSlots := [.slot1], latencyCycles := 3, reciprocalThroughput := 1.0, srcRegs := [i.rn], dstRegs := [i.rt2], isLoad := true } ]

  toAssembly i :=
    if i.offset.toInt == 0 then
      s!"ldp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}]"
    else
      s!"ldp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}, #{i.offset.toInt}]"

  roundtripCases := [
    { is64 := true, rt1 := .x0, rt2 := .x1, rn := .sp, offset := 0 },
    { is64 := false, rt1 := .x2, rt2 := .x3, rn := .sp, offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- STP (offset): Stores pair of registers at base + signed scaled offset. -/
structure StpOffset where
  is64   : Bool
  rt1    : Reg64
  rt2    : Reg64
  rn     : Reg64
  offset : Int64
  deriving DecidableEq, Repr, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
instance : AArch64Instruction StpOffset where
  encodeWord i :=
    let opc : UInt32 := if i.is64 then (2 : UInt32) <<< 30 else 0
    let scale : UInt64 := if i.is64 then 8 else 4
    let imm7 := ((i.offset.toUInt64 / scale).toUInt32 &&& 0x7F) <<< 15
    let rt2Code := (i.rt2.code.toUInt32 &&& 0x1F) <<< 10
    let rnCode := (i.rn.code.toUInt32 &&& 0x1F) <<< 5
    let rt1Code := i.rt1.code.toUInt32 &&& 0x1F
    opc ||| ((0x14 : UInt32) <<< 25) ||| ((2 : UInt32) <<< 23) ||| imm7 ||| rt2Code ||| rnCode ||| rt1Code

  step i s :=
    let addr := s.getReg64 i.rn + i.offset.toUInt64
    let stride : UInt64 := if i.is64 then 8 else 4
    let w : MemWidth := if i.is64 then .w64 else .w32
    let val1 := s.getReg64 i.rt1
    let val2 := s.getReg64 i.rt2
    let s1 := s.writeMem w addr (if i.is64 then val1 else val1 &&& 0xFFFFFFFF)
    let s2 := s1.writeMem w (addr + stride) (if i.is64 then val2 else val2 &&& 0xFFFFFFFF)
    s2.advancePc

  toUops i :=
    [ { mnemonic := "STP_UOP1", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt1], dstRegs := [], isStore := true },
      { mnemonic := "STP_UOP2", uopClass := .store, eligibleSlots := [.slot1], latencyCycles := 1, reciprocalThroughput := 1.0, srcRegs := [i.rn, i.rt2], dstRegs := [], isStore := true } ]

  toAssembly i :=
    if i.offset.toInt == 0 then
      s!"stp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}]"
    else
      s!"stp {formatReg i.is64 i.rt1}, {formatReg i.is64 i.rt2}, [{i.rn}, #{i.offset.toInt}]"

  roundtripCases := [
    { is64 := true, rt1 := .x0, rt2 := .x1, rn := .sp, offset := 0 },
    { is64 := false, rt1 := .x2, rt2 := .x3, rn := .sp, offset := 0 }
  ]

  validationOracle _ := .llvmMcEncoding "Differential fuzzer verified encoding bit-for-bit against llvm-mc-19"
  costProvenance _ := .modelInternalUnvalidated "Cortex-A53 Software Optimization Guide (DDI 0500J) nominal cycle estimates"

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- All roundtrip test cases for immediate Load/Store variants. -/
def loadStoreImmFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := LdrImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := StrImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdrbImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := StrbImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdrhImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := StrhImm)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdrPost)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := StrPost)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdrPre)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := StrPre)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdrLit)).map AnyAArch64Instruction.mk

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
/-- All roundtrip test cases for Load/Store Pair variants. -/
def loadStorePairFamilyCases : List AnyAArch64Instruction :=
  (AArch64Instruction.roundtripCases (ι := StpPre)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdpPost)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := StpOffset)).map AnyAArch64Instruction.mk ++
  (AArch64Instruction.roundtripCases (ι := LdpOffset)).map AnyAArch64Instruction.mk

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
/-- All roundtrip test cases for the combined Load/Store family. -/
def loadStoreFamilyCases : List AnyAArch64Instruction :=
  loadStoreImmFamilyCases ++ loadStorePairFamilyCases

-- Smart constructors

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
def ldr64 (rt rn : Reg64) (offset : UInt64 := 0) : LdrImm :=
  { is64 := true, rt := rt, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
def ldr32 (rt : Reg32) (rn : Reg64) (offset : UInt64 := 0) : LdrImm :=
  { is64 := false, rt := reg32To64 rt, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
def str64 (rt rn : Reg64) (offset : UInt64 := 0) : StrImm :=
  { is64 := true, rt := rt, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
def str32 (rt : Reg32) (rn : Reg64) (offset : UInt64 := 0) : StrImm :=
  { is64 := false, rt := reg32To64 rt, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#8-loadstoreimm-family -/
def strbReg (rt : Reg32) (rn : Reg64) (offset : UInt64 := 0) : StrbImm :=
  { rt := reg32To64 rt, rn := rn, offset := offset }

-- Pair smart constructors

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def ldpPost (is64 : Bool) (rt1 rt2 rn : Reg64) (offset : Int64) : LdpPost :=
  { is64 := is64, rt1 := rt1, rt2 := rt2, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def ldpPre (is64 : Bool) (rt1 rt2 rn : Reg64) (offset : Int64) : LdpPre :=
  { is64 := is64, rt1 := rt1, rt2 := rt2, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def ldpOffset (is64 : Bool) (rt1 rt2 rn : Reg64) (offset : Int64) : LdpOffset :=
  { is64 := is64, rt1 := rt1, rt2 := rt2, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def stpPost (is64 : Bool) (rt1 rt2 rn : Reg64) (offset : Int64) : StpPost :=
  { is64 := is64, rt1 := rt1, rt2 := rt2, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def stpPre (is64 : Bool) (rt1 rt2 rn : Reg64) (offset : Int64) : StpPre :=
  { is64 := is64, rt1 := rt1, rt2 := rt2, rn := rn, offset := offset }

/- REF: docs/TARGETS/ARM64.md#10-loadstorepair-family -/
def stpOffset (is64 : Bool) (rt1 rt2 rn : Reg64) (offset : Int64) : StpOffset :=
  { is64 := is64, rt1 := rt1, rt2 := rt2, rn := rn, offset := offset }

end Gasm.Targets.AArch64.Instructions

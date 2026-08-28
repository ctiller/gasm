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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg32, imm32 instruction: moves 32-bit immediate into register with 32-to-64-bit zero extension. -/
structure MovR32Imm32 where
  dst : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR32Imm32 where
  encode i :=
    let (code, isExt) := reg32Code i.dst
    let rexPrefix := if isExt then #[makeRex false false false true] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xB8 + code] ++ uint32ToLittleEndian i.imm
    
  step i s :=
    let s' := s.setGpr32 i.dst i.imm
    { s' with rip := s.rip + (if (reg32Code i.dst).2 then 6 else 5) }

  toUops _ := [{ mnemonic := "MOV.imm32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_r32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (MovR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (MovR32Imm32.mk .r15d ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg64, imm64: moves full 64-bit immediate into general-purpose register. -/
structure MovR64Imm64 where
  dst : Reg64
  imm : UInt64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR64Imm64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let rex := makeRex true false false dstExt
    ByteArray.mk #[rex, 0xB8 + dstCode] ++ uint64ToLittleEndian i.imm

  step i s :=
    let s' := s.setGpr64 i.dst i.imm
    { s' with rip := s.rip + 10 }

  toUops _ := [{ mnemonic := "MOV.imm64", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, strict qword 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_r64_imm64 .{i.dst} {formatHex64 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    -- Uses the smaller curatedUInt64Cases (not the 17-element curated64BitValues, which is sized
    -- for fuzz-state generation) to bound this family's contribution to the MOV shard's `decide`
    -- elaboration cost — this was the single largest case list in the family that OOM'd once
    -- during a parallel 21-shard build (see docs/TARGETS/X86_64.md).
    (allReg64List.map (MovR64Imm64.mk · 0)) ++ (curatedUInt64Cases.map (MovR64Imm64.mk .rax ·)) ++
    (curatedUInt64Cases.map (MovR64Imm64.mk .r15 ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg64, reg64 instruction: moves full 64-bit value between general-purpose registers. -/
structure MovR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x89, makeModRM 3 srcCode dstCode]
    
  step i s :=
    let s' := s.setGpr64 i.dst (s.gprs i.src)
    { s' with rip := s.rip + 3 }

  toUops _ := [{ mnemonic := "MOV.reg", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, {i.src}"
  toLean i := s!"mov_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (MovR64R64.mk · .rax)) ++ (allReg64List.map (MovR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV BYTE PTR [RSP + disp8], val: writes an 8-bit immediate byte directly to stack offset. -/
structure MovRspDispByte where
  disp : UInt8
  val  : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovRspDispByte where
  encode i :=
    if i.disp == 0 then
      ByteArray.mk #[0xC6, makeModRM 0 0 4, makeSIB 0 4 4, i.val]
    else
      ByteArray.mk #[0xC6, makeModRM 1 0 4, makeSIB 0 4 4, i.disp, i.val]

  step i s :=
    let base := s.rsp + signExtend8To64 i.disp
    let s' := s.write8 base i.val
    let len := if i.disp == 0 then 4 else 5
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "MOV.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "MOV.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"mov byte [rsp], 0x{String.ofList (Nat.toDigits 16 i.val.toNat)}"
    else
      s!"mov byte [rsp {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.val.toNat)}"
  toLean i := s!"mov_rsp_byte {formatHex8 i.disp} {formatHex8 i.val}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (curatedUInt8Cases.map (MovRspDispByte.mk · 0x00)) ++ (curatedUInt8Cases.map (MovRspDispByte.mk 0x00 ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV DWORD PTR [RSP + disp8], imm32: writes a 32-bit immediate doubleword directly to stack offset. -/
structure MovRspDispImm32 where
  disp : UInt8
  imm  : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovRspDispImm32 where
  encode i :=
    if i.disp == 0 then
      ByteArray.mk #[0xC7, makeModRM 0 0 4, makeSIB 0 4 4] ++ uint32ToLittleEndian i.imm
    else
      ByteArray.mk #[0xC7, makeModRM 1 0 4, makeSIB 0 4 4, i.disp] ++ uint32ToLittleEndian i.imm

  step i s :=
    let base := s.rsp + signExtend8To64 i.disp
    let len := if i.disp == 0 then 7 else 8
    let s' := { s with
      memory := fun a =>
        if a == base then i.imm.toUInt8
        else if a == base + 1 then (i.imm >>> 8).toUInt8
        else if a == base + 2 then (i.imm >>> 16).toUInt8
        else if a == base + 3 then (i.imm >>> 24).toUInt8
        else s.memory a
      rip := s.rip + len
    }
    s'

  toUops _ := [
    { mnemonic := "MOV.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "MOV.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"mov dword [rsp], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
    else
      s!"mov dword [rsp {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_rsp32 {formatHex8 i.disp} {formatHex32 i.imm}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (curatedUInt8Cases.map (MovRspDispImm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovRspDispImm32.mk 0x00 ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV QWORD PTR [RSP + disp8], imm32: sign-extends 32-bit immediate to 64 bits and writes to stack offset. -/
structure MovRspDispImm64 where
  disp : UInt8
  imm  : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovRspDispImm64 where
  encode i :=
    if i.disp == 0 then
      ByteArray.mk #[makeRex true false false false, 0xC7, makeModRM 0 0 4, makeSIB 0 4 4] ++ uint32ToLittleEndian i.imm
    else
      ByteArray.mk #[makeRex true false false false, 0xC7, makeModRM 1 0 4, makeSIB 0 4 4, i.disp] ++ uint32ToLittleEndian i.imm

  step i s :=
    let base := s.rsp + signExtend8To64 i.disp
    let extByte : UInt8 := if (i.imm &&& 0x80000000) != 0 then 0xFF else 0x00
    let len := if i.disp == 0 then 8 else 9
    let s' := { s with
      memory := fun a =>
        if a == base then i.imm.toUInt8
        else if a == base + 1 then (i.imm >>> 8).toUInt8
        else if a == base + 2 then (i.imm >>> 16).toUInt8
        else if a == base + 3 then (i.imm >>> 24).toUInt8
        else if a >= base + 4 && a < base + 8 then extByte
        else s.memory a
      rip := s.rip + len
    }
    s'

  toUops _ := [
    { mnemonic := "MOV.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "MOV.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"mov qword [rsp], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
    else
      s!"mov qword [rsp {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_rsp64 {formatHex8 i.disp} {formatHex32 i.imm}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (curatedUInt8Cases.map (MovRspDispImm64.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovRspDispImm64.mk 0x00 ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV [dstPtr], srcReg8: Writes the low 8-bit byte of srcReg into memory at [dstPtr]. -/
structure MovMem8Reg8 where
  dstPtr : Reg64
  srcReg : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovMem8Reg8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dstPtr
    let (srcCode, srcExt) := reg64Code i.srcReg
    let rex := makeRex false srcExt false dstExt
    let rexNeeded := srcExt || dstExt || srcCode >= 4
    let rexPrefix := if rexNeeded then #[rex] else #[]
    if dstCode == 4 then
      -- RSP / R12 requires SIB byte (scale=0, index=4 (none), base=4)
      let modrm := makeModRM 0 srcCode 4
      let sib := makeSIB 0 4 4
      ByteArray.mk rexPrefix ++ ByteArray.mk #[0x88, modrm, sib]
    else if dstCode == 5 then
      -- RBP / R13 base with no displacement requires mod=1 and disp8=0
      let modrm := makeModRM 1 srcCode 5
      ByteArray.mk rexPrefix ++ ByteArray.mk #[0x88, modrm, 0x00]
    else
      let modrm := makeModRM 0 srcCode dstCode
      ByteArray.mk rexPrefix ++ ByteArray.mk #[0x88, modrm]

  step i s :=
    let (dstCode, dstExt) := reg64Code i.dstPtr
    let (srcCode, srcExt) := reg64Code i.srcReg
    let addr := s.gprs i.dstPtr
    let val := (s.gprs i.srcReg).toUInt8
    let s' := s.write8 addr val
    let rexNeeded := srcExt || dstExt || srcCode >= 4
    let rexLen := if rexNeeded then 1 else 0
    let extraLen := if dstCode == 4 || dstCode == 5 then 1 else 0
    let instrLen := 2 + rexLen + extraLen
    { s' with rip := s.rip + instrLen }

  toUops _ := [
    { mnemonic := "MOV.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "MOV.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"mov byte [{i.dstPtr}], {reg64To8BitString i.srcReg}"
  toLean i := s!"mov_mem8 .{i.dstPtr} .{i.srcReg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovMem8Reg8.mk · .rax)) ++ (allReg64List.map (MovMem8Reg8.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovMem8Reg8.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV QWORD PTR [basePtr + disp8], srcReg64: Writes 64-bit register into memory at [basePtr + disp8]. -/
structure MovMem64DispReg64 where
  basePtr : Reg64
  disp    : UInt8
  srcReg  : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovMem64DispReg64 where
  encode i :=
    let (baseCode, baseExt) := reg64Code i.basePtr
    let (srcCode, srcExt) := reg64Code i.srcReg
    let rex := makeRex true srcExt false baseExt
    if i.disp == 0 && baseCode != 5 then
      if baseCode == 4 then
        ByteArray.mk #[rex, 0x89, makeModRM 0 srcCode 4, makeSIB 0 4 4]
      else
        ByteArray.mk #[rex, 0x89, makeModRM 0 srcCode baseCode]
    else
      if baseCode == 4 then
        ByteArray.mk #[rex, 0x89, makeModRM 1 srcCode 4, makeSIB 0 4 4, i.disp]
      else
        ByteArray.mk #[rex, 0x89, makeModRM 1 srcCode baseCode, i.disp]

  step i s :=
    let (baseCode, _) := reg64Code i.basePtr
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val := s.gprs i.srcReg
    let s' := s.write64 addr val
    let hasSib := baseCode == 4
    let hasDisp := i.disp != 0 || baseCode == 5
    let len := 3 + (if hasSib then 1 else 0) + (if hasDisp then 1 else 0)
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "MOV.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "MOV.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"mov qword [{i.basePtr}], {i.srcReg}"
    else
      s!"mov qword [{i.basePtr} {formatDisp8 i.disp}], {i.srcReg}"
  toLean i := s!"mov_mem64_disp .{i.basePtr} {formatHex8 i.disp} .{i.srcReg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovMem64DispReg64.mk · 0 .rax)) ++
    (curatedUInt8Cases.map (MovMem64DispReg64.mk .rax · .rax)) ++
    (allReg64List.map (MovMem64DispReg64.mk .rax 0 ·)) ++
    (extendedReg64Pairs.map fun p => MovMem64DispReg64.mk p.1 0 p.2) ++
    (curatedUInt8Cases.map (MovMem64DispReg64.mk .r15 · .r15))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV QWORD PTR [basePtr + disp8], imm32: Writes 32-bit immediate sign-extended into 64-bit memory. -/
structure MovMem64DispImm32 where
  basePtr : Reg64
  disp    : UInt8
  imm     : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovMem64DispImm32 where
  encode i :=
    let (baseCode, baseExt) := reg64Code i.basePtr
    let rex := makeRex true false false baseExt
    if i.disp == 0 && baseCode != 5 then
      if baseCode == 4 then
        ByteArray.mk #[rex, 0xC7, makeModRM 0 0 4, makeSIB 0 4 4] ++ uint32ToLittleEndian i.imm
      else
        ByteArray.mk #[rex, 0xC7, makeModRM 0 0 baseCode] ++ uint32ToLittleEndian i.imm
    else
      if baseCode == 4 then
        ByteArray.mk #[rex, 0xC7, makeModRM 1 0 4, makeSIB 0 4 4, i.disp] ++ uint32ToLittleEndian i.imm
      else
        ByteArray.mk #[rex, 0xC7, makeModRM 1 0 baseCode, i.disp] ++ uint32ToLittleEndian i.imm

  step i s :=
    let (baseCode, _) := reg64Code i.basePtr
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val : UInt64 := signExtendUInt32To64 i.imm
    let s' := s.write64 addr val
    let hasSib := baseCode == 4
    let hasDisp := i.disp != 0 || baseCode == 5
    let len := 7 + (if hasSib then 1 else 0) + (if hasDisp then 1 else 0)
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "MOV.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "MOV.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"mov qword [{i.basePtr}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
    else
      s!"mov qword [{i.basePtr} {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_mem64_disp_imm .{i.basePtr} {formatHex8 i.disp} {formatHex32 i.imm}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  -- basePtr varies over allReg64ListNoRsp: with basePtr=.rsp, this struct's SIB-base-4 encoding
  -- is byte-identical to the dedicated MovRspDispImm32/64 helpers, which the decoder
  -- canonicalizes to on purpose (matching the ADD/SUB RSP-immediate precedent) — that RSP case
  -- is exercised by MovRspDispImm32/64's own roundtripCases instead. RSP's SIB-base-4 sibling,
  -- R12 (rexB=true), is a genuinely distinct, correctly round-tripping case and stays included.
  roundtripCases :=
    (allReg64ListNoRsp.map (MovMem64DispImm32.mk · 0 0x00000000)) ++
    (curatedUInt8Cases.map (MovMem64DispImm32.mk .rax · 0x00000000)) ++
    (curatedUInt32Cases.map (MovMem64DispImm32.mk .rax 0 ·)) ++
    (curatedUInt8Cases.map (MovMem64DispImm32.mk .r15 · 0x00000000)) ++
    (curatedUInt32Cases.map (MovMem64DispImm32.mk .r15 0 ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV dstReg64, QWORD PTR [basePtr + disp8]: Reads 64-bit value from memory into register. -/
structure MovReg64Mem64Disp where
  dstReg  : Reg64
  basePtr : Reg64
  disp    : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovReg64Mem64Disp where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dstReg
    let (baseCode, baseExt) := reg64Code i.basePtr
    let rex := makeRex true dstExt false baseExt
    if i.disp == 0 && baseCode != 5 then
      if baseCode == 4 then
        ByteArray.mk #[rex, 0x8B, makeModRM 0 dstCode 4, makeSIB 0 4 4]
      else
        ByteArray.mk #[rex, 0x8B, makeModRM 0 dstCode baseCode]
    else
      if baseCode == 4 then
        ByteArray.mk #[rex, 0x8B, makeModRM 1 dstCode 4, makeSIB 0 4 4, i.disp]
      else
        ByteArray.mk #[rex, 0x8B, makeModRM 1 dstCode baseCode, i.disp]

  step i s :=
    let (baseCode, _) := reg64Code i.basePtr
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val := s.read64 addr
    let s' := s.setGpr64 i.dstReg val
    let hasSib := baseCode == 4
    let hasDisp := i.disp != 0 || baseCode == 5
    let len := 3 + (if hasSib then 1 else 0) + (if hasDisp then 1 else 0)
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "MOV.load", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"mov {i.dstReg}, qword [{i.basePtr}]"
    else
      s!"mov {i.dstReg}, qword [{i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"mov_reg64_mem64_disp .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovReg64Mem64Disp.mk · .rax 0)) ++
    (allReg64List.map (MovReg64Mem64Disp.mk .rax · 0)) ++
    (curatedUInt8Cases.map (MovReg64Mem64Disp.mk .rax .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovReg64Mem64Disp.mk p.1 p.2 0) ++
    (curatedUInt8Cases.map (MovReg64Mem64Disp.mk .r15 .r15 ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg32, imm32 helper. -/
def mov_r32 (dst : Reg32) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨MovR32Imm32.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg64, imm64 helper. -/
def mov_r64_imm64 (dst : Reg64) (imm : UInt64) : AnyX86_64Instruction :=
  ⟨MovR64Imm64.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg64, reg64 helper. -/
def mov_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨MovR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV BYTE PTR [RSP + disp8], val helper. -/
def mov_rsp_byte (disp : UInt8) (val : UInt8) : AnyX86_64Instruction :=
  ⟨MovRspDispByte.mk disp val⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV DWORD PTR [RSP + disp8], imm32 helper. -/
def mov_rsp32 (disp : UInt8) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨MovRspDispImm32.mk disp imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV QWORD PTR [RSP + disp8], imm32 helper. -/
def mov_rsp64 (disp : UInt8) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨MovRspDispImm64.mk disp imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV BYTE PTR [dstPtr], srcReg8 helper. -/
def mov_mem8 (dstPtr srcReg : Reg64) : AnyX86_64Instruction :=
  ⟨MovMem8Reg8.mk dstPtr srcReg⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV QWORD PTR [basePtr + disp8], srcReg64 helper. -/
def mov_mem64_disp (basePtr : Reg64) (disp : UInt8) (srcReg : Reg64) : AnyX86_64Instruction :=
  ⟨MovMem64DispReg64.mk basePtr disp srcReg⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV QWORD PTR [basePtr + disp8], imm32 helper. -/
def mov_mem64_disp_imm (basePtr : Reg64) (disp : UInt8) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨MovMem64DispImm32.mk basePtr disp imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV dstReg64, QWORD PTR [basePtr + disp8] helper. -/
def mov_reg64_mem64_disp (dstReg basePtr : Reg64) (disp : UInt8) : AnyX86_64Instruction :=
  ⟨MovReg64Mem64Disp.mk dstReg basePtr disp⟩

/- REF: intel-sdm#vol=2;instr=MOVZX;part=description -/
/-- MOVZX dstReg64, BYTE PTR [basePtr + disp8]: Moves 8-bit byte from memory with zero-extension into 64-bit register. -/
structure MovzxR64Mem8 where
  dstReg  : Reg64
  basePtr : Reg64
  disp    : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOVZX;part=operation -/
instance : X86_64Instruction MovzxR64Mem8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dstReg
    let (baseCode, baseExt) := reg64Code i.basePtr
    let rex := makeRex true dstExt false baseExt
    if i.disp == 0 && baseCode != 5 then
      if baseCode == 4 then
        ByteArray.mk #[rex, 0x0F, 0xB6, makeModRM 0 dstCode 4, makeSIB 0 4 4]
      else
        ByteArray.mk #[rex, 0x0F, 0xB6, makeModRM 0 dstCode baseCode]
    else
      if baseCode == 4 then
        ByteArray.mk #[rex, 0x0F, 0xB6, makeModRM 1 dstCode 4, makeSIB 0 4 4, i.disp]
      else
        ByteArray.mk #[rex, 0x0F, 0xB6, makeModRM 1 dstCode baseCode, i.disp]

  step i s :=
    let (baseCode, _) := reg64Code i.basePtr
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val := (s.memory addr).toUInt64
    let s' := s.setGpr64 i.dstReg val
    let hasSib := baseCode == 4
    let hasDisp := i.disp != 0 || baseCode == 5
    let len := 4 + (if hasSib then 1 else 0) + (if hasDisp then 1 else 0)
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "MOVZX.load", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4, reciprocalThroughput := 0.5 }
  ]
  toNASM i :=
    if i.disp == 0 then
      s!"movzx {i.dstReg}, byte [{i.basePtr}]"
    else
      s!"movzx {i.dstReg}, byte [{i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"movzx_r64_mem8 .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovzxR64Mem8.mk · .rax 0)) ++
    (allReg64List.map (MovzxR64Mem8.mk .rax · 0)) ++
    (curatedUInt8Cases.map (MovzxR64Mem8.mk .rax .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovzxR64Mem8.mk p.1 p.2 0) ++
    (curatedUInt8Cases.map (MovzxR64Mem8.mk .r15 .r15 ·))

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV dstReg32, DWORD PTR [RSP + disp8]: Reads 32-bit value from stack memory with 32-to-64-bit zero extension. -/
structure MovReg32RspDisp32 where
  dstReg : Reg32
  disp   : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovReg32RspDisp32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dstReg
    let rexPrefix := if dstExt then #[makeRex false dstExt false false] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x8B, makeModRM 1 dstCode 4, makeSIB 0 4 4, i.disp]

  step i s :=
    let addr := s.rsp + signExtend8To64 i.disp
    let b0 := (s.memory addr).toUInt32
    let b1 := (s.memory (addr + 1)).toUInt32 <<< 8
    let b2 := (s.memory (addr + 2)).toUInt32 <<< 16
    let b3 := (s.memory (addr + 3)).toUInt32 <<< 24
    let val := b0 ||| b1 ||| b2 ||| b3
    let s' := s.setGpr32 i.dstReg val
    let len := 4 + (if (reg32Code i.dstReg).2 then 1 else 0)
    { s' with rip := s.rip + len }

  toUops _ := [
    { mnemonic := "MOV.load", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4, reciprocalThroughput := 0.5 }
  ]
  -- Signed-displacement formatting is load-bearing here too (see the sibling fix throughout this
  -- file, found via P4(a)'s registry-derived encoding fuzzer,
  -- docs/X86_ISA_EXPANSION_PREREQUISITES.md): `{i.disp.toNat}` rendered `0x80` (disp=`0x80`, i.e.
  -- signed -128) as the POSITIVE literal "128", which does not fit a signed disp8 (-128..127) by
  -- NASM's reading, forcing it to a disp32 SIB encoding instead of the disp8 SIB form `encode`
  -- always emits. `formatDisp8` supplies the correct sign.
  toNASM i := s!"mov {i.dstReg}, dword [rsp {formatDisp8 i.disp}]"
  toLean i := s!"mov_r32_rsp .{i.dstReg} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet (PLAN.md Phase 3), and the memory-operand capability contract (P2) is also unbuilt -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg32List.map (MovReg32RspDisp32.mk · 0x00)) ++ (curatedUInt8Cases.map (MovReg32RspDisp32.mk .eax ·)) ++
    (curatedUInt8Cases.map (MovReg32RspDisp32.mk .r15d ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOVZX dstReg64, BYTE PTR [basePtr + disp8] helper. -/
def movzx_r64_mem8 (dstReg basePtr : Reg64) (disp : UInt8 := 0) : AnyX86_64Instruction :=
  ⟨MovzxR64Mem8.mk dstReg basePtr disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV dstReg32, DWORD PTR [RSP + disp8] helper. -/
def mov_r32_rsp (dstReg : Reg32) (disp : UInt8) : AnyX86_64Instruction :=
  ⟨MovReg32RspDisp32.mk dstReg disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV dstReg64, QWORD PTR [RSP + disp8] helper. -/
def mov_rsp64_to_reg (dstReg : Reg64) (disp : UInt8) : AnyX86_64Instruction :=
  ⟨MovReg64Mem64Disp.mk dstReg .rsp disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formal theorem: MovMem64DispImm32 faithfully sign-extends negative and positive 32-bit immediates into 64-bit memory per Intel SDM. -/
theorem mov_mem64_disp_imm_sign_extension_soundness :
    let s0 : X86_64MachineState := {
      rip := 0x1000,
      gprs := fun r => if r == .rax then 0x20000000 else 0,
      flags := 0,
      memory := fun _ => 0
    }
    -- Store negative 32-bit immediate 0xFFFFFFF6 (-10) at [rax + 0]
    let instrNeg : AnyX86_64Instruction := mov_mem64_disp_imm .rax 0 0xFFFFFFF6
    let s1 := X86_64Instruction.step instrNeg s0
    -- Store positive 32-bit immediate 0x1234 at [rax + 8]
    let instrPos : AnyX86_64Instruction := mov_mem64_disp_imm .rax 8 0x1234
    let s2 := X86_64Instruction.step instrPos s1
    (s2.read64 0x20000000 == 0xFFFFFFFFFFFFFFF6 &&
     s2.read64 0x20000008 == 0x0000000000001234) = true := by
  decide

end Gasm.Targets.X86_64.Instructions


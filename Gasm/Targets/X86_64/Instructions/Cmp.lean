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

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r64, r64: Compares two 64-bit general-purpose registers and updates condition flags. -/
structure CmpR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    let rex := makeRex true srcExt false dstExt
    let modrm := makeModRM 3 srcCode dstCode
    ByteArray.mk #[rex, 0x39, modrm]
  step i s :=
    let s' := s.setFlagsCmp64 (s.gprs i.dst) (s.gprs i.src)
    { s' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "CMP.reg", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, {i.src}"
  toLean i := s!"cmp_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmpR64R64.mk · .rax)) ++ (allReg64List.map (CmpR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmpR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r64, imm8: Compares 64-bit register with sign-extended 8-bit immediate. -/
structure CmpR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let rex := makeRex true false false dstExt
    let modrm := makeModRM 3 7 dstCode
    ByteArray.mk #[rex, 0x83, modrm, i.imm]
  step i s :=
    let s' := s.setFlagsCmp64 (s.gprs i.dst) (signExtend8To64 i.imm)
    { s' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "CMP.imm8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"cmp_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (CmpR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (CmpR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (CmpR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMP r64, r64 helper. -/
def cmp_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmpR64R64.mk dst src⟩

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- The existentially packaged register CMP step exposes its unsigned borrow test. -/
theorem cmp_r64_step_cf (dst src : Reg64) (s : X86_64MachineState) :
    ((X86_64Instruction.step (cmp_r64 dst src) s).cf = true) =
      (s.gprs dst < s.gprs src) := by
  change (((({ s with stdinBuffer := ByteArray.empty, incomingRequests := [] }).setFlagsCmp64
    (s.gprs dst) (s.gprs src)).cf = true) : Prop) = (s.gprs dst < s.gprs src)
  exact X86_64MachineState.setFlagsCmp64_cf _ _ _

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMP r64, imm8 helper. -/
def cmp_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨CmpR64Imm8.mk dst imm⟩

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r64, imm32: Compares 64-bit register with sign-extended 32-bit immediate. -/
structure CmpR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let rex := makeRex true false false dstExt
    let modrm := makeModRM 3 7 dstCode
    ByteArray.mk #[rex, 0x81, modrm] ++ uint32ToLittleEndian i.imm
  step i s :=
    let s' := s.setFlagsCmp64 (s.gprs i.dst) (signExtendUInt32To64 i.imm)
    { s' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "CMP.imm32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"cmp_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (CmpR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (CmpR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (CmpR64Imm32.mk .r15 ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMP r64, imm32 helper. -/
def cmp_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨CmpR64Imm32.mk dst imm⟩

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r32, r32: Compares 32-bit source register with destination register, setting flags. -/
structure CmpR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexNeeded := dstExt || srcExt
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x39, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := s.readGpr32 i.src
    let s' := s.setFlagsCmp32 dVal sVal
    let len := (if (reg32Code i.dst).2 || (reg32Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, {i.src}"
  toLean i := s!"cmp_r32 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (CmpR32R32.mk · .eax)) ++ (allReg32List.map (CmpR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => CmpR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r32, imm8: Compares sign-extended 8-bit immediate with 32-bit destination register, setting flags. -/
structure CmpR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x83, makeModRM 3 7 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt32
    let s' := s.setFlagsCmp32 dVal sVal
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"cmp_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (CmpR32Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (CmpR32Imm8.mk .eax ·)) ++
    (curatedUInt8Cases.map (CmpR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r32, imm32: Compares 32-bit immediate with destination register, setting flags. -/
structure CmpR32Imm32 where
  dst : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR32Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x81, makeModRM 3 7 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := i.imm
    let s' := s.setFlagsCmp32 dVal sVal
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 6
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"cmp_r32_imm32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (CmpR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (CmpR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (CmpR32Imm32.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r16, r16: Compares 16-bit source register with destination register, setting flags. -/
structure CmpR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexNeeded := dstExt || srcExt
    let rexBytes := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x39, makeModRM 3 srcCode dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let s' := s.setFlagsCmp16 dVal sVal
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, {i.src}"
  toLean i := s!"cmp_r16 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (CmpR16R16.mk · .ax)) ++ (allReg16List.map (CmpR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => CmpR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r16, imm8: Compares sign-extended 8-bit immediate with 16-bit destination register, setting flags. -/
structure CmpR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x83, makeModRM 3 7 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt16
    let s' := s.setFlagsCmp16 dVal sVal
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"cmp_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (CmpR16Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (CmpR16Imm8.mk .ax ·)) ++
    (curatedUInt8Cases.map (CmpR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r16, imm16: Compares 16-bit immediate with destination register, setting flags. -/
structure CmpR16Imm16 where
  dst : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR16Imm16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x81, makeModRM 3 7 dstCode]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := i.imm
    let s' := s.setFlagsCmp16 dVal sVal
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 4
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, word {i.imm.toNat}"
  toLean i := s!"cmp_r16_imm16 .{i.dst} {formatHex16 i.imm}"
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (CmpR16Imm16.mk · 0x0000)) ++ (curatedUInt16Cases.map (CmpR16Imm16.mk .ax ·)) ++
    (curatedUInt16Cases.map (CmpR16Imm16.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r8, r8: Compares 8-bit source register with destination register, setting flags. -/
structure CmpR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x38, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := s.readGpr8 i.src
    let s' := s.setFlagsCmp8 dVal sVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, {i.src}"
  toLean i := s!"cmp_r8 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (CmpR8R8.mk · .al)) ++ (allReg8List.map (CmpR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => CmpR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=CMP;part=description -/
/-- CMP r8, imm8: Compares 8-bit immediate with destination register, setting flags. -/
structure CmpR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CMP;part=operation -/
instance : X86_64Instruction CmpR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x80, makeModRM 3 7 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := i.imm
    let s' := s.setFlagsCmp8 dVal sVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "CMP.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"cmp {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"cmp_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (CmpR8Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (CmpR8Imm8.mk .al ·)) ++
    (curatedUInt8Cases.map (CmpR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def cmp_r32 (dst src : Reg32) : AnyX86_64Instruction := ⟨CmpR32R32.mk dst src⟩
def cmp_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨CmpR32Imm8.mk dst imm⟩
def cmp_r32_imm32 (dst : Reg32) (imm : UInt32) : AnyX86_64Instruction := ⟨CmpR32Imm32.mk dst imm⟩
def cmp_r16 (dst src : Reg16) : AnyX86_64Instruction := ⟨CmpR16R16.mk dst src⟩
def cmp_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨CmpR16Imm8.mk dst imm⟩
def cmp_r16_imm16 (dst : Reg16) (imm : UInt16) : AnyX86_64Instruction := ⟨CmpR16Imm16.mk dst imm⟩
def cmp_r8 (dst src : Reg8) : AnyX86_64Instruction := ⟨CmpR8R8.mk dst src⟩
def cmp_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨CmpR8Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the CMP family: `0x39` (CMP r64/r32/r16), `0x38` (CMP r8), `0x80 /7` (CMP r8, imm8),
    `0x81 /7` (CMP imm32/imm16), and `0x83 /7` (CMP imm8). Errors for any other byte pattern. -/
def cmpTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, _, rexW, rexR, _, rexB, opcode, opOffset) =>
    if has0x66 then
      if opcode == 0x39 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, pos) =>
          let dst := codeToReg16 rm rexB
          let src := codeToReg16 reg rexR
          .ok (cmp_r16 dst src, pos - offset)
      else if opcode == 0x83 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          if reg == 7 then
            let dst := codeToReg16 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (cmp_r16_imm8 dst imm8, (modPos + 1) - offset)
          else .error "cmpTryDecode: 0x83 sub-opcode is not CMP"
      else if opcode == 0x81 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          if reg == 7 then
            let dst := codeToReg16 rm rexB
            match readUInt16LE bytes modPos with
            | .error e => .error e
            | .ok imm16 => .ok (cmp_r16_imm16 dst imm16, (modPos + 2) - offset)
          else .error "cmpTryDecode: 0x81 sub-opcode is not CMP"
      else .error s!"cmpTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} with 0x66 prefix is not CMP"
    else if opcode == 0x38 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg8 rm rexB
        let src := codeToReg8 reg rexR
        .ok (cmp_r8 dst src, pos - offset)
    else if opcode == 0x80 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 7 then
          let dst := codeToReg8 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 => .ok (cmp_r8_imm8 dst imm8, (modPos + 1) - offset)
        else .error "cmpTryDecode: 0x80 sub-opcode is not CMP"
    else if opcode == 0x39 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if rexW then
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (cmp_r64 dst src, pos - offset)
        else
          let dst := codeToReg32 rm rexB
          let src := codeToReg32 reg rexR
          .ok (cmp_r32 dst src, pos - offset)
    else if opcode == 0x81 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 7 then
          if rexW then
            let dst := codeToReg64 rm rexB
            match readUInt32LE bytes modPos with
            | .error e => .error e
            | .ok imm32 => .ok (cmp_r64_imm32 dst imm32, (modPos + 4) - offset)
          else
            let dst := codeToReg32 rm rexB
            match readUInt32LE bytes modPos with
            | .error e => .error e
            | .ok imm32 => .ok (cmp_r32_imm32 dst imm32, (modPos + 4) - offset)
        else .error "cmpTryDecode: 0x81 sub-opcode is not CMP"
    else if opcode == 0x83 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 7 then
          if rexW then
            let dst := codeToReg64 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (cmp_r64_imm8 dst imm8, (modPos + 1) - offset)
          else
            let dst := codeToReg32 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (cmp_r32_imm8 dst imm8, (modPos + 1) - offset)
        else .error "cmpTryDecode: 0x83 sub-opcode is not CMP"
    else
      .error s!"cmpTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not CMP"

end Gasm.Targets.X86_64.Instructions

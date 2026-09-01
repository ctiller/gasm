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

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r64, r64: Computes bitwise logical AND between two 64-bit registers, sets condition flags (ZF, SF, PF), clears CF and OF, without modifying registers. -/
structure TestR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x85, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic64 temp
    { s' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, {i.src}"
  toLean i := s!"test_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (TestR64R64.mk · .rax)) ++ (allReg64List.map (TestR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => TestR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r64, imm32: Computes bitwise logical AND between 64-bit register and sign-extended 32-bit immediate, sets condition flags without modifying registers. -/
structure TestR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xF7, makeModRM 3 0 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic64 temp
    { s' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"test_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (TestR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (TestR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (TestR64Imm32.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r32, r32: Computes bitwise logical AND between 32-bit registers, sets condition flags without modifying registers. -/
structure TestR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexNeeded := dstExt || srcExt
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x85, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := s.readGpr32 i.src
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic32 temp
    let len := (if (reg32Code i.dst).2 || (reg32Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, {i.src}"
  toLean i := s!"test_r32 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (TestR32R32.mk · .eax)) ++ (allReg32List.map (TestR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => TestR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r32, imm32: Computes bitwise logical AND between 32-bit register and 32-bit immediate, sets condition flags without modifying registers. -/
structure TestR32Imm32 where
  dst : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR32Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xF7, makeModRM 3 0 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := i.imm
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic32 temp
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 6
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"test_r32_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (TestR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (TestR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (TestR32Imm32.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r16, r16: Computes bitwise logical AND between 16-bit registers, sets condition flags without modifying registers. -/
structure TestR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexNeeded := dstExt || srcExt
    let rexBytes := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x85, makeModRM 3 srcCode dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic16 temp
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, {i.src}"
  toLean i := s!"test_r16 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (TestR16R16.mk · .ax)) ++ (allReg16List.map (TestR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => TestR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r16, imm16: Computes bitwise logical AND between 16-bit register and 16-bit immediate, sets condition flags without modifying registers. -/
structure TestR16Imm16 where
  dst : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR16Imm16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0xF7, makeModRM 3 0 dstCode]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := i.imm
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic16 temp
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 4
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, word {i.imm.toNat}"
  toLean i := s!"test_r16_imm16 .{i.dst} {formatHex16 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (TestR16Imm16.mk · 0x0000)) ++ (curatedUInt16Cases.map (TestR16Imm16.mk .ax ·)) ++
    (curatedUInt16Cases.map (TestR16Imm16.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r8, r8: Computes bitwise logical AND between 8-bit registers, sets condition flags without modifying registers. -/
structure TestR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x84, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := s.readGpr8 i.src
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic8 temp
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, {i.src}"
  toLean i := s!"test_r8 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (TestR8R8.mk · .al)) ++ (allReg8List.map (TestR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => TestR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r8, imm8: Computes bitwise logical AND between 8-bit register and 8-bit immediate, sets condition flags without modifying registers. -/
structure TestR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xF6, makeModRM 3 0 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := i.imm
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic8 temp
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"test_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (TestR8Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (TestR8Imm8.mk .al ·)) ++
    (curatedUInt8Cases.map (TestR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- TEST r64, r64 helper. -/
def test_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨TestR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- TEST r64, imm32 helper. -/
def test_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨TestR64Imm32.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def test_r32 (dst src : Reg32) : AnyX86_64Instruction := ⟨TestR32R32.mk dst src⟩
def test_r32_imm32 (dst : Reg32) (imm : UInt32) : AnyX86_64Instruction := ⟨TestR32Imm32.mk dst imm⟩
def test_r16 (dst src : Reg16) : AnyX86_64Instruction := ⟨TestR16R16.mk dst src⟩
def test_r16_imm16 (dst : Reg16) (imm : UInt16) : AnyX86_64Instruction := ⟨TestR16Imm16.mk dst imm⟩
def test_r8 (dst src : Reg8) : AnyX86_64Instruction := ⟨TestR8R8.mk dst src⟩
def test_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨TestR8Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
def testDecodeRules : List DecodeRule := [
  -- 0x85 (reg, reg)
  { opcode := .one 0x85, has0x66 := some true,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r16"
      | some m =>
        let dst := codeToReg16 m.rm ctx.rexB
        let src := codeToReg16 m.reg ctx.rexR
        .ok (test_r16 dst src, m.pos - ctx.startOffset) },
  { opcode := .one 0x85, has0x66 := some false, rexW := some true,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r64"
      | some m =>
        let dst := codeToReg64 m.rm ctx.rexB
        let src := codeToReg64 m.reg ctx.rexR
        .ok (test_r64 dst src, m.pos - ctx.startOffset) },
  { opcode := .one 0x85, has0x66 := some false, rexW := some false,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r32"
      | some m =>
        let dst := codeToReg32 m.rm ctx.rexB
        let src := codeToReg32 m.reg ctx.rexR
        .ok (test_r32 dst src, m.pos - ctx.startOffset) },
  -- 0x84 (r8, r8)
  { opcode := .one 0x84, has0x66 := some false,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r8"
      | some m =>
        let dst := codeToReg8 m.rm ctx.rexB
        let src := codeToReg8 m.reg ctx.rexR
        .ok (test_r8 dst src, m.pos - ctx.startOffset) },
  -- 0xF6 /0 (r8, imm8)
  { opcode := .one 0xF6, has0x66 := some false, modrmReg := some 0,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r8_imm8"
      | some m =>
        match readUInt8 ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm8 =>
          let dst := codeToReg8 m.rm ctx.rexB
          .ok (test_r8_imm8 dst imm8, (m.pos + 1) - ctx.startOffset) },
  -- 0xF7 /0 (imm)
  { opcode := .one 0xF7, has0x66 := some true, modrmReg := some 0,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r16_imm16"
      | some m =>
        match readUInt16LE ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm16 =>
          let dst := codeToReg16 m.rm ctx.rexB
          .ok (test_r16_imm16 dst imm16, (m.pos + 2) - ctx.startOffset) },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some true, modrmReg := some 0,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r64_imm32"
      | some m =>
        match readUInt32LE ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm32 =>
          let dst := codeToReg64 m.rm ctx.rexB
          .ok (test_r64_imm32 dst imm32, (m.pos + 4) - ctx.startOffset) },
  { opcode := .one 0xF7, has0x66 := some false, rexW := some false, modrmReg := some 0,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "test_r32_imm32"
      | some m =>
        match readUInt32LE ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm32 =>
          let dst := codeToReg32 m.rm ctx.rexB
          .ok (test_r32_imm32 dst imm32, (m.pos + 4) - ctx.startOffset) }
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the TEST family, evaluating its declarative rules. -/
def testTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules testDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions

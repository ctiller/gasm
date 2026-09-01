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

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR reg32, reg32 instruction: clears/xors general-purpose register. -/
structure XorR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexNeeded := dstExt || srcExt
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x31, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := (s.gprs (reg32To64 i.dst)).toUInt32
    let sVal := (s.gprs (reg32To64 i.src)).toUInt32
    let res := dVal ^^^ sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic 32 res.toUInt64
    let len := if (reg32Code i.dst).2 || (reg32Code i.src).2 then 3 else 2
    { s' with rip := s.rip + len }
  toUops i :=
    if i.dst == i.src then
      -- Zeroing idiom: eliminated in the Rename stage with 0 execution latency and 0 execution port allocation
      [{ mnemonic := "XOR.zeroing", uopClass := .intALU, eligiblePorts := [], latencyCycles := 0, reciprocalThroughput := 0.0 }]
    else
      [{ mnemonic := "XOR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, {i.src}"
  toLean i := s!"xor_r32 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (XorR32R32.mk · .eax)) ++ (allReg32List.map (XorR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => XorR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r64, r64: Bitwise exclusive OR between destination and source 64-bit registers. -/
structure XorR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x31, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let res := dVal ^^^ sVal
    let s' := (s.setGpr64 i.dst res).setFlagsLogic64 res
    { s' with rip := s.rip + 3 }
  toUops i :=
    if i.dst == i.src then
      [{ mnemonic := "XOR.zeroing", uopClass := .intALU, eligiblePorts := [], latencyCycles := 0, reciprocalThroughput := 0.0 }]
    else
      [{ mnemonic := "XOR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, {i.src}"
  toLean i := s!"xor_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (XorR64R64.mk · .rax)) ++ (allReg64List.map (XorR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => XorR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r64, imm8: Bitwise exclusive OR between destination 64-bit register and sign-extended 8-bit immediate. -/
structure XorR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x83, makeModRM 3 6 dstCode, i.imm]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtend8To64 i.imm
    let res := dVal ^^^ sVal
    let s' := (s.setGpr64 i.dst res).setFlagsLogic64 res
    { s' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "XOR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"xor_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (XorR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (XorR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (XorR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r64, imm32: Bitwise exclusive OR between destination 64-bit register and sign-extended 32-bit immediate. -/
structure XorR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x81, makeModRM 3 6 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let res := dVal ^^^ sVal
    let s' := (s.setGpr64 i.dst res).setFlagsLogic64 res
    { s' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "XOR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"xor_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (XorR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (XorR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (XorR64Imm32.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r32, imm8: Bitwise exclusive OR between 32-bit register and sign-extended 8-bit immediate. -/
structure XorR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x83, makeModRM 3 6 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt32
    let res := dVal ^^^ sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic32 res
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"xor_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (XorR32Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (XorR32Imm8.mk .eax ·)) ++
    (curatedUInt8Cases.map (XorR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r32, imm32: Bitwise exclusive OR between 32-bit register and 32-bit immediate. -/
structure XorR32Imm32 where
  dst : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR32Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x81, makeModRM 3 6 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := i.imm
    let res := dVal ^^^ sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic32 res
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 6
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"xor_r32_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (XorR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (XorR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (XorR32Imm32.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r16, r16: Bitwise exclusive OR between 16-bit registers, preserving upper 48 bits. -/
structure XorR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexNeeded := dstExt || srcExt
    let rexBytes := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x31, makeModRM 3 srcCode dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let res := dVal ^^^ sVal
    let s' := (s.setGpr16 i.dst res).setFlagsLogic16 res
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, {i.src}"
  toLean i := s!"xor_r16 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (XorR16R16.mk · .ax)) ++ (allReg16List.map (XorR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => XorR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r16, imm8: Bitwise exclusive OR between 16-bit register and sign-extended 8-bit immediate. -/
structure XorR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x83, makeModRM 3 6 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt16
    let res := dVal ^^^ sVal
    let s' := (s.setGpr16 i.dst res).setFlagsLogic16 res
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"xor_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (XorR16Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (XorR16Imm8.mk .ax ·)) ++
    (curatedUInt8Cases.map (XorR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r16, imm16: Bitwise exclusive OR between 16-bit register and 16-bit immediate. -/
structure XorR16Imm16 where
  dst : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR16Imm16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x81, makeModRM 3 6 dstCode]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := i.imm
    let res := dVal ^^^ sVal
    let s' := (s.setGpr16 i.dst res).setFlagsLogic16 res
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 4
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, word {i.imm.toNat}"
  toLean i := s!"xor_r16_imm16 .{i.dst} {formatHex16 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (XorR16Imm16.mk · 0x0000)) ++ (curatedUInt16Cases.map (XorR16Imm16.mk .ax ·)) ++
    (curatedUInt16Cases.map (XorR16Imm16.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r8, r8: Bitwise exclusive OR between 8-bit registers, preserving upper 56 bits. -/
structure XorR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x30, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := s.readGpr8 i.src
    let res := dVal ^^^ sVal
    let s' := (s.setGpr8 i.dst res).setFlagsLogic8 res
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, {i.src}"
  toLean i := s!"xor_r8 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (XorR8R8.mk · .al)) ++ (allReg8List.map (XorR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => XorR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR r8, imm8: Bitwise exclusive OR between 8-bit register and 8-bit immediate. -/
structure XorR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x80, makeModRM 3 6 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := i.imm
    let res := dVal ^^^ sVal
    let s' := (s.setGpr8 i.dst res).setFlagsLogic8 res
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "XOR.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"xor_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (XorR8Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (XorR8Imm8.mk .al ·)) ++
    (curatedUInt8Cases.map (XorR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XOR reg64, reg64 helper. -/
def xor_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨XorR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XOR reg64, imm8 helper. -/
def xor_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨XorR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XOR reg64, imm32 helper. -/
def xor_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨XorR64Imm32.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XOR reg32, reg32 helper. -/
def xor_r32 (dst src : Reg32) : AnyX86_64Instruction :=
  ⟨XorR32R32.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def xor_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨XorR32Imm8.mk dst imm⟩
def xor_r32_imm32 (dst : Reg32) (imm : UInt32) : AnyX86_64Instruction := ⟨XorR32Imm32.mk dst imm⟩
def xor_r16 (dst src : Reg16) : AnyX86_64Instruction := ⟨XorR16R16.mk dst src⟩
def xor_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨XorR16Imm8.mk dst imm⟩
def xor_r16_imm16 (dst : Reg16) (imm : UInt16) : AnyX86_64Instruction := ⟨XorR16Imm16.mk dst imm⟩
def xor_r8 (dst src : Reg8) : AnyX86_64Instruction := ⟨XorR8R8.mk dst src⟩
def xor_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨XorR8Imm8.mk dst imm⟩

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
/-- The 64-bit zeroing idiom clears the destination register. -/
theorem XorR64R64.step_self_gpr (dst : Reg64) (state : X86_64MachineState) :
    (X86_64Instruction.step (XorR64R64.mk dst dst) state).gprs dst = 0 := by
  cases dst <;>
    simp only [X86_64Instruction.step] <;>
    simp [X86_64MachineState.setGpr64, X86_64MachineState.setFlagsLogic64, X86_64MachineState.setFlagsLogic]

theorem xor_r64_self_step_gpr (dst : Reg64) (state : X86_64MachineState) :
    (X86_64Instruction.step (xor_r64 dst dst) state).gprs dst = 0 := by
  change (X86_64Instruction.step (XorR64R64.mk dst dst)
    { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }).gprs dst = 0
  exact XorR64R64.step_self_gpr dst _

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
/-- The core architectural zeroing idiom clears the full 64-bit register because a 32-bit
    destination write is zero-extending. -/
theorem XorR32R32.step_self_gpr (dst : Reg32) (state : X86_64MachineState) :
    (X86_64Instruction.step (XorR32R32.mk dst dst) state).gprs (reg32To64 dst) = 0 := by
  cases dst <;>
    simp only [X86_64Instruction.step] <;>
    simp [X86_64MachineState.setGpr32, X86_64MachineState.setFlagsLogic, reg32To64]

/-- The packaged architectural zeroing idiom has the same full-register result. -/
theorem xor_r32_self_step_gpr (dst : Reg32) (state : X86_64MachineState) :
    (X86_64Instruction.step (xor_r32 dst dst) state).gprs (reg32To64 dst) = 0 := by
  change (X86_64Instruction.step (XorR32R32.mk dst dst)
    { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }).gprs
      (reg32To64 dst) = 0
  exact XorR32R32.step_self_gpr dst _

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
def xorDecodeRules : List DecodeRule := [
  -- 0x31 (reg, reg)
  { opcode := .one 0x31, has0x66 := some true,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r16"
      | some m =>
        let dst := codeToReg16 m.rm ctx.rexB
        let src := codeToReg16 m.reg ctx.rexR
        .ok (xor_r16 dst src, m.pos - ctx.startOffset) },
  { opcode := .one 0x31, has0x66 := some false, rexW := some true,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r64"
      | some m =>
        let dst := codeToReg64 m.rm ctx.rexB
        let src := codeToReg64 m.reg ctx.rexR
        .ok (xor_r64 dst src, m.pos - ctx.startOffset) },
  { opcode := .one 0x31, has0x66 := some false, rexW := some false,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r32"
      | some m =>
        let dst := codeToReg32 m.rm ctx.rexB
        let src := codeToReg32 m.reg ctx.rexR
        .ok (xor_r32 dst src, m.pos - ctx.startOffset) },
  -- 0x30 (r8, r8)
  { opcode := .one 0x30, has0x66 := some false,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r8"
      | some m =>
        let dst := codeToReg8 m.rm ctx.rexB
        let src := codeToReg8 m.reg ctx.rexR
        .ok (xor_r8 dst src, m.pos - ctx.startOffset) },
  -- 0x80 /6 (r8, imm8)
  { opcode := .one 0x80, has0x66 := some false, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r8_imm8"
      | some m =>
        match readUInt8 ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm8 =>
          let dst := codeToReg8 m.rm ctx.rexB
          .ok (xor_r8_imm8 dst imm8, (m.pos + 1) - ctx.startOffset) },
  -- 0x81 /6 (imm)
  { opcode := .one 0x81, has0x66 := some true, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r16_imm16"
      | some m =>
        match readUInt16LE ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm16 =>
          let dst := codeToReg16 m.rm ctx.rexB
          .ok (xor_r16_imm16 dst imm16, (m.pos + 2) - ctx.startOffset) },
  { opcode := .one 0x81, has0x66 := some false, rexW := some true, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r64_imm32"
      | some m =>
        match readUInt32LE ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm32 =>
          let dst := codeToReg64 m.rm ctx.rexB
          .ok (xor_r64_imm32 dst imm32, (m.pos + 4) - ctx.startOffset) },
  { opcode := .one 0x81, has0x66 := some false, rexW := some false, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r32_imm32"
      | some m =>
        match readUInt32LE ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm32 =>
          let dst := codeToReg32 m.rm ctx.rexB
          .ok (xor_r32_imm32 dst imm32, (m.pos + 4) - ctx.startOffset) },
  -- 0x83 /6 (imm8)
  { opcode := .one 0x83, has0x66 := some true, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r16_imm8"
      | some m =>
        match readUInt8 ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm8 =>
          let dst := codeToReg16 m.rm ctx.rexB
          .ok (xor_r16_imm8 dst imm8, (m.pos + 1) - ctx.startOffset) },
  { opcode := .one 0x83, has0x66 := some false, rexW := some true, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r64_imm8"
      | some m =>
        match readUInt8 ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm8 =>
          let dst := codeToReg64 m.rm ctx.rexB
          .ok (xor_r64_imm8 dst imm8, (m.pos + 1) - ctx.startOffset) },
  { opcode := .one 0x83, has0x66 := some false, rexW := some false, modrmReg := some 6,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xor_r32_imm8"
      | some m =>
        match readUInt8 ctx.bytes m.pos with
        | .error e => .error e
        | .ok imm8 =>
          let dst := codeToReg32 m.rm ctx.rexB
          .ok (xor_r32_imm8 dst imm8, (m.pos + 1) - ctx.startOffset) }
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the XOR family, evaluating its declarative rules. -/
def xorTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules xorDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions

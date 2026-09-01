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

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND reg64, imm8 instruction: bitwise AND with sign-extended 8-bit immediate. -/
structure AndR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let rex := makeRex true false false dstExt
    let modrm := makeModRM 3 4 dstCode
    ByteArray.mk #[rex, 0x83, modrm, i.imm]
  step i s :=
    let imm64 := signExtend8To64 i.imm
    let res := s.gprs i.dst &&& imm64
    let s' := (s.setGpr64 i.dst res).setFlagsLogic64 res
    { s' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "AND.r64_imm8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  -- `byte` qualifier is load-bearing, not decorative (found via P4(a)'s registry-derived
  -- encoding fuzzer, docs/X86_ISA_EXPANSION_PREREQUISITES.md, on the `curatedUInt8Cases` 0xFF
  -- witness): without it, a bare "0xff" is a POSITIVE literal (255) to NASM, which does not fit
  -- signed imm8 range (-128..127), so NASM falls back to the general `81 /4 id` (imm32) encoding
  -- instead of the `83 /4 ib` (sign-extended imm8) form `encode` always emits -- even though
  -- `AndR64Imm8` is the only registered AND-with-immediate type, AND still has a real, valid
  -- `81 /4 id` opcode NASM can and does reach for. Same root cause as `AddR64Imm8`/`AddRspImm8`'s
  -- pre-existing `byte` qualifier; this form was simply never NASM-cross-checked before the
  -- registry-derived generator existed.
  toNASM i := s!"and {i.dst}, byte 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"and_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (AndR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AndR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (AndR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND reg64, reg64 instruction: bitwise AND between 64-bit registers. -/
structure AndR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    let rex := makeRex true srcExt false dstExt
    let modrm := makeModRM 3 srcCode dstCode
    ByteArray.mk #[rex, 0x21, modrm]
  step i s :=
    let res := s.gprs i.dst &&& s.gprs i.src
    let s' := (s.setGpr64 i.dst res).setFlagsLogic64 res
    { s' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "AND.r64_r64", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, {i.src}"
  toLean i := s!"and_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (AndR64R64.mk · .rax)) ++ (allReg64List.map (AndR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => AndR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r64, imm32: Bitwise AND between 64-bit destination register and sign-extended 32-bit immediate. -/
structure AndR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x81, makeModRM 3 4 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let res := dVal &&& sVal
    let s' := (s.setGpr64 i.dst res).setFlagsLogic64 res
    { s' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "AND.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"and_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (AndR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (AndR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (AndR64Imm32.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r32, r32: Bitwise AND between 32-bit registers with 64-bit zero-extension. -/
structure AndR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexNeeded := dstExt || srcExt
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x21, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := s.readGpr32 i.src
    let res := dVal &&& sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic32 res
    let len := (if (reg32Code i.dst).2 || (reg32Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, {i.src}"
  toLean i := s!"and_r32 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (AndR32R32.mk · .eax)) ++ (allReg32List.map (AndR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => AndR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r32, imm8: Bitwise AND between 32-bit register and sign-extended 8-bit immediate. -/
structure AndR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x83, makeModRM 3 4 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt32
    let res := dVal &&& sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic32 res
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"and_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (AndR32Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AndR32Imm8.mk .eax ·)) ++
    (curatedUInt8Cases.map (AndR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r32, imm32: Bitwise AND between 32-bit register and 32-bit immediate. -/
structure AndR32Imm32 where
  dst : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR32Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x81, makeModRM 3 4 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := i.imm
    let res := dVal &&& sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic32 res
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 6
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"and_r32_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (AndR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (AndR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (AndR32Imm32.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r16, r16: Bitwise AND between 16-bit registers, preserving upper 48 bits. -/
structure AndR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexNeeded := dstExt || srcExt
    let rexBytes := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x21, makeModRM 3 srcCode dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let res := dVal &&& sVal
    let s' := (s.setGpr16 i.dst res).setFlagsLogic16 res
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, {i.src}"
  toLean i := s!"and_r16 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (AndR16R16.mk · .ax)) ++ (allReg16List.map (AndR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => AndR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r16, imm8: Bitwise AND between 16-bit register and sign-extended 8-bit immediate. -/
structure AndR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x83, makeModRM 3 4 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt16
    let res := dVal &&& sVal
    let s' := (s.setGpr16 i.dst res).setFlagsLogic16 res
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"and_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (AndR16Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AndR16Imm8.mk .ax ·)) ++
    (curatedUInt8Cases.map (AndR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r16, imm16: Bitwise AND between 16-bit register and 16-bit immediate. -/
structure AndR16Imm16 where
  dst : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR16Imm16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x81, makeModRM 3 4 dstCode]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := i.imm
    let res := dVal &&& sVal
    let s' := (s.setGpr16 i.dst res).setFlagsLogic16 res
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 4
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, word {i.imm.toNat}"
  toLean i := s!"and_r16_imm16 .{i.dst} {formatHex16 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (AndR16Imm16.mk · 0x0000)) ++ (curatedUInt16Cases.map (AndR16Imm16.mk .ax ·)) ++
    (curatedUInt16Cases.map (AndR16Imm16.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r8, r8: Bitwise AND between 8-bit registers, preserving upper 56 bits. -/
structure AndR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x20, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := s.readGpr8 i.src
    let res := dVal &&& sVal
    let s' := (s.setGpr8 i.dst res).setFlagsLogic8 res
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, {i.src}"
  toLean i := s!"and_r8 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (AndR8R8.mk · .al)) ++ (allReg8List.map (AndR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => AndR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=AND;part=description -/
/-- AND r8, imm8: Bitwise AND between 8-bit register and 8-bit immediate. -/
structure AndR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=AND;part=operation -/
instance : X86_64Instruction AndR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x80, makeModRM 3 4 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := i.imm
    let res := dVal &&& sVal
    let s' := (s.setGpr8 i.dst res).setFlagsLogic8 res
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "AND.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"and {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"and_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (AndR8Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AndR8Imm8.mk .al ·)) ++
    (curatedUInt8Cases.map (AndR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, imm8 helper. -/
def and_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨AndR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, reg64 helper. -/
def and_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨AndR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def and_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction := ⟨AndR64Imm32.mk dst imm⟩
def and_r32 (dst src : Reg32) : AnyX86_64Instruction := ⟨AndR32R32.mk dst src⟩
def and_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨AndR32Imm8.mk dst imm⟩
def and_r32_imm32 (dst : Reg32) (imm : UInt32) : AnyX86_64Instruction := ⟨AndR32Imm32.mk dst imm⟩
def and_r16 (dst src : Reg16) : AnyX86_64Instruction := ⟨AndR16R16.mk dst src⟩
def and_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨AndR16Imm8.mk dst imm⟩
def and_r16_imm16 (dst : Reg16) (imm : UInt16) : AnyX86_64Instruction := ⟨AndR16Imm16.mk dst imm⟩
def and_r8 (dst src : Reg8) : AnyX86_64Instruction := ⟨AndR8R8.mk dst src⟩
def and_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨AndR8Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the AND family: `0x21` (AND r64/r32/r16), `0x20` (AND r8), `0x80 /4` (AND r8, imm8),
    `0x81 /4` (AND imm32/imm16), and `0x83 /4` (AND imm8). Errors for any other byte pattern. -/
def andTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, _, rexW, rexR, _, rexB, opcode, opOffset) =>
    if has0x66 then
      if opcode == 0x21 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, pos) =>
          let dst := codeToReg16 rm rexB
          let src := codeToReg16 reg rexR
          .ok (and_r16 dst src, pos - offset)
      else if opcode == 0x83 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          if reg == 4 then
            let dst := codeToReg16 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (and_r16_imm8 dst imm8, (modPos + 1) - offset)
          else .error "andTryDecode: 0x83 sub-opcode is not AND"
      else if opcode == 0x81 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          if reg == 4 then
            let dst := codeToReg16 rm rexB
            match readUInt16LE bytes modPos with
            | .error e => .error e
            | .ok imm16 => .ok (and_r16_imm16 dst imm16, (modPos + 2) - offset)
          else .error "andTryDecode: 0x81 sub-opcode is not AND"
      else .error s!"andTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} with 0x66 prefix is not AND"
    else if opcode == 0x20 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg8 rm rexB
        let src := codeToReg8 reg rexR
        .ok (and_r8 dst src, pos - offset)
    else if opcode == 0x80 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 4 then
          let dst := codeToReg8 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 => .ok (and_r8_imm8 dst imm8, (modPos + 1) - offset)
        else .error "andTryDecode: 0x80 sub-opcode is not AND"
    else if opcode == 0x21 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if rexW then
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (and_r64 dst src, pos - offset)
        else
          let dst := codeToReg32 rm rexB
          let src := codeToReg32 reg rexR
          .ok (and_r32 dst src, pos - offset)
    else if opcode == 0x81 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 4 then
          if rexW then
            let dst := codeToReg64 rm rexB
            match readUInt32LE bytes modPos with
            | .error e => .error e
            | .ok imm32 => .ok (and_r64_imm32 dst imm32, (modPos + 4) - offset)
          else
            let dst := codeToReg32 rm rexB
            match readUInt32LE bytes modPos with
            | .error e => .error e
            | .ok imm32 => .ok (and_r32_imm32 dst imm32, (modPos + 4) - offset)
        else .error "andTryDecode: 0x81 sub-opcode is not AND"
    else if opcode == 0x83 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 4 then
          if rexW then
            let dst := codeToReg64 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (and_r64_imm8 dst imm8, (modPos + 1) - offset)
          else
            let dst := codeToReg32 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (and_r32_imm8 dst imm8, (modPos + 1) - offset)
        else .error "andTryDecode: 0x83 sub-opcode is not AND"
    else
      .error s!"andTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not AND"

end Gasm.Targets.X86_64.Instructions

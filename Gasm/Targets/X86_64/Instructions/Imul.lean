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

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r64, r64: Signed two-operand 64-bit integer multiplication with 64-bit result, setting CF and OF on signed truncation. -/
structure ImulR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0xAF, makeModRM 3 dstCode srcCode]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let res := dVal * sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsImul64 dVal sVal
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}"
  toLean i := s!"imul_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 0xD4 -- PF, AF, ZF, SF are undefined according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (ImulR64R64.mk · .rax)) ++ (allReg64List.map (ImulR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => ImulR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r64, r64 helper. -/
def imul_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨ImulR64R64.mk dst src⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r32, r32: Signed two-operand 32-bit integer multiplication with 32-bit result and 64-bit zero extension. -/
structure ImulR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexBytes := if dstExt || srcExt then #[makeRex false dstExt false srcExt] else #[]
    ByteArray.mk (rexBytes ++ #[0x0F, 0xAF, makeModRM 3 dstCode srcCode])
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := s.readGpr32 i.src
    let res := dVal * sVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsImul32 dVal sVal
    let rexNeeded := (reg32Code i.dst).2 || (reg32Code i.src).2
    let len := (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}"
  toLean i := s!"imul_r32 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (ImulR32R32.mk · .eax)) ++ (allReg32List.map (ImulR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => ImulR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r32, r32 helper. -/
def imul_r32 (dst src : Reg32) : AnyX86_64Instruction :=
  ⟨ImulR32R32.mk dst src⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r16, r16: Signed two-operand 16-bit integer multiplication preserving upper 48 bits of destination. -/
structure ImulR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexBytes := if dstExt || srcExt then #[makeRex false dstExt false srcExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x0F, 0xAF, makeModRM 3 dstCode srcCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let res := dVal * sVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsImul16 dVal sVal
    let rexNeeded := (reg16Code i.dst).2 || (reg16Code i.src).2
    let len := 1 + (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}"
  toLean i := s!"imul_r16 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (ImulR16R16.mk · .ax)) ++ (allReg16List.map (ImulR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => ImulR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r16, r16 helper. -/
def imul_r16 (dst src : Reg16) : AnyX86_64Instruction :=
  ⟨ImulR16R16.mk dst src⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r64, r64, imm32: Signed three-operand multiplication of 64-bit source by sign-extended 32-bit immediate. -/
structure ImulR64R64Imm32 where
  dst : Reg64
  src : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR64R64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x69, makeModRM 3 dstCode srcCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let sVal := s.gprs i.src
    let immVal := signExtendUInt32To64 i.imm
    let res := sVal * immVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsImul64 sVal immVal
    { s'' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}, dword {i.imm.toNat}"
  toLean i := s!"imul_r64_r64_imm32 .{i.dst} .{i.src} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (ImulR64R64Imm32.mk · .rax 0x00000000)) ++
    (allReg64List.map (ImulR64R64Imm32.mk .rax · 0x00000000)) ++
    (curatedUInt32Cases.map (ImulR64R64Imm32.mk .rax .rcx ·)) ++
    (extendedReg64Pairs.map fun p => ImulR64R64Imm32.mk p.1 p.2 0x7FFFFFFF)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r64, r64, imm32 helper. -/
def imul_r64_r64_imm32 (dst src : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨ImulR64R64Imm32.mk dst src imm⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r64, r64, imm8: Signed three-operand multiplication of 64-bit source by sign-extended 8-bit immediate. -/
structure ImulR64R64Imm8 where
  dst : Reg64
  src : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR64R64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x6B, makeModRM 3 dstCode srcCode, i.imm]
  step i s :=
    let sVal := s.gprs i.src
    let immVal := signExtend8To64 i.imm
    let res := sVal * immVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsImul64 sVal immVal
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}, byte {i.imm.toNat}"
  toLean i := s!"imul_r64_r64_imm8 .{i.dst} .{i.src} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (ImulR64R64Imm8.mk · .rax 0x00)) ++
    (allReg64List.map (ImulR64R64Imm8.mk .rax · 0x00)) ++
    (curatedUInt8Cases.map (ImulR64R64Imm8.mk .rax .rcx ·)) ++
    (extendedReg64Pairs.map fun p => ImulR64R64Imm8.mk p.1 p.2 0x7F)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r64, r64, imm8 helper. -/
def imul_r64_r64_imm8 (dst src : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨ImulR64R64Imm8.mk dst src imm⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r32, r32, imm32: Signed three-operand multiplication of 32-bit source by 32-bit immediate with 64-bit zero extension. -/
structure ImulR32R32Imm32 where
  dst : Reg32
  src : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR32R32Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexBytes := if dstExt || srcExt then #[makeRex false dstExt false srcExt] else #[]
    ByteArray.mk (rexBytes ++ #[0x69, makeModRM 3 dstCode srcCode]) ++ uint32ToLittleEndian i.imm
  step i s :=
    let sVal := s.readGpr32 i.src
    let immVal := i.imm
    let res := sVal * immVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsImul32 sVal immVal
    let rexNeeded := (reg32Code i.dst).2 || (reg32Code i.src).2
    let len := (if rexNeeded then 1 else 0) + 6
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}, dword {i.imm.toNat}"
  toLean i := s!"imul_r32_r32_imm32 .{i.dst} .{i.src} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (ImulR32R32Imm32.mk · .eax 0x00000000)) ++
    (allReg32List.map (ImulR32R32Imm32.mk .eax · 0x00000000)) ++
    (curatedUInt32Cases.map (ImulR32R32Imm32.mk .eax .ecx ·)) ++
    (extendedReg32Pairs.map fun p => ImulR32R32Imm32.mk p.1 p.2 0x7FFFFFFF)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r32, r32, imm32 helper. -/
def imul_r32_r32_imm32 (dst src : Reg32) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨ImulR32R32Imm32.mk dst src imm⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r32, r32, imm8: Signed three-operand multiplication of 32-bit source by sign-extended 8-bit immediate with 64-bit zero extension. -/
structure ImulR32R32Imm8 where
  dst : Reg32
  src : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR32R32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexBytes := if dstExt || srcExt then #[makeRex false dstExt false srcExt] else #[]
    ByteArray.mk (rexBytes ++ #[0x6B, makeModRM 3 dstCode srcCode, i.imm])
  step i s :=
    let sVal := s.readGpr32 i.src
    let immVal := (signExtend8To64 i.imm).toUInt32
    let res := sVal * immVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsImul32 sVal immVal
    let rexNeeded := (reg32Code i.dst).2 || (reg32Code i.src).2
    let len := (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}, byte {i.imm.toNat}"
  toLean i := s!"imul_r32_r32_imm8 .{i.dst} .{i.src} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (ImulR32R32Imm8.mk · .eax 0x00)) ++
    (allReg32List.map (ImulR32R32Imm8.mk .eax · 0x00)) ++
    (curatedUInt8Cases.map (ImulR32R32Imm8.mk .eax .ecx ·)) ++
    (extendedReg32Pairs.map fun p => ImulR32R32Imm8.mk p.1 p.2 0x7F)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r32, r32, imm8 helper. -/
def imul_r32_r32_imm8 (dst src : Reg32) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨ImulR32R32Imm8.mk dst src imm⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r16, r16, imm16: Signed three-operand multiplication of 16-bit source by 16-bit immediate preserving upper 48 bits of destination. -/
structure ImulR16R16Imm16 where
  dst : Reg16
  src : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR16R16Imm16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexBytes := if dstExt || srcExt then #[makeRex false dstExt false srcExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x69, makeModRM 3 dstCode srcCode]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let sVal := s.readGpr16 i.src
    let immVal := i.imm
    let res := sVal * immVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsImul16 sVal immVal
    let rexNeeded := (reg16Code i.dst).2 || (reg16Code i.src).2
    let len := 1 + (if rexNeeded then 1 else 0) + 4
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}, word {i.imm.toNat}"
  toLean i := s!"imul_r16_r16_imm16 .{i.dst} .{i.src} {formatHex16 i.imm}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (ImulR16R16Imm16.mk · .ax 0x0000)) ++
    (allReg16List.map (ImulR16R16Imm16.mk .ax · 0x0000)) ++
    (curatedUInt16Cases.map (ImulR16R16Imm16.mk .ax .cx ·)) ++
    (extendedReg16Pairs.map fun p => ImulR16R16Imm16.mk p.1 p.2 0x7FFF)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r16, r16, imm16 helper. -/
def imul_r16_r16_imm16 (dst src : Reg16) (imm : UInt16) : AnyX86_64Instruction :=
  ⟨ImulR16R16Imm16.mk dst src imm⟩

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r16, r16, imm8: Signed three-operand multiplication of 16-bit source by sign-extended 8-bit immediate preserving upper 48 bits of destination. -/
structure ImulR16R16Imm8 where
  dst : Reg16
  src : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR16R16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexBytes := if dstExt || srcExt then #[makeRex false dstExt false srcExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x6B, makeModRM 3 dstCode srcCode, i.imm])
  step i s :=
    let sVal := s.readGpr16 i.src
    let immVal := (signExtend8To64 i.imm).toUInt16
    let res := sVal * immVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsImul16 sVal immVal
    let rexNeeded := (reg16Code i.dst).2 || (reg16Code i.src).2
    let len := 1 + (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}, byte {i.imm.toNat}"
  toLean i := s!"imul_r16_r16_imm8 .{i.dst} .{i.src} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 0xD4
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (ImulR16R16Imm8.mk · .ax 0x00)) ++
    (allReg16List.map (ImulR16R16Imm8.mk .ax · 0x00)) ++
    (curatedUInt8Cases.map (ImulR16R16Imm8.mk .ax .cx ·)) ++
    (extendedReg16Pairs.map fun p => ImulR16R16Imm8.mk p.1 p.2 0x7F)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r16, r16, imm8 helper. -/
def imul_r16_r16_imm8 (dst src : Reg16) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨ImulR16R16Imm8.mk dst src imm⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the IMUL family: `0x0F 0xAF` (2-operand), `0x69` (3-operand imm32/imm16),
    `0x6B` (3-operand imm8). -/
def imulTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, _, rexW, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x0F then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok 0xAF =>
        match readModRM bytes (opOffset + 1) with
        | .error e => .error e
        | .ok (mod, reg, rm, pos) =>
          if mod != 3 then .error "imulTryDecode: memory operand unsupported"
          else if has0x66 then
            .ok (imul_r16 (codeToReg16 reg rexR) (codeToReg16 rm rexB), pos - offset)
          else if rexW then
            .ok (imul_r64 (codeToReg64 reg rexR) (codeToReg64 rm rexB), pos - offset)
          else
            .ok (imul_r32 (codeToReg32 reg rexR) (codeToReg32 rm rexB), pos - offset)
      | .ok _ => .error "imulTryDecode: 0x0F sub-opcode is not IMUL"
    else if opcode == 0x69 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (mod, reg, rm, pos) =>
        if mod != 3 then .error "imulTryDecode: memory operand unsupported"
        else if has0x66 then
          match readUInt16LE bytes pos with
          | .error e => .error e
          | .ok imm => .ok (imul_r16_r16_imm16 (codeToReg16 reg rexR) (codeToReg16 rm rexB) imm, pos + 2 - offset)
        else
          match readUInt32LE bytes pos with
          | .error e => .error e
          | .ok imm =>
            if rexW then
              .ok (imul_r64_r64_imm32 (codeToReg64 reg rexR) (codeToReg64 rm rexB) imm, pos + 4 - offset)
            else
              .ok (imul_r32_r32_imm32 (codeToReg32 reg rexR) (codeToReg32 rm rexB) imm, pos + 4 - offset)
    else if opcode == 0x6B then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (mod, reg, rm, pos) =>
        if mod != 3 then .error "imulTryDecode: memory operand unsupported"
        else
          match readUInt8 bytes pos with
          | .error e => .error e
          | .ok imm =>
            if has0x66 then
              .ok (imul_r16_r16_imm8 (codeToReg16 reg rexR) (codeToReg16 rm rexB) imm, pos + 1 - offset)
            else if rexW then
              .ok (imul_r64_r64_imm8 (codeToReg64 reg rexR) (codeToReg64 rm rexB) imm, pos + 1 - offset)
            else
              .ok (imul_r32_r32_imm8 (codeToReg32 reg rexR) (codeToReg32 rm rexB) imm, pos + 1 - offset)
    else
      .error s!"imulTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not IMUL"

end Gasm.Targets.X86_64.Instructions

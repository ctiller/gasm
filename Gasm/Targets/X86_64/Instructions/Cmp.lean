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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (CmpR64R64.mk · .rax)) ++ (allReg64List.map (CmpR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => CmpR64R64.mk p.1 p.2)

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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (CmpR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (CmpR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (CmpR64Imm8.mk .r15 ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMP r64, r64 helper. -/
def cmp_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨CmpR64R64.mk dst src⟩

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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (CmpR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (CmpR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (CmpR64Imm32.mk .r15 ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CMP r64, imm32 helper. -/
def cmp_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨CmpR64Imm32.mk dst imm⟩

end Gasm.Targets.X86_64.Instructions

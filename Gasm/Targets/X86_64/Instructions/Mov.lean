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
import Gasm.Targets.X86_64.MemCostModel

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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (MovR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (MovR32Imm32.mk .r15d ·))
  memAccesses _ := []

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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    -- Uses the smaller curatedUInt64Cases (not the 17-element curated64BitValues, which is sized
    -- for fuzz-state generation) to bound this family's contribution to the MOV shard's `decide`
    -- elaboration cost — this was the single largest case list in the family that OOM'd once
    -- during a parallel 21-shard build (see docs/TARGETS/X86_64.md).
    (allReg64List.map (MovR64Imm64.mk · 0)) ++ (curatedUInt64Cases.map (MovR64Imm64.mk .rax ·)) ++
    (curatedUInt64Cases.map (MovR64Imm64.mk .r15 ·))
  memAccesses _ := []

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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (MovR64R64.mk · .rax)) ++ (allReg64List.map (MovR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg64, imm32: moves sign-extended 32-bit immediate into general-purpose register. -/
structure MovR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xC7, makeModRM 3 0 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let s' := s.setGpr64 i.dst (signExtendUInt32To64 i.imm)
    { s' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "MOV.imm32_to_64", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i :=
    if (i.imm &&& 0x80000000) != 0 then
      s!"mov {i.dst}, strict dword -0x{String.ofList (Nat.toDigits 16 (0 - i.imm).toNat)}"
    else
      s!"mov {i.dst}, strict dword 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (MovR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (MovR64Imm32.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg32, reg32 instruction: moves 32-bit register to 32-bit register with zero-extension to 64 bits. -/
structure MovR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexPrefix := if dstExt || srcExt then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x89, makeModRM 3 srcCode dstCode]
  step i s :=
    let sVal := s.readGpr32 i.src
    let s' := s.setGpr32 i.dst sVal
    let len := (if (reg32Code i.dst).2 || (reg32Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "MOV.reg32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, {i.src}"
  toLean i := s!"mov_r32_r32 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (MovR32R32.mk · .eax)) ++ (allReg32List.map (MovR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => MovR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg16, reg16 instruction: moves 16-bit register to 16-bit register, preserving upper 48 bits. -/
structure MovR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexPrefix := if dstExt || srcExt then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0x89, makeModRM 3 srcCode dstCode])
  step i s :=
    let sVal := s.readGpr16 i.src
    let s' := s.setGpr16 i.dst sVal
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "MOV.reg16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, {i.src}"
  toLean i := s!"mov_r16 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (MovR16R16.mk · .ax)) ++ (allReg16List.map (MovR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => MovR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg16, imm16: moves 16-bit immediate into 16-bit register, preserving upper 48 bits. -/
structure MovR16Imm16 where
  dst : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR16Imm16 where
  encode i :=
    let (code, isExt) := reg16Code i.dst
    let rexPrefix := if isExt then #[makeRex false false false true] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0xB8 + code]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let s' := s.setGpr16 i.dst i.imm
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "MOV.imm16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_r16_imm16 .{i.dst} {formatHex16 i.imm}"
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (MovR16Imm16.mk · 0x0000)) ++ (curatedUInt16Cases.map (MovR16Imm16.mk .ax ·)) ++
    (curatedUInt16Cases.map (MovR16Imm16.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg8, reg8 instruction: moves 8-bit register to 8-bit register, preserving upper 56 bits. -/
structure MovR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x88, makeModRM 3 srcCode dstCode]
  step i s :=
    let sVal := s.readGpr8 i.src
    let s' := s.setGpr8 i.dst sVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "MOV.reg8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, {i.src}"
  toLean i := s!"mov_r8 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (MovR8R8.mk · .al)) ++ (allReg8List.map (MovR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => MovR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV reg8, imm8: moves 8-bit immediate into 8-bit register, preserving upper 56 bits. -/
structure MovR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xB0 + dstCode, i.imm]
  step i s :=
    let s' := s.setGpr8 i.dst i.imm
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "MOV.imm8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"mov {i.dst}, 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (MovR8Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (MovR8Imm8.mk .al ·)) ++
    (curatedUInt8Cases.map (MovR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV BYTE PTR [RSP + disp8], val: writes an 8-bit immediate byte directly to stack offset. -/
structure MovRspDispByte where
  disp : UInt8
  val  : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `MovRspDispByte`'s declared memory access, hoisted to a top-level `def` and shared by both
    `memAccesses` and `toUops` below (via `memUops`) -- a typeclass instance's fields cannot
    reference one another during construction, so this is how "derive `toUops` from `memAccesses`"
    (`docs/MEMORY_HOOK.md` §5.1) is expressed without re-typing the descriptor literal twice
    (which would itself be exactly the Law-12 twin this hook exists to retire). Every one of the
    14 memory forms in this file/`Push.lean`/`Pop.lean`/`Call.lean`/`Ret.lean` follows this same
    shape. -/
@[simp] def movRspDispByteAccesses (i : MovRspDispByte) : List MemAccessSpec :=
  [⟨.store, .w8, ⟨some .rsp, none, signExtend8To64 i.disp⟩⟩]

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

  toUops i := derivedMemUops (movRspDispByteAccesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov byte [rsp], 0x{String.ofList (Nat.toDigits 16 i.val.toNat)}"
    else
      s!"mov byte [rsp {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.val.toNat)}"
  toLean i := s!"mov_rsp_byte {formatHex8 i.disp} {formatHex8 i.val}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (curatedUInt8Cases.map (MovRspDispByte.mk · 0x00)) ++ (curatedUInt8Cases.map (MovRspDispByte.mk 0x00 ·))
  memAccesses := movRspDispByteAccesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV DWORD PTR [RSP + disp8], imm32: writes a 32-bit immediate doubleword directly to stack offset. -/
structure MovRspDispImm32 where
  disp : UInt8
  imm  : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movRspDispImm32Accesses (i : MovRspDispImm32) : List MemAccessSpec :=
  [⟨.store, .w32, ⟨some .rsp, none, signExtend8To64 i.disp⟩⟩]

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
    let s' := s.write32 base i.imm
    { s' with rip := s.rip + len }

  toUops i := derivedMemUops (movRspDispImm32Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov dword [rsp], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
    else
      s!"mov dword [rsp {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_rsp32 {formatHex8 i.disp} {formatHex32 i.imm}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (curatedUInt8Cases.map (MovRspDispImm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovRspDispImm32.mk 0x00 ·))
  memAccesses := movRspDispImm32Accesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV QWORD PTR [RSP + disp8], imm32: sign-extends 32-bit immediate to 64 bits and writes to stack offset. -/
structure MovRspDispImm64 where
  disp : UInt8
  imm  : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movRspDispImm64Accesses (i : MovRspDispImm64) : List MemAccessSpec :=
  [⟨.store, .w64, ⟨some .rsp, none, signExtend8To64 i.disp⟩⟩]

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovRspDispImm64 where
  encode i :=
    if i.disp == 0 then
      ByteArray.mk #[makeRex true false false false, 0xC7, makeModRM 0 0 4, makeSIB 0 4 4] ++ uint32ToLittleEndian i.imm
    else
      ByteArray.mk #[makeRex true false false false, 0xC7, makeModRM 1 0 4, makeSIB 0 4 4, i.disp] ++ uint32ToLittleEndian i.imm

  step i s :=
    let base := s.rsp + signExtend8To64 i.disp
    let len := if i.disp == 0 then 8 else 9
    -- Sign-extending the 32-bit immediate to 64 bits first and issuing ONE 64-bit write
    -- produces byte-for-byte the same result as the old inline lambda (bytes 0-3 = imm's
    -- bytes, bytes 4-7 = a uniform 0xFF/0x00 extension byte derived from imm's sign bit):
    -- `signExtendUInt32To64` already builds exactly that 64-bit pattern.
    let s' := s.write64 base (signExtendUInt32To64 i.imm)
    { s' with rip := s.rip + len }

  toUops i := derivedMemUops (movRspDispImm64Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov qword [rsp], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
    else
      s!"mov qword [rsp {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_rsp64 {formatHex8 i.disp} {formatHex32 i.imm}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (curatedUInt8Cases.map (MovRspDispImm64.mk · 0x00000000)) ++ (curatedUInt32Cases.map (MovRspDispImm64.mk 0x00 ·))
  memAccesses := movRspDispImm64Accesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV [dstPtr], srcReg8: Writes the low 8-bit byte of srcReg into memory at [dstPtr]. -/
structure MovMem8Reg8 where
  dstPtr : Reg64
  srcReg : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movMem8Reg8Accesses (i : MovMem8Reg8) : List MemAccessSpec :=
  [⟨.store, .w8, ⟨some i.dstPtr, none, 0⟩⟩]

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

  toUops i := derivedMemUops (movMem8Reg8Accesses i) defaultMemCostModel
  toNASM i := s!"mov byte [{i.dstPtr}], {reg64To8BitString i.srcReg}"
  toLean i := s!"mov_mem8 .{i.dstPtr} .{i.srcReg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovMem8Reg8.mk · .rax)) ++ (allReg64List.map (MovMem8Reg8.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovMem8Reg8.mk p.1 p.2)
  memAccesses := movMem8Reg8Accesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV QWORD PTR [basePtr + disp8], srcReg64: Writes 64-bit register into memory at [basePtr + disp8]. -/
structure MovMem64DispReg64 where
  basePtr : Reg64
  disp    : UInt8
  srcReg  : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movMem64DispReg64Accesses (i : MovMem64DispReg64) : List MemAccessSpec :=
  [⟨.store, .w64, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

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

  toUops i := derivedMemUops (movMem64DispReg64Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov qword [{i.basePtr}], {i.srcReg}"
    else
      s!"mov qword [{i.basePtr} {formatDisp8 i.disp}], {i.srcReg}"
  toLean i := s!"mov_mem64_disp .{i.basePtr} {formatHex8 i.disp} .{i.srcReg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovMem64DispReg64.mk · 0 .rax)) ++
    (curatedUInt8Cases.map (MovMem64DispReg64.mk .rax · .rax)) ++
    (allReg64List.map (MovMem64DispReg64.mk .rax 0 ·)) ++
    (extendedReg64Pairs.map fun p => MovMem64DispReg64.mk p.1 0 p.2) ++
    (curatedUInt8Cases.map (MovMem64DispReg64.mk .r15 · .r15))
  memAccesses := movMem64DispReg64Accesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV DWORD PTR [basePtr + disp8], srcReg32: Writes the low 32 bits of the source register
    into exactly four memory bytes.  The upper half of the enclosing 64-bit register is not part
    of the store. -/
structure MovMem32DispReg32 where
  basePtr : Reg64
  disp    : UInt8
  srcReg  : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
@[simp] def movMem32DispReg32Accesses (i : MovMem32DispReg32) : List MemAccessSpec :=
  [⟨.store, .w32, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovMem32DispReg32 where
  encode i :=
    let (baseCode, baseExt) := reg64Code i.basePtr
    let (srcCode, srcExt) := reg32Code i.srcReg
    let rexPrefix :=
      if srcExt || baseExt then ByteArray.mk #[makeRex false srcExt false baseExt]
      else ByteArray.empty
    let body :=
      if i.disp == 0 && baseCode != 5 then
        if baseCode == 4 then
          ByteArray.mk #[0x89, makeModRM 0 srcCode 4, makeSIB 0 4 4]
        else
          ByteArray.mk #[0x89, makeModRM 0 srcCode baseCode]
      else
        if baseCode == 4 then
          ByteArray.mk #[0x89, makeModRM 1 srcCode 4, makeSIB 0 4 4, i.disp]
        else
          ByteArray.mk #[0x89, makeModRM 1 srcCode baseCode, i.disp]
    rexPrefix ++ body

  step i s :=
    let (baseCode, baseExt) := reg64Code i.basePtr
    let (_, srcExt) := reg32Code i.srcReg
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let value := (s.gprs (reg32To64 i.srcReg)).toUInt32
    let s' := s.write32 addr value
    let hasRex := srcExt || baseExt
    let hasSib := baseCode == 4
    let hasDisp := i.disp != 0 || baseCode == 5
    let len := 2 + (if hasRex then 1 else 0) + (if hasSib then 1 else 0) +
      (if hasDisp then 1 else 0)
    { s' with rip := s.rip + len }

  toUops i := derivedMemUops (movMem32DispReg32Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov dword [{i.basePtr}], {i.srcReg}"
    else
      s!"mov dword [{i.basePtr} {formatDisp8 i.disp}], {i.srcReg}"
  toLean i := s!"mov_mem32_disp .{i.basePtr} {formatHex8 i.disp} .{i.srcReg}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand form; production encoding is NASM-cross-checked and the separate guarded scratch harness supplies supplemental native semantic evidence"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovMem32DispReg32.mk · 0 .eax)) ++
    (curatedUInt8Cases.map (MovMem32DispReg32.mk .rax · .eax)) ++
    (allReg32List.map (MovMem32DispReg32.mk .rax 0 ·)) ++
    (allReg32List.map (MovMem32DispReg32.mk .r12 0x7f ·)) ++
    (curatedUInt8Cases.map (MovMem32DispReg32.mk .r13 · .r15d))
  memAccesses := movMem32DispReg32Accesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV QWORD PTR [basePtr + disp8], imm32: Writes 32-bit immediate sign-extended into 64-bit memory. -/
structure MovMem64DispImm32 where
  basePtr : Reg64
  disp    : UInt8
  imm     : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movMem64DispImm32Accesses (i : MovMem64DispImm32) : List MemAccessSpec :=
  [⟨.store, .w64, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

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

  toUops i := derivedMemUops (movMem64DispImm32Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov qword [{i.basePtr}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
    else
      s!"mov qword [{i.basePtr} {formatDisp8 i.disp}], 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"mov_mem64_disp_imm .{i.basePtr} {formatHex8 i.disp} {formatHex32 i.imm}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  -- basePtr varies over allReg64ListNoRsp: with basePtr=.rsp, this struct's SIB-base-4 encoding
  -- is byte-identical to the dedicated qword `MovRspDispImm64` helper, which the decoder
  -- canonicalizes to on purpose (matching the ADD/SUB RSP-immediate precedent) — that RSP case
  -- is exercised by `MovRspDispImm64.roundtripCases` instead. RSP's SIB-base-4 sibling,
  -- R12 (rexB=true), is a genuinely distinct, correctly round-tripping case and stays included.
  roundtripCases :=
    (allReg64ListNoRsp.map (MovMem64DispImm32.mk · 0 0x00000000)) ++
    (curatedUInt8Cases.map (MovMem64DispImm32.mk .rax · 0x00000000)) ++
    (curatedUInt32Cases.map (MovMem64DispImm32.mk .rax 0 ·)) ++
    (curatedUInt8Cases.map (MovMem64DispImm32.mk .r15 · 0x00000000)) ++
    (curatedUInt32Cases.map (MovMem64DispImm32.mk .r15 0 ·))
  memAccesses := movMem64DispImm32Accesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV dstReg64, QWORD PTR [basePtr + disp8]: Reads 64-bit value from memory into register. -/
structure MovReg64Mem64Disp where
  dstReg  : Reg64
  basePtr : Reg64
  disp    : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movReg64Mem64DispAccesses (i : MovReg64Mem64Disp) : List MemAccessSpec :=
  [⟨.load, .w64, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

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

  toUops i := derivedMemUops (movReg64Mem64DispAccesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov {i.dstReg}, qword [{i.basePtr}]"
    else
      s!"mov {i.dstReg}, qword [{i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"mov_reg64_mem64_disp .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovReg64Mem64Disp.mk · .rax 0)) ++
    (allReg64List.map (MovReg64Mem64Disp.mk .rax · 0)) ++
    (curatedUInt8Cases.map (MovReg64Mem64Disp.mk .rax .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovReg64Mem64Disp.mk p.1 p.2 0) ++
    (curatedUInt8Cases.map (MovReg64Mem64Disp.mk .r15 .r15 ·))
  memAccesses := movReg64Mem64DispAccesses

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV dstReg32, DWORD PTR [basePtr + disp8]: Reads a 32-bit value from memory at `basePtr` plus
    sign-extended `disp8` and zero-extends it into the architectural 64-bit destination register.
    Mapping and memory-type admission belong to the selected target/profile boundary. -/
structure MovReg32Mem32Disp where
  dstReg  : Reg32
  basePtr : Reg64
  disp    : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The exact singleton read footprint shared by semantics, uop derivation, and memory-frame
    automation. -/
@[simp] def movReg32Mem32DispAccesses (i : MovReg32Mem32Disp) : List MemAccessSpec :=
  [⟨.load, .w32, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

/-- The two optional bytes in the canonical exact-disp8 encoding. This shape is shared by the
    encoder and operational RIP update so their length accounting cannot drift. -/
structure MovReg32Mem32DispEncodingShape where
  rexPresent : Bool
  sibPresent : Bool
  deriving DecidableEq, Repr

def movReg32Mem32DispEncodingShape (i : MovReg32Mem32Disp) :
    MovReg32Mem32DispEncodingShape :=
  { rexPresent := (reg32Code i.dstReg).2 || (reg64Code i.basePtr).2
    sibPresent := (reg64Code i.basePtr).1 == 4 }

def movReg32Mem32DispEncodedLength (i : MovReg32Mem32Disp) : Nat :=
  let shape := movReg32Mem32DispEncodingShape i
  3 + (if shape.rexPresent then 1 else 0) + (if shape.sibPresent then 1 else 0)

def encodeMovReg32Mem32Disp (i : MovReg32Mem32Disp) : ByteArray :=
  let (dstCode, dstExt) := reg32Code i.dstReg
  let (baseCode, baseExt) := reg64Code i.basePtr
  let shape := movReg32Mem32DispEncodingShape i
  let rexPrefix :=
    if shape.rexPresent then #[makeRex false dstExt false baseExt] else #[]
  let sib := if shape.sibPresent then #[makeSIB 0 4 4] else #[]
  ByteArray.mk rexPrefix ++
    ByteArray.mk (#[0x8B, makeModRM 1 dstCode baseCode] ++ sib ++ #[i.disp])

theorem encodeMovReg32Mem32Disp_size (i : MovReg32Mem32Disp) :
    (encodeMovReg32Mem32Disp i).size = movReg32Mem32DispEncodedLength i := by
  simp [encodeMovReg32Mem32Disp, movReg32Mem32DispEncodedLength,
    movReg32Mem32DispEncodingShape] <;>
    split <;> simp_all <;> split <;> simp_all <;> rfl

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovReg32Mem32Disp where
  encode := encodeMovReg32Mem32Disp

  step i s :=
    -- The effective address is deliberately evaluated from the pre-state. This keeps dst=base
    -- correct even though the 32-bit destination write clears the register's upper half.
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val := (s.read32 addr).toUInt32
    let s' := s.setGpr32 i.dstReg val
    { s' with rip := s.rip + (movReg32Mem32DispEncodedLength i).toUInt64 }

  toUops i := derivedMemUops (movReg32Mem32DispAccesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"mov {i.dstReg}, dword [{i.basePtr}]"
    else
      s!"mov {i.dstReg}, dword [{i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"mov_reg32_mem32_disp .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "general memory-operand form; the sealed guarded scratch-memory differential is supplemental evidence and does not grant silicon admission"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg32List.map (MovReg32Mem32Disp.mk · .rax 0)) ++
    (allReg64List.map (MovReg32Mem32Disp.mk .eax · 0)) ++
    (curatedUInt8Cases.map (MovReg32Mem32Disp.mk .eax .rax ·)) ++
    (extendedReg32Pairs.map fun p => MovReg32Mem32Disp.mk p.1 (reg32To64 p.2) 0) ++
    (curatedUInt8Cases.map (MovReg32Mem32Disp.mk .r15d .r15 ·))
  memAccesses := movReg32Mem32DispAccesses

theorem MovReg32Mem32Disp.step_rip (i : MovReg32Mem32Disp) (s : X86_64MachineState) :
    (X86_64Instruction.step i s).rip =
      s.rip + (X86_64Instruction.encode i).size.toUInt64 := by
  change s.rip + (movReg32Mem32DispEncodedLength i).toUInt64 =
    s.rip + (encodeMovReg32Mem32Disp i).size.toUInt64
  rw [encodeMovReg32Mem32Disp_size]

theorem MovReg32Mem32Disp.step_preserves_other_projections (i : MovReg32Mem32Disp)
    (s : X86_64MachineState) :
    let s' := X86_64Instruction.step i s
    s'.flags = s.flags ∧
    s'.stdinBuffer = s.stdinBuffer ∧
    s'.incomingRequests = s.incomingRequests ∧
    s'.fault = s.fault ∧
    (∀ r, r ≠ reg32To64 i.dstReg → s'.gprs r = s.gprs r) := by
  dsimp
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro r hne
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32, hne]

theorem MovReg32Mem32Disp.step_destination_exact_zero_extended (i : MovReg32Mem32Disp)
    (s : X86_64MachineState) :
    (X86_64Instruction.step i s).gprs (reg32To64 i.dstReg) =
      (s.read32 (s.gprs i.basePtr + signExtend8To64 i.disp)).toUInt32.toUInt64 := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32]

/- REF: intel-sdm#vol=1;sec=3.3.7;part=address-calculations-in-64-bit-mode -/
/-- Effective-address addition is architectural UInt64 addition. These model controls exercise
    both positive and negative disp8 wrap without asking the native scratch harness to map a
    noncanonical host address. -/
theorem movReg32Mem32Disp_effective_address_wrap_controls :
    let positiveSeed :=
      ((default : X86_64MachineState).setGpr64 .rax 0xffffffffffffffff).write32
        0 0x89abcdef
    let positive := X86_64Instruction.step
      (MovReg32Mem32Disp.mk .ecx .rax 1) positiveSeed
    let negativeSeed :=
      ((default : X86_64MachineState).setGpr64 .rax 0).write32
        0xffffffffffffffff 0x76543210
    let negative := X86_64Instruction.step
      (MovReg32Mem32Disp.mk .ecx .rax 0xff) negativeSeed
    positive.gprs .rcx = 0x89abcdef ∧ negative.gprs .rcx = 0x76543210 := by
  decide

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
/-- MOV reg64, imm32 helper. -/
def mov_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨MovR64Imm32.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg32, reg32 helper. -/
def mov_r32_r32 (dst src : Reg32) : AnyX86_64Instruction :=
  ⟨MovR32R32.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg16, reg16 helper. -/
def mov_r16 (dst src : Reg16) : AnyX86_64Instruction :=
  ⟨MovR16R16.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg16, imm16 helper. -/
def mov_r16_imm16 (dst : Reg16) (imm : UInt16) : AnyX86_64Instruction :=
  ⟨MovR16Imm16.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg8, reg8 helper. -/
def mov_r8 (dst src : Reg8) : AnyX86_64Instruction :=
  ⟨MovR8R8.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV reg8, imm8 helper. -/
def mov_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨MovR8Imm8.mk dst imm⟩

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
/-- MOV DWORD PTR [basePtr + disp8], srcReg32 helper. -/
def mov_mem32_disp (basePtr : Reg64) (disp : UInt8) (srcReg : Reg32) : AnyX86_64Instruction :=
  ⟨MovMem32DispReg32.mk basePtr disp srcReg⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV QWORD PTR [basePtr + disp8], imm32 helper. -/
def mov_mem64_disp_imm (basePtr : Reg64) (disp : UInt8) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨MovMem64DispImm32.mk basePtr disp imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV dstReg64, QWORD PTR [basePtr + disp8] helper. -/
def mov_reg64_mem64_disp (dstReg basePtr : Reg64) (disp : UInt8) : AnyX86_64Instruction :=
  ⟨MovReg64Mem64Disp.mk dstReg basePtr disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOV dstReg32, DWORD PTR [basePtr + disp8] helper. -/
def mov_reg32_mem32_disp (dstReg : Reg32) (basePtr : Reg64) (disp : UInt8) :
    AnyX86_64Instruction :=
  ⟨MovReg32Mem32Disp.mk dstReg basePtr disp⟩

/- REF: intel-sdm#vol=2;instr=MOV;part=description -/
/-- MOV dstReg8, BYTE PTR [basePtr + disp8].  This low-byte-only family deliberately excludes
    the legacy high-byte registers AH/CH/DH/BH.  Its canonical identity always uses mod=01 and
    carries an explicit signed disp8, including zero. -/
structure MovReg8Mem8Disp where
  dstReg  : Reg8
  basePtr : Reg64
  disp    : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
@[simp] def movReg8Mem8DispAccesses (i : MovReg8Mem8Disp) : List MemAccessSpec :=
  [⟨.load, .w8, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

structure MovReg8Mem8DispEncodingShape where
  rexPresent : Bool
  sibPresent : Bool
  deriving DecidableEq, Repr

def movReg8Mem8DispEncodingShape (i : MovReg8Mem8Disp) :
    MovReg8Mem8DispEncodingShape :=
  { rexPresent := (reg8Code i.dstReg).2.2 || (reg64Code i.basePtr).2
    sibPresent := (reg64Code i.basePtr).1 == 4 }

def movReg8Mem8DispEncodedLength (i : MovReg8Mem8Disp) : Nat :=
  let shape := movReg8Mem8DispEncodingShape i
  3 + (if shape.rexPresent then 1 else 0) + (if shape.sibPresent then 1 else 0)

def encodeMovReg8Mem8Disp (i : MovReg8Mem8Disp) : ByteArray :=
  let (dstCode, dstExt, _) := reg8Code i.dstReg
  let (baseCode, baseExt) := reg64Code i.basePtr
  let shape := movReg8Mem8DispEncodingShape i
  let rexPrefix := if shape.rexPresent then #[makeRex false dstExt false baseExt] else #[]
  let sib := if shape.sibPresent then #[makeSIB 0 4 4] else #[]
  ByteArray.mk rexPrefix ++
    ByteArray.mk (#[0x8A, makeModRM 1 dstCode baseCode] ++ sib ++ #[i.disp])

theorem encodeMovReg8Mem8Disp_size (i : MovReg8Mem8Disp) :
    (encodeMovReg8Mem8Disp i).size = movReg8Mem8DispEncodedLength i := by
  simp [encodeMovReg8Mem8Disp, movReg8Mem8DispEncodedLength,
    movReg8Mem8DispEncodingShape] <;>
    split <;> simp_all <;> split <;> simp_all <;> rfl

/- REF: intel-sdm#vol=2;instr=MOV;part=operation -/
instance : X86_64Instruction MovReg8Mem8Disp where
  encode := encodeMovReg8Mem8Disp

  step i s :=
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let value := (s.read8 addr).toUInt8
    let s' := s.setGpr8 i.dstReg value
    { s' with rip := s.rip + (movReg8Mem8DispEncodedLength i).toUInt64 }

  toUops i := derivedMemUops (movReg8Mem8DispAccesses i) defaultMemCostModel
  -- The inner `byte` is NASM's displacement-size qualifier.  It forces the exact mod01 identity
  -- even when the displacement is zero, rather than letting NASM shorten `[base + 0]` to mod00.
  toNASM i := s!"mov {i.dstReg}, byte [byte {i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"mov_reg8_mem8_disp .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "exact mod01+disp8 byte load; this slice adds no guarded native scratch class, so the claim is encoding-only"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg8List.map (MovReg8Mem8Disp.mk · .rax 0)) ++
    (allReg64List.map (MovReg8Mem8Disp.mk .al · 0)) ++
    (curatedUInt8Cases.map (MovReg8Mem8Disp.mk .al .rax ·)) ++
    (extendedReg8Pairs.map fun p => MovReg8Mem8Disp.mk p.1 (reg8To64 p.2) 0) ++
    [⟨.r15b, .r12, 0x7F⟩, ⟨.spl, .r13, 0x80⟩]
  memAccesses := movReg8Mem8DispAccesses

theorem MovReg8Mem8Disp.step_rip (i : MovReg8Mem8Disp) (s : X86_64MachineState) :
    (X86_64Instruction.step i s).rip =
      s.rip + (X86_64Instruction.encode i).size.toUInt64 := by
  change s.rip + (movReg8Mem8DispEncodedLength i).toUInt64 =
    s.rip + (encodeMovReg8Mem8Disp i).size.toUInt64
  rw [encodeMovReg8Mem8Disp_size]

theorem MovReg8Mem8Disp.step_preserves_other_projections (i : MovReg8Mem8Disp)
    (s : X86_64MachineState) :
    let s' := X86_64Instruction.step i s
    s'.memory = s.memory ∧
    s'.flags = s.flags ∧
    s'.stdinBuffer = s.stdinBuffer ∧
    s'.incomingRequests = s.incomingRequests ∧
    s'.fault = s.fault ∧
    (∀ r, r ≠ reg8To64 i.dstReg → s'.gprs r = s.gprs r) := by
  dsimp
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro r hne
  exact X86_64MachineState.setGpr8_gpr_other _ _ _ _ hne

theorem MovReg8Mem8Disp.step_destination_exact (i : MovReg8Mem8Disp)
    (s : X86_64MachineState) :
    (X86_64Instruction.step i s).gprs (reg8To64 i.dstReg) =
      (s.gprs (reg8To64 i.dstReg) &&& 0xFFFFFFFFFFFFFF00) |||
        (s.read8 (s.gprs i.basePtr + signExtend8To64 i.disp)).toUInt8.toUInt64 := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr8,
    X86_64MachineState.setGpr64]

/- REF: intel-sdm#vol=1;sec=3.3.7;part=address-calculations-in-64-bit-mode -/
theorem movReg8Mem8Disp_effective_address_wrap_controls :
    let positiveSeed :=
      ((default : X86_64MachineState).setGpr64 .rax 0xffffffffffffffff).write8 0 0xA5
    let positive := X86_64Instruction.step
      (MovReg8Mem8Disp.mk .cl .rax 1) positiveSeed
    let negativeSeed :=
      ((default : X86_64MachineState).setGpr64 .rax 0).write8 0xffffffffffffffff 0x5A
    let negative := X86_64Instruction.step
      (MovReg8Mem8Disp.mk .cl .rax 0xff) negativeSeed
    positive.readGpr8 .cl = 0xA5 ∧ negative.readGpr8 .cl = 0x5A := by
  decide

/- REF: intel-sdm#vol=1;sec=3.4.1.1;part=general-purpose-registers-in-64-bit-mode -/
/-- Destination/base aliasing uses the pre-state effective address and preserves bits 63:8. -/
theorem movReg8Mem8Disp_alias_and_partial_register_control :
    let seed :=
      ((default : X86_64MachineState).setGpr64 .r9 0x0000000010000080).write8
        0x0000000010000000 0xA5
    let final := X86_64Instruction.step
      (MovReg8Mem8Disp.mk .r9b .r9 0x80) seed
    final.gprs .r9 = 0x00000000100000A5 ∧
      final.memory = seed.memory := by
  constructor
  · decide
  · rfl

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Locks the NASM displacement-size qualifier that preserves the exact mod01 identity at zero. -/
theorem movReg8Mem8Disp_nasm_disp8_qualifier_controls :
    X86_64Instruction.toNASM (MovReg8Mem8Disp.mk .al .rax 0) =
        "mov al, byte [byte rax + 0x0]" ∧
      X86_64Instruction.toNASM (MovReg8Mem8Disp.mk .r15b .r12 0x80) =
        "mov r15b, byte [byte r12 - 0x80]" := by
  decide

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def mov_reg8_mem8_disp (dstReg : Reg8) (basePtr : Reg64) (disp : UInt8) :
    AnyX86_64Instruction :=
  ⟨MovReg8Mem8Disp.mk dstReg basePtr disp⟩

/- REF: intel-sdm#vol=2;instr=MOVZX;part=description -/
/-- MOVZX dstReg32, BYTE PTR [basePtr + disp8]: moves one byte from memory and writes its
    zero-extension through the architectural 32-bit destination.  The write therefore clears
    bits 63:32 of the corresponding GPR. -/
structure MovzxR32Mem8 where
  dstReg  : Reg32
  basePtr : Reg64
  disp    : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=MOVZX;part=description -/
/-- MOVZX dstReg64, BYTE PTR [basePtr + disp8]: Moves 8-bit byte from memory with zero-extension into 64-bit register. -/
structure MovzxR64Mem8 where
  dstReg  : Reg64
  basePtr : Reg64
  disp    : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
@[simp] def movzxR32Mem8Accesses (i : MovzxR32Mem8) : List MemAccessSpec :=
  [⟨.load, .w8, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- See `movRspDispByteAccesses`'s doc comment for why this is hoisted rather than duplicated
    inline between `memAccesses` and `toUops`. -/
@[simp] def movzxR64Mem8Accesses (i : MovzxR64Mem8) : List MemAccessSpec :=
  [⟨.load, .w8, ⟨some i.basePtr, none, signExtend8To64 i.disp⟩⟩]

/-- The optional bytes in either canonical `0F B6` memory encoding.  REX.W selects the
    destination width; REX.R/B extend its register fields; SIB is present only for RSP/R12;
    and a displacement is present exactly when nonzero or forced by RBP/R13. -/
structure MovzxMem8EncodingShape where
  rexPresent  : Bool
  sibPresent  : Bool
  dispPresent : Bool
  deriving DecidableEq, Repr

def movzxMem8EncodingShape (rexW dstExt baseExt : Bool) (baseCode : UInt8)
    (disp : UInt8) : MovzxMem8EncodingShape :=
  { rexPresent := rexW || dstExt || baseExt
    sibPresent := baseCode == 4
    dispPresent := disp != 0 || baseCode == 5 }

def movzxMem8EncodedLength (rexW dstExt baseExt : Bool) (baseCode : UInt8)
    (disp : UInt8) : Nat :=
  let shape := movzxMem8EncodingShape rexW dstExt baseExt baseCode disp
  3 + (if shape.rexPresent then 1 else 0) +
    (if shape.sibPresent then 1 else 0) + (if shape.dispPresent then 1 else 0)

def encodeMovzxMem8 (rexW : Bool) (dstCode : UInt8) (dstExt : Bool)
    (baseCode : UInt8) (baseExt : Bool) (disp : UInt8) : ByteArray :=
  let shape := movzxMem8EncodingShape rexW dstExt baseExt baseCode disp
  let rexPrefix :=
    if shape.rexPresent then #[makeRex rexW dstExt false baseExt] else #[]
  let mod : UInt8 := if shape.dispPresent then 1 else 0
  let sib := if shape.sibPresent then #[makeSIB 0 4 4] else #[]
  let displacement := if shape.dispPresent then #[disp] else #[]
  ByteArray.mk rexPrefix ++
    ByteArray.mk (#[0x0F, 0xB6, makeModRM mod dstCode baseCode] ++ sib ++ displacement)

theorem encodeMovzxMem8_size (rexW dstExt baseExt : Bool) (dstCode baseCode : UInt8)
    (disp : UInt8) :
    (encodeMovzxMem8 rexW dstCode dstExt baseCode baseExt disp).size =
      movzxMem8EncodedLength rexW dstExt baseExt baseCode disp := by
  simp [encodeMovzxMem8, movzxMem8EncodedLength, movzxMem8EncodingShape] <;>
    split <;> simp_all <;> split <;> simp_all <;> split <;> simp_all <;> rfl

def encodeMovzxR32Mem8 (i : MovzxR32Mem8) : ByteArray :=
  let (dstCode, dstExt) := reg32Code i.dstReg
  let (baseCode, baseExt) := reg64Code i.basePtr
  encodeMovzxMem8 false dstCode dstExt baseCode baseExt i.disp

def movzxR32Mem8EncodedLength (i : MovzxR32Mem8) : Nat :=
  let (_, dstExt) := reg32Code i.dstReg
  let (baseCode, baseExt) := reg64Code i.basePtr
  movzxMem8EncodedLength false dstExt baseExt baseCode i.disp

theorem encodeMovzxR32Mem8_size (i : MovzxR32Mem8) :
    (encodeMovzxR32Mem8 i).size = movzxR32Mem8EncodedLength i := by
  simp [encodeMovzxR32Mem8, movzxR32Mem8EncodedLength, encodeMovzxMem8_size]

def encodeMovzxR64Mem8 (i : MovzxR64Mem8) : ByteArray :=
  let (dstCode, dstExt) := reg64Code i.dstReg
  let (baseCode, baseExt) := reg64Code i.basePtr
  encodeMovzxMem8 true dstCode dstExt baseCode baseExt i.disp

def movzxR64Mem8EncodedLength (i : MovzxR64Mem8) : Nat :=
  let (_, dstExt) := reg64Code i.dstReg
  let (baseCode, baseExt) := reg64Code i.basePtr
  movzxMem8EncodedLength true dstExt baseExt baseCode i.disp

theorem encodeMovzxR64Mem8_size (i : MovzxR64Mem8) :
    (encodeMovzxR64Mem8 i).size = movzxR64Mem8EncodedLength i := by
  simp [encodeMovzxR64Mem8, movzxR64Mem8EncodedLength, encodeMovzxMem8_size]

/- REF: intel-sdm#vol=2;instr=MOVZX;part=operation -/
instance : X86_64Instruction MovzxR32Mem8 where
  encode := encodeMovzxR32Mem8

  step i s :=
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val := (s.read8 addr).toUInt8
    let s' := s.setGpr32 i.dstReg val.toUInt32
    { s' with rip := s.rip + (movzxR32Mem8EncodedLength i).toUInt64 }

  toUops i := derivedMemUops (movzxR32Mem8Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"movzx {i.dstReg}, byte [{i.basePtr}]"
    else
      s!"movzx {i.dstReg}, byte [{i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"movzx_r32_mem8 .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "canonical 0F B6 byte load into a 32-bit destination; this slice adds no guarded native scratch class, so the claim is encoding-only"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg32List.map (MovzxR32Mem8.mk · .rax 0)) ++
    (allReg64List.map (MovzxR32Mem8.mk .eax · 0)) ++
    (curatedUInt8Cases.map (MovzxR32Mem8.mk .eax .rax ·)) ++
    (extendedReg32Pairs.map fun p => MovzxR32Mem8.mk p.1 (reg32To64 p.2) 0) ++
    (curatedUInt8Cases.map (MovzxR32Mem8.mk .r15d .r15 ·))
  memAccesses := movzxR32Mem8Accesses

/- REF: intel-sdm#vol=2;instr=MOVZX;part=operation -/
instance : X86_64Instruction MovzxR64Mem8 where
  encode := encodeMovzxR64Mem8

  step i s :=
    let addr := s.gprs i.basePtr + signExtend8To64 i.disp
    let val := s.read8 addr
    let s' := s.setGpr64 i.dstReg val
    { s' with rip := s.rip + (movzxR64Mem8EncodedLength i).toUInt64 }

  toUops i := derivedMemUops (movzxR64Mem8Accesses i) defaultMemCostModel
  toNASM i :=
    if i.disp == 0 then
      s!"movzx {i.dstReg}, byte [{i.basePtr}]"
    else
      s!"movzx {i.dstReg}, byte [{i.basePtr} {formatDisp8 i.disp}]"
  toLean i := s!"movzx_r64_mem8 .{i.dstReg} .{i.basePtr} {formatHex8 i.disp}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "memory-operand or RSP-relative addressing form; HardwareHarness has no scratch-memory-region support yet, and the memory-operand capability contract is also unbuilt (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P2/P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (MovzxR64Mem8.mk · .rax 0)) ++
    (allReg64List.map (MovzxR64Mem8.mk .rax · 0)) ++
    (curatedUInt8Cases.map (MovzxR64Mem8.mk .rax .rax ·)) ++
    (extendedReg64Pairs.map fun p => MovzxR64Mem8.mk p.1 p.2 0) ++
    (curatedUInt8Cases.map (MovzxR64Mem8.mk .r15 .r15 ·))
  memAccesses := movzxR64Mem8Accesses

theorem MovzxR32Mem8.step_rip (i : MovzxR32Mem8) (s : X86_64MachineState) :
    (X86_64Instruction.step i s).rip =
      s.rip + (X86_64Instruction.encode i).size.toUInt64 := by
  change s.rip + (movzxR32Mem8EncodedLength i).toUInt64 =
    s.rip + (encodeMovzxR32Mem8 i).size.toUInt64
  rw [encodeMovzxR32Mem8_size]

theorem MovzxR64Mem8.step_rip (i : MovzxR64Mem8) (s : X86_64MachineState) :
    (X86_64Instruction.step i s).rip =
      s.rip + (X86_64Instruction.encode i).size.toUInt64 := by
  change s.rip + (movzxR64Mem8EncodedLength i).toUInt64 =
    s.rip + (encodeMovzxR64Mem8 i).size.toUInt64
  rw [encodeMovzxR64Mem8_size]

theorem MovzxR32Mem8.step_preserves_other_projections (i : MovzxR32Mem8)
    (s : X86_64MachineState) :
    let s' := X86_64Instruction.step i s
    s'.memory = s.memory ∧ s'.flags = s.flags ∧ s'.stdinBuffer = s.stdinBuffer ∧
      s'.incomingRequests = s.incomingRequests ∧ s'.fault = s.fault ∧
      (∀ r, r ≠ reg32To64 i.dstReg → s'.gprs r = s.gprs r) := by
  dsimp
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro r hne
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32, hne]

theorem MovzxR64Mem8.step_preserves_other_projections (i : MovzxR64Mem8)
    (s : X86_64MachineState) :
    let s' := X86_64Instruction.step i s
    s'.memory = s.memory ∧ s'.flags = s.flags ∧ s'.stdinBuffer = s.stdinBuffer ∧
      s'.incomingRequests = s.incomingRequests ∧ s'.fault = s.fault ∧
      (∀ r, r ≠ i.dstReg → s'.gprs r = s.gprs r) := by
  dsimp
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro r hne
  simp [X86_64Instruction.step, X86_64MachineState.setGpr64, hne]

theorem MovzxR32Mem8.step_destination_exact_zero_extended (i : MovzxR32Mem8)
    (s : X86_64MachineState) :
    (X86_64Instruction.step i s).gprs (reg32To64 i.dstReg) =
      s.read8 (s.gprs i.basePtr + signExtend8To64 i.disp) := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32,
    X86_64MachineState.read8, X86_64Mem.read]

theorem MovzxR64Mem8.step_destination_exact_zero_extended (i : MovzxR64Mem8)
    (s : X86_64MachineState) :
    (X86_64Instruction.step i s).gprs i.dstReg =
      s.read8 (s.gprs i.basePtr + signExtend8To64 i.disp) := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr64]

theorem movzxR32Mem8_effective_address_wrap_controls :
    let positiveSeed :=
      ((default : X86_64MachineState).setGpr64 .rax 0xffffffffffffffff).write8 0 0xa5
    let positive := X86_64Instruction.step (MovzxR32Mem8.mk .ecx .rax 1) positiveSeed
    let negativeSeed :=
      ((default : X86_64MachineState).setGpr64 .rax 0).write8 0xffffffffffffffff 0x5a
    let negative := X86_64Instruction.step (MovzxR32Mem8.mk .ecx .rax 0xff) negativeSeed
    positive.gprs .rcx = 0xa5 ∧ negative.gprs .rcx = 0x5a := by
  decide

theorem movzxR32Mem8_alias_uses_pre_state_address :
    let seed := ((default : X86_64MachineState).setGpr64 .r9 0x10000000).write8
      0x000000000fffff80 0xa5
    let final := X86_64Instruction.step (MovzxR32Mem8.mk .r9d .r9 0x80) seed
    final.gprs .r9 = 0xa5 ∧ final.memory = seed.memory := by
  constructor
  · decide
  · rfl

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOVZX dstReg64, BYTE PTR [basePtr + disp8] helper. -/
def movzx_r64_mem8 (dstReg basePtr : Reg64) (disp : UInt8 := 0) : AnyX86_64Instruction :=
  ⟨MovzxR64Mem8.mk dstReg basePtr disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- MOVZX dstReg32, BYTE PTR [basePtr + disp8] helper. -/
def movzx_r32_mem8 (dstReg : Reg32) (basePtr : Reg64) (disp : UInt8 := 0) :
    AnyX86_64Instruction :=
  ⟨MovzxR32Mem8.mk dstReg basePtr disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Compatibility spelling for the canonical general disp8 family at base RSP. -/
def mov_r32_rsp (dstReg : Reg32) (disp : UInt8) : AnyX86_64Instruction :=
  mov_reg32_mem32_disp dstReg .rsp disp

@[simp] theorem mov_r32_rsp_is_canonical_general_identity (dstReg : Reg32) (disp : UInt8) :
    mov_r32_rsp dstReg disp = mov_reg32_mem32_disp dstReg .rsp disp := rfl

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
      memory := X86_64Mem.zero
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

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Parse the shared canonical base-plus-optional-disp8 address identity used by both `0F B6`
    destination widths.  The returned position is immediately after the complete addressing
    bytes.  Indexed SIB, RIP-relative/no-base, and longer or redundant displacement identities
    are deliberately outside these instruction structures. -/
private def decodeMovzxMem8Address (bytes : ByteArray) (mod rm : UInt8) (modPos : Nat)
    (rexB : Bool) : Except String (Reg64 × UInt8 × Nat) :=
  if mod == 0 then
    if rm == 4 then
      match readUInt8 bytes modPos with
      | .error e => .error e
      | .ok sib =>
        if sib == makeSIB 0 4 4 then
          .ok (codeToReg64 4 rexB, 0, modPos + 1)
        else
          .error "movTryDecode: unsupported indexed/noncanonical SIB for 0F B6 MOVZX"
    else if rm == 5 then
      .error "movTryDecode: unsupported RIP-relative/no-base form for 0F B6 MOVZX"
    else
      .ok (codeToReg64 rm rexB, 0, modPos)
  else if mod == 1 then
    if rm == 4 then
      match readUInt8 bytes modPos with
      | .error e => .error e
      | .ok sib =>
        if sib == makeSIB 0 4 4 then
          match readUInt8 bytes (modPos + 1) with
          | .error e => .error e
          | .ok disp8 =>
            if disp8 == 0 then
              .error "movTryDecode: noncanonical zero displacement for 0F B6 MOVZX"
            else
              .ok (codeToReg64 4 rexB, disp8, modPos + 2)
        else
          .error "movTryDecode: unsupported indexed/noncanonical SIB for 0F B6 MOVZX"
    else
      match readUInt8 bytes modPos with
      | .error e => .error e
      | .ok disp8 =>
        if disp8 == 0 && rm != 5 then
          .error "movTryDecode: noncanonical zero displacement for 0F B6 MOVZX"
        else
          .ok (codeToReg64 rm rexB, disp8, modPos + 1)
  else
    .error "movTryDecode: unsupported mod field for 0F B6 MOVZX"

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the MOV/MOVZX family: `0xB8..0xBF` (MOV reg, imm — 32-bit or 64-bit
    depending on REX.W), `0x88` (MOV byte ptr [mem], reg8), `0x8A` (MOV low reg8,
    byte ptr [base+disp8], exact mod01 identity), `0x89` (MOV r64, r64 or MOV
    [base+disp], reg64 when REX.W=1; MOV [base+disp], reg32 when REX.W=0), `0x8B`
    (MOV r64, [base+disp] when REX.W=1, or MOV r32, [base+disp] when REX.W=0),
    `0xC6` (MOV byte ptr [RSP+disp8], imm8, RSP-only), `0xC7`
    (MOV [mem], imm32, with the same RSP/R12 canonicalization `encode` uses), and `0x0F 0xB6`
    (MOVZX r64 when REX.W=1, or MOVZX r32 when REX.W=0, from byte ptr [base+disp]).
    Preserves every soundness fix the original monolithic
    branch carried (the 0x8B REX.W-conditioned width switch; SIB-base-4 deriving R12 via `rexB`
    instead of hardcoding RSP for 0x88/0x89/0x8B/0xC7). Errors for any other byte pattern. -/
def movTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, hasRex, rexW, rexR, rexX, rexB, opcode, opOffset) =>
    if has0x66 then
      if opcode == 0x89 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, reg, rm, modPos) =>
          if mod == 3 then
            let dst := codeToReg16 rm rexB
            let src := codeToReg16 reg rexR
            .ok (mov_r16 dst src, modPos - offset)
          else .error "movTryDecode: unsupported 16-bit memory form for 0x89 MOV"
      else if opcode >= 0xB8 && opcode <= 0xBF then
        let regCode := opcode - 0xB8
        let dst := codeToReg16 regCode rexB
        match readUInt16LE bytes opOffset with
        | .error e => .error e
        | .ok imm16 => .ok (mov_r16_imm16 dst imm16, (opOffset + 2) - offset)
      else .error s!"movTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} with 0x66 is not MOV"
    else if opcode >= 0xB8 && opcode <= 0xBF then
      let regCode := opcode - 0xB8
      if rexW then
        let dst := codeToReg64 regCode rexB
        match readUInt64LE bytes opOffset with
        | .error e => .error e
        | .ok imm64 => .ok (mov_r64_imm64 dst imm64, (opOffset + 8) - offset)
      else
        let dst := codeToReg32 regCode rexB
        match readUInt32LE bytes opOffset with
        | .error e => .error e
        | .ok imm32 => .ok (mov_r32 dst imm32, (opOffset + 4) - offset)
    else if opcode >= 0xB0 && opcode <= 0xB7 then
      let regCode := opcode - 0xB0
      let dst := codeToReg8 regCode rexB
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok imm8 => .ok (mov_r8_imm8 dst imm8, (opOffset + 1) - offset)
    else if opcode == 0x88 then
      if rexW || rexX then
        .error "movTryDecode: unsupported REX.W/REX.X form for 0x88 MOV"
      else
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, reg, rm, modPos) =>
          if mod == 3 then
            let dst := codeToReg8 rm rexB
            let src := codeToReg8 reg rexR
            let needsRex := rexR || rexB || (reg8Code src).2.2 || (reg8Code dst).2.2
            if hasRex != needsRex then
              .error "movTryDecode: noncanonical or legacy high-byte REX identity for 0x88 MOV"
            else
              .ok (mov_r8 dst src, modPos - offset)
          else
            let needsRex := rexR || rexB || reg >= 4
            if hasRex != needsRex then
              .error "movTryDecode: noncanonical or legacy high-byte REX identity for 0x88 MOV"
            else
              let srcReg := codeToReg64 reg rexR
              if mod == 0 then
              if rm == 4 then
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok sib =>
                  if sib == makeSIB 0 4 4 then
                    let dstPtr := codeToReg64 4 rexB
                    .ok (mov_mem8 dstPtr srcReg, (modPos + 1) - offset)
                  else
                    .error "movTryDecode: unsupported indexed/noncanonical SIB for 0x88 MOV"
              else if rm == 5 then
                .error "movTryDecode: unsupported RIP-relative/no-base form for 0x88 MOV"
              else
                let dstPtr := codeToReg64 rm rexB
                .ok (mov_mem8 dstPtr srcReg, modPos - offset)
            else if mod == 1 && rm == 5 then
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok disp8 =>
                if disp8 == 0 then
                  let dstPtr := codeToReg64 5 rexB
                  .ok (mov_mem8 dstPtr srcReg, (modPos + 1) - offset)
                else
                  .error "movTryDecode: noncanonical nonzero displacement for 0x88 MOV"
            else
              .error "movTryDecode: unsupported mod field for 0x88 MOV"
    else if opcode == 0x8A then
      if rexW || rexX then
        .error "movTryDecode: unsupported REX.W/REX.X form for 0x8A MOV"
      else
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, reg, rm, modPos) =>
          let needsRex := rexR || rexB || reg >= 4
          if hasRex != needsRex then
            .error "movTryDecode: noncanonical or legacy high-byte REX identity for 0x8A MOV"
          else if mod != 1 then
            .error "movTryDecode: unsupported mod field for exact-disp8 0x8A MOV"
          else
            let dstReg := codeToReg8 reg rexR
            let basePtr := codeToReg64 rm rexB
            if rm == 4 then
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok sib =>
                if sib == makeSIB 0 4 4 then
                  match readUInt8 bytes (modPos + 1) with
                  | .error e => .error e
                  | .ok disp8 =>
                    .ok (mov_reg8_mem8_disp dstReg basePtr disp8, (modPos + 2) - offset)
                else
                  .error "movTryDecode: unsupported indexed/noncanonical SIB for 0x8A MOV"
            else
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok disp8 =>
                .ok (mov_reg8_mem8_disp dstReg basePtr disp8, (modPos + 1) - offset)
    else if opcode == 0x89 then
      if rexX then
        .error "movTryDecode: unsupported REX.X form for 0x89 MOV"
      else if !rexW && hasRex != (rexR || rexB) then
        .error "movTryDecode: redundant REX prefix for 32-bit 0x89 MOV"
      else
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, reg, rm, modPos) =>
          if mod == 3 then
            if rexW then
              let dst := codeToReg64 rm rexB
              let src := codeToReg64 reg rexR
              .ok (mov_r64 dst src, modPos - offset)
            else
              let dst := codeToReg32 rm rexB
              let src := codeToReg32 reg rexR
              .ok (mov_r32_r32 dst src, modPos - offset)
          else if mod == 0 then
            if rexW then
              let srcReg := codeToReg64 reg rexR
              if rm == 4 then
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok sib =>
                  if sib == makeSIB 0 4 4 then
                    let basePtr := codeToReg64 4 rexB
                    .ok (mov_mem64_disp basePtr 0 srcReg, (modPos + 1) - offset)
                  else
                    .error "movTryDecode: unsupported indexed/noncanonical SIB for 64-bit 0x89 MOV"
              else if rm == 5 then
                .error "movTryDecode: unsupported RIP-relative 64-bit 0x89 MOV"
              else
                let basePtr := codeToReg64 rm rexB
                .ok (mov_mem64_disp basePtr 0 srcReg, modPos - offset)
            else
              let srcReg := codeToReg32 reg rexR
              if rm == 4 then
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok sib =>
                  if sib == makeSIB 0 4 4 then
                    let basePtr := codeToReg64 4 rexB
                    .ok (mov_mem32_disp basePtr 0 srcReg, (modPos + 1) - offset)
                  else
                    .error "movTryDecode: unsupported indexed/noncanonical SIB for 32-bit 0x89 MOV"
              else if rm == 5 then
                .error "movTryDecode: unsupported RIP-relative 32-bit 0x89 MOV"
              else
                let basePtr := codeToReg64 rm rexB
                .ok (mov_mem32_disp basePtr 0 srcReg, modPos - offset)
          else if mod == 1 then
          if rexW then
            let srcReg := codeToReg64 reg rexR
            if rm == 4 then
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok sib =>
                if sib == makeSIB 0 4 4 then
                  match readUInt8 bytes (modPos + 1) with
                  | .error e => .error e
                  | .ok disp8 =>
                    if disp8 == 0 then
                      .error "movTryDecode: noncanonical zero displacement for 64-bit 0x89 MOV"
                    else
                      let basePtr := codeToReg64 4 rexB
                      .ok (mov_mem64_disp basePtr disp8 srcReg, (modPos + 2) - offset)
                else
                  .error "movTryDecode: unsupported indexed/noncanonical SIB for 64-bit 0x89 MOV"
            else
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok disp8 =>
                if disp8 == 0 && rm != 5 then
                  .error "movTryDecode: noncanonical zero displacement for 64-bit 0x89 MOV"
                else
                  let basePtr := codeToReg64 rm rexB
                  .ok (mov_mem64_disp basePtr disp8 srcReg, (modPos + 1) - offset)
          else
            let srcReg := codeToReg32 reg rexR
            if rm == 4 then
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok sib =>
                if sib == makeSIB 0 4 4 then
                  match readUInt8 bytes (modPos + 1) with
                  | .error e => .error e
                  | .ok disp8 =>
                    if disp8 == 0 then
                      .error "movTryDecode: noncanonical zero displacement for 32-bit 0x89 MOV"
                    else
                      let basePtr := codeToReg64 4 rexB
                      .ok (mov_mem32_disp basePtr disp8 srcReg, (modPos + 2) - offset)
                else
                  .error "movTryDecode: unsupported indexed/noncanonical SIB for 32-bit 0x89 MOV"
            else
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok disp8 =>
                if disp8 == 0 && rm != 5 then
                  .error "movTryDecode: noncanonical zero displacement for 32-bit 0x89 MOV"
                else
                let basePtr := codeToReg64 rm rexB
                .ok (mov_mem32_disp basePtr disp8 srcReg, (modPos + 1) - offset)
          else
            .error "movTryDecode: unsupported mod field for 0x89 MOV"
    else if opcode == 0x8B then
      if rexX then
        .error "movTryDecode: unsupported indexed REX.X form for 0x8B MOV"
      else if !rexW && hasRex && !rexR && !rexB then
        .error "movTryDecode: redundant REX prefix for 32-bit 0x8B MOV"
      else
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, reg, rm, modPos) =>
          if rexW then
            let dstReg := codeToReg64 reg rexR
            if mod == 0 then
              if rm == 4 then
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok sib =>
                  if sib == makeSIB 0 4 4 then
                    let basePtr := codeToReg64 4 rexB
                    .ok (mov_reg64_mem64_disp dstReg basePtr 0, (modPos + 1) - offset)
                  else
                    .error "movTryDecode: unsupported indexed/noncanonical SIB for 64-bit 0x8B MOV"
              else if rm == 5 then
                .error "movTryDecode: unsupported RIP-relative 64-bit 0x8B MOV"
              else
                let basePtr := codeToReg64 rm rexB
                .ok (mov_reg64_mem64_disp dstReg basePtr 0, modPos - offset)
            else if mod == 1 then
              if rm == 4 then
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok sib =>
                  if sib == makeSIB 0 4 4 then
                    match readUInt8 bytes (modPos + 1) with
                    | .error e => .error e
                    | .ok disp8 =>
                      if disp8 == 0 then
                        .error "movTryDecode: noncanonical zero displacement for 64-bit 0x8B MOV"
                      else
                        let basePtr := codeToReg64 4 rexB
                        .ok (mov_reg64_mem64_disp dstReg basePtr disp8,
                          (modPos + 2) - offset)
                  else
                    .error "movTryDecode: unsupported indexed/noncanonical SIB for 64-bit 0x8B MOV"
              else
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok disp8 =>
                  if disp8 == 0 && rm != 5 then
                    .error "movTryDecode: noncanonical zero displacement for 64-bit 0x8B MOV"
                  else
                    let basePtr := codeToReg64 rm rexB
                    .ok (mov_reg64_mem64_disp dstReg basePtr disp8,
                      (modPos + 1) - offset)
            else
              .error "movTryDecode: unsupported mod field for 64-bit 0x8B MOV"
          else
            let dstReg := codeToReg32 reg rexR
            if mod == 1 then
              if rm == 4 then
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok sib =>
                  if sib == makeSIB 0 4 4 then
                    match readUInt8 bytes (modPos + 1) with
                    | .error e => .error e
                    | .ok disp8 =>
                      let basePtr := codeToReg64 4 rexB
                      .ok (mov_reg32_mem32_disp dstReg basePtr disp8,
                        (modPos + 2) - offset)
                  else
                    .error "movTryDecode: unsupported indexed/noncanonical SIB for 32-bit 0x8B MOV"
              else
                match readUInt8 bytes modPos with
                | .error e => .error e
                | .ok disp8 =>
                  let basePtr := codeToReg64 rm rexB
                  .ok (mov_reg32_mem32_disp dstReg basePtr disp8,
                    (modPos + 1) - offset)
            else
              .error "movTryDecode: 32-bit 0x8B MOV requires canonical mod=01 disp8"
    else if opcode == 0xC6 then
      if hasRex then
        .error "movTryDecode: unsupported REX prefix for 0xC6 MOV"
      else
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, extension, rm, modPos) =>
          if extension != 0 then
            .error "movTryDecode: 0xC6 MOV requires ModRM /0"
          else if rm != 4 then
            .error "movTryDecode: unsupported non-RSP rm field for 0xC6 MOV"
          else
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok sib =>
              if sib != makeSIB 0 4 4 then
                .error "movTryDecode: unsupported indexed/noncanonical SIB for 0xC6 MOV"
              else
                let nextPos := modPos + 1
                if mod == 0 then
                  match readUInt8 bytes nextPos with
                  | .error e => .error e
                  | .ok val => .ok (mov_rsp_byte 0 val, (nextPos + 1) - offset)
                else if mod == 1 then
                  match readUInt8 bytes nextPos with
                  | .error e => .error e
                  | .ok disp8 =>
                    if disp8 == 0 then
                      .error "movTryDecode: noncanonical zero displacement for 0xC6 MOV"
                    else
                      match readUInt8 bytes (nextPos + 1) with
                      | .error e => .error e
                      | .ok val => .ok (mov_rsp_byte disp8 val, (nextPos + 2) - offset)
                else
                  .error "movTryDecode: unsupported mod field for 0xC6 MOV"
    else if opcode == 0xC7 then
      if rexR || rexX || (!rexW && hasRex) then
        .error "movTryDecode: unsupported or redundant REX prefix for 0xC7 MOV"
      else
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (mod, extension, rm, modPos) =>
          if extension != 0 then
            .error "movTryDecode: 0xC7 MOV requires ModRM /0"
          else if mod == 0 then
            if rm == 4 then
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok sib =>
                if sib != makeSIB 0 4 4 then
                  .error "movTryDecode: unsupported indexed/noncanonical SIB for 0xC7 MOV"
                else
                  let immPos := modPos + 1
                  match readUInt32LE bytes immPos with
                  | .error e => .error e
                  | .ok imm32 =>
                    let pos := immPos + 4
                    if rexW then
                      if rexB then
                        .ok (mov_mem64_disp_imm .r12 0 imm32, pos - offset)
                      else
                        .ok (mov_rsp64 0 imm32, pos - offset)
                    else
                      .ok (mov_rsp32 0 imm32, pos - offset)
            else if rm == 5 then
              .error "movTryDecode: unsupported RIP-relative/no-base form for 0xC7 MOV"
            else if !rexW then
              .error "movTryDecode: unsupported non-RSP dword form for 0xC7 MOV"
            else
              let basePtr := codeToReg64 rm rexB
              match readUInt32LE bytes modPos with
              | .error e => .error e
              | .ok imm32 =>
                .ok (mov_mem64_disp_imm basePtr 0 imm32, (modPos + 4) - offset)
          else if mod == 1 then
            if rm == 4 then
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok sib =>
                if sib != makeSIB 0 4 4 then
                  .error "movTryDecode: unsupported indexed/noncanonical SIB for 0xC7 MOV"
                else
                  let dispPos := modPos + 1
                  match readUInt8 bytes dispPos with
                  | .error e => .error e
                  | .ok disp8 =>
                    if disp8 == 0 then
                      .error "movTryDecode: noncanonical zero displacement for 0xC7 MOV"
                    else
                      let immPos := dispPos + 1
                      match readUInt32LE bytes immPos with
                      | .error e => .error e
                      | .ok imm32 =>
                        let pos := immPos + 4
                        if rexW then
                          if rexB then
                            .ok (mov_mem64_disp_imm .r12 disp8 imm32, pos - offset)
                          else
                            .ok (mov_rsp64 disp8 imm32, pos - offset)
                        else
                          .ok (mov_rsp32 disp8 imm32, pos - offset)
            else if !rexW then
              .error "movTryDecode: unsupported non-RSP dword form for 0xC7 MOV"
            else
              match readUInt8 bytes modPos with
              | .error e => .error e
              | .ok disp8 =>
                if disp8 == 0 && rm != 5 then
                  .error "movTryDecode: noncanonical zero displacement for 0xC7 MOV"
                else
                  let basePtr := codeToReg64 rm rexB
                  let immPos := modPos + 1
                  match readUInt32LE bytes immPos with
                  | .error e => .error e
                  | .ok imm32 =>
                    .ok (mov_mem64_disp_imm basePtr disp8 imm32,
                      (immPos + 4) - offset)
          else if mod == 3 then
            if rexW then
              let dst := codeToReg64 rm rexB
              match readUInt32LE bytes modPos with
              | .error e => .error e
              | .ok imm32 => .ok (mov_r64_imm32 dst imm32, (modPos + 4) - offset)
            else
              .error "movTryDecode: 32-bit register-immediate 0xC7 /0 is noncanonical (use 0xB8)"
          else
            .error "movTryDecode: unsupported mod field for 0xC7 MOV"
    else if opcode == 0x0F then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok op2 =>
        if op2 == 0xB6 then
          if rexX then
            .error "movTryDecode: unsupported REX.X form for 0F B6 MOVZX"
          else if !rexW && hasRex != (rexR || rexB) then
            .error "movTryDecode: redundant REX prefix for 32-bit 0F B6 MOVZX"
          else
            match readModRM bytes (opOffset + 1) with
            | .error e => .error e
            | .ok (mod, reg, rm, modPos) =>
              match decodeMovzxMem8Address bytes mod rm modPos rexB with
              | .error e => .error e
              | .ok (basePtr, disp8, nextPos) =>
                if rexW then
                  .ok (movzx_r64_mem8 (codeToReg64 reg rexR) basePtr disp8,
                    nextPos - offset)
                else
                  .ok (movzx_r32_mem8 (codeToReg32 reg rexR) basePtr disp8,
                    nextPos - offset)
        else
          .error "movTryDecode: 0x0F sub-opcode is not MOVZX"
    else
      .error s!"movTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not MOV"

end Gasm.Targets.X86_64.Instructions

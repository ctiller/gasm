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

/- REF: intel-sdm#vol=2;instr=NEG;part=description -/
/-- NEG r64: Replaces the value of destination 64-bit register with its two's complement (0 - val) and updates arithmetic flags. -/
structure NegR64 where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=NEG;part=operation -/
instance : X86_64Instruction NegR64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xF7, makeModRM 3 3 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let res := 0 - dVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsNeg64 dVal
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "NEG.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"neg {i.dst}"
  toLean i := s!"neg_r64 .{i.dst}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor1Reg i.dst rng
  roundtripCases := allReg64List.map NegR64.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- NEG r64 helper. -/
def neg_r64 (dst : Reg64) : AnyX86_64Instruction :=
  ⟨NegR64.mk dst⟩

/- REF: intel-sdm#vol=2;instr=NEG;part=description -/
/-- NEG r32: Replaces the value of destination 32-bit register with its two's complement with 64-bit zero-extension and updates arithmetic flags. -/
structure NegR32 where
  dst : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=NEG;part=operation -/
instance : X86_64Instruction NegR32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xF7, makeModRM 3 3 dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let res := 0 - dVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsNeg32 dVal
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "NEG.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"neg {i.dst}"
  toLean i := s!"neg_r32 .{i.dst}"
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor1Reg (reg32To64 i.dst) rng
  roundtripCases := allReg32List.map NegR32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=NEG;part=description -/
/-- NEG r16: Replaces the value of destination 16-bit register with its two's complement, preserving upper 48 bits, and updates arithmetic flags. -/
structure NegR16 where
  dst : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=NEG;part=operation -/
instance : X86_64Instruction NegR16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0xF7, makeModRM 3 3 dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let res := 0 - dVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsNeg16 dVal
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "NEG.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"neg {i.dst}"
  toLean i := s!"neg_r16 .{i.dst}"
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor1Reg (reg16To64 i.dst) rng
  roundtripCases := allReg16List.map NegR16.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=NEG;part=description -/
/-- NEG r8: Replaces the value of destination 8-bit register with its two's complement, preserving upper 56 bits, and updates arithmetic flags. -/
structure NegR8 where
  dst : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=NEG;part=operation -/
instance : X86_64Instruction NegR8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0xF6, makeModRM 3 3 dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let res := 0 - dVal
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsNeg8 dVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "NEG.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"neg {i.dst}"
  toLean i := s!"neg_r8 .{i.dst}"
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor1Reg (reg8To64 i.dst) rng
  roundtripCases := allReg8List.map NegR8.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def neg_r32 (dst : Reg32) : AnyX86_64Instruction := ⟨NegR32.mk dst⟩
def neg_r16 (dst : Reg16) : AnyX86_64Instruction := ⟨NegR16.mk dst⟩
def neg_r8 (dst : Reg8) : AnyX86_64Instruction := ⟨NegR8.mk dst⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the NEG family: `0xF7 /3` (NEG r64/r32/r16) and `0xF6 /3` (NEG r8),
    sharing Group 3 with TEST/NOT/DIV, disambiguated by ModR/M.reg. Errors for any other byte pattern. -/
def negTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, _, rexW, _, _, rexB, opcode, opOffset) =>
    if has0x66 then
      if opcode == 0xF7 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, pos) =>
          if reg == 3 then
            let dst := codeToReg16 rm rexB
            .ok (neg_r16 dst, pos - offset)
          else .error "negTryDecode: 0xF7 sub-opcode is not NEG"
      else .error s!"negTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} with 0x66 prefix is not NEG"
    else if opcode == 0xF6 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if reg == 3 then
          let dst := codeToReg8 rm rexB
          .ok (neg_r8 dst, pos - offset)
        else .error "negTryDecode: 0xF6 sub-opcode is not NEG"
    else if opcode == 0xF7 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if reg == 3 then
          if rexW then
            let dst := codeToReg64 rm rexB
            .ok (neg_r64 dst, pos - offset)
          else
            let dst := codeToReg32 rm rexB
            .ok (neg_r32 dst, pos - offset)
        else .error "negTryDecode: 0xF7 sub-opcode is not NEG"
    else
      .error s!"negTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not NEG"

end Gasm.Targets.X86_64.Instructions

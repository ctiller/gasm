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

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r64, r64: Adds 64-bit source register to destination register and updates condition flags. -/
structure AddR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x01, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let res := dVal + sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsAdd64 dVal sVal
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "ADD.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, {i.src}"
  toLean i := s!"add_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (AddR64R64.mk · .rax)) ++ (allReg64List.map (AddR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => AddR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r64, imm8: Adds sign-extended 8-bit immediate to destination register and updates condition flags. -/
structure AddR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x83, makeModRM 3 0 dstCode, i.imm]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtend8To64 i.imm
    let res := dVal + sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsAdd64 dVal sVal
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "ADD.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"add_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64ListNoRsp.map (AddR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AddR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (AddR64Imm8.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD RSP, imm8 instruction: deallocates stack frame space. -/
structure AddRspImm8 where
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddRspImm8 where
  encode i :=
    ByteArray.mk #[0x48, 0x83, 0xC4, i.imm]
  step i s :=
    let dVal := s.gprs .rsp
    let sVal := signExtend8To64 i.imm
    let res := dVal + sVal
    let s' := s.setGpr64 .rsp res
    let s'' := s'.setFlagsAdd64 dVal sVal
    { s'' with rip := s.rip + 4 }
  toUops _ := [{ mnemonic := "ADD.rsp", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add rsp, byte {i.imm.toNat}"
  toLean i := s!"add_rsp {formatHex8 i.imm}"
  canFuzzHardware _ := false -- Stack pointer modifications cannot be executed in-place on host thread stack
  validationOracle _ := .nasmEncoding "Stack pointer modifications cannot be executed in-place on host thread stack -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases := curatedUInt8Cases.map AddRspImm8.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD RSP, imm32 instruction: increments stack pointer with 32-bit immediate to deallocate large stack frame. -/
structure AddRspImm32 where
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddRspImm32 where
  encode i :=
    ByteArray.mk #[0x48, 0x81, 0xC4] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.gprs .rsp
    let sVal := i.imm.toUInt64
    let res := dVal + sVal
    let s' := s.setGpr64 .rsp res
    let s'' := s'.setFlagsAdd64 dVal sVal
    { s'' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "ADD.rsp32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  -- The `dword` qualifier is load-bearing, not decorative: found while wiring
  -- `EncodingFuzzer.lean`'s registry-derived generator (P4(a),
  -- docs/X86_ISA_EXPANSION_PREREQUISITES.md). Without it, NASM's own assembler -- given
  -- unqualified "add rsp, 0" text -- silently prefers the shorter `83 /r ib` (imm8) encoding
  -- whenever the immediate value fits in a byte, diverging from `encode`'s fixed `81 /r id`
  -- (imm32) form and producing a false-positive byte mismatch that is a `toNASM` ambiguity, not
  -- a real encoding defect (`AddR64Imm8`/`AddRspImm8` already carry the analogous `byte`
  -- qualifier for exactly this reason; this form was simply never exercised against NASM before
  -- the registry-derived generator existed).
  toNASM i := s!"add rsp, dword {i.imm.toNat}"
  toLean i := s!"add_rsp32 {formatHex32 i.imm}"
  canFuzzHardware _ := false -- Stack pointer modifications cannot be executed in-place on host thread stack
  validationOracle _ := .nasmEncoding "Stack pointer modifications cannot be executed in-place on host thread stack -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases := curatedUInt32Cases.map AddRspImm32.mk
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r64, imm32: Adds sign-extended 32-bit immediate to destination register and updates condition flags. -/
structure AddR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x81, makeModRM 3 0 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let res := dVal + sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsAdd64 dVal sVal
    { s'' with rip := s.rip + 7 }
  toUops _ := [{ mnemonic := "ADD.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  -- `dword` qualifier: see `AddRspImm32.toNASM`'s comment above -- same NASM shortest-encoding
  -- ambiguity, same fix, found the same way.
  toNASM i := s!"add {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"add_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64ListNoRsp.map (AddR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (AddR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (AddR64Imm32.mk .r15 ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- ADD r64, r64 helper. -/
def add_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨AddR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- ADD r64, imm8 helper. -/
def add_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨AddR64Imm8.mk dst imm⟩

/- REF: intel-sdm#vol=1;sec=3.4;part=34-basic-program-execution-registers -/
/-- The existentially packaged ADD-imm8 step exposes exactly its architectural carry test. -/
theorem add_r64_imm8_step_cf (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    ((X86_64Instruction.step (add_r64_imm8 dst imm) s).cf = true) =
      (s.gprs dst + signExtend8To64 imm < s.gprs dst) := by
  change (((( { s with stdinBuffer := ByteArray.empty, incomingRequests := [] }.setGpr64 dst
    (s.gprs dst + signExtend8To64 imm)).setFlagsAdd64
      (s.gprs dst) (signExtend8To64 imm)).cf = true) : Prop) =
        (s.gprs dst + signExtend8To64 imm < s.gprs dst)
  exact X86_64MachineState.setFlagsAdd64_cf _ _ _

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- ADD r64, imm32 helper. -/
def add_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨AddR64Imm32.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- ADD RSP, imm8 helper. -/
def add_rsp (imm : UInt8) : AnyX86_64Instruction :=
  ⟨AddRspImm8.mk imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- ADD RSP, imm32 helper. -/
def add_rsp32 (imm : UInt32) : AnyX86_64Instruction :=
  ⟨AddRspImm32.mk imm⟩


/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r32, r32: Adds 32-bit source register to destination register with 64-bit zero-extension. -/
structure AddR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexNeeded := dstExt || srcExt
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x01, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := s.readGpr32 i.src
    let res := dVal + sVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsAdd32 dVal sVal
    let len := (if (reg32Code i.dst).2 || (reg32Code i.src).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, {i.src}"
  toLean i := s!"add_r32 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (AddR32R32.mk · .eax)) ++ (allReg32List.map (AddR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => AddR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r32, imm8: Adds sign-extended 8-bit immediate to 32-bit destination register with 64-bit zero-extension. -/
structure AddR32Imm8 where
  dst : Reg32
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR32Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x83, makeModRM 3 0 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt32
    let res := dVal + sVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsAdd32 dVal sVal
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"add_r32_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (AddR32Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AddR32Imm8.mk .eax ·)) ++
    (curatedUInt8Cases.map (AddR32Imm8.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r32, imm32: Adds 32-bit immediate to destination register with 64-bit zero-extension. -/
structure AddR32Imm32 where
  dst : Reg32
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR32Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let rexPrefix := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x81, makeModRM 3 0 dstCode] ++ uint32ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := i.imm
    let res := dVal + sVal
    let s' := s.setGpr32 i.dst res
    let s'' := s'.setFlagsAdd32 dVal sVal
    let len := (if (reg32Code i.dst).2 then 1 else 0) + 6
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"add_r32_imm32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg32 i.dst
  validationOracle i := if hwSafeReg32 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg32To64 i.dst) rng
  roundtripCases :=
    (allReg32List.map (AddR32Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (AddR32Imm32.mk .eax ·)) ++
    (curatedUInt32Cases.map (AddR32Imm32.mk .r15d ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r16, r16: Adds 16-bit source register to destination register, preserving upper 48 bits. -/
structure AddR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexNeeded := dstExt || srcExt
    let rexBytes := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x01, makeModRM 3 srcCode dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let res := dVal + sVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsAdd16 dVal sVal
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, {i.src}"
  toLean i := s!"add_r16 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (AddR16R16.mk · .ax)) ++ (allReg16List.map (AddR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => AddR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r16, imm8: Adds sign-extended 8-bit immediate to 16-bit destination register, preserving upper 48 bits. -/
structure AddR16Imm8 where
  dst : Reg16
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR16Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x83, makeModRM 3 0 dstCode, i.imm])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := (signExtend8To64 i.imm).toUInt16
    let res := dVal + sVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsAdd16 dVal sVal
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"add_r16_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (AddR16Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AddR16Imm8.mk .ax ·)) ++
    (curatedUInt8Cases.map (AddR16Imm8.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r16, imm16: Adds 16-bit immediate to destination register, preserving upper 48 bits. -/
structure AddR16Imm16 where
  dst : Reg16
  imm : UInt16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR16Imm16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let rexBytes := if dstExt then #[makeRex false false false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexBytes ++ #[0x81, makeModRM 3 0 dstCode]) ++ uint16ToLittleEndian i.imm
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := i.imm
    let res := dVal + sVal
    let s' := s.setGpr16 i.dst res
    let s'' := s'.setFlagsAdd16 dVal sVal
    let len := 1 + (if (reg16Code i.dst).2 then 1 else 0) + 4
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu16", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, word {i.imm.toNat}"
  toLean i := s!"add_r16_imm16 .{i.dst} {formatHex16 i.imm}"
  canFuzzHardware i := hwSafeReg16 i.dst
  validationOracle i := if hwSafeReg16 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg16To64 i.dst) rng
  roundtripCases :=
    (allReg16List.map (AddR16Imm16.mk · 0x0000)) ++ (curatedUInt16Cases.map (AddR16Imm16.mk .ax ·)) ++
    (curatedUInt16Cases.map (AddR16Imm16.mk .r15w ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r8, r8: Adds 8-bit source register to destination register, preserving upper 56 bits. -/
structure AddR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x00, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := s.readGpr8 i.src
    let res := dVal + sVal
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsAdd8 dVal sVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, {i.src}"
  toLean i := s!"add_r8 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (AddR8R8.mk · .al)) ++ (allReg8List.map (AddR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => AddR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=ADD;part=description -/
/-- ADD r8, imm8: Adds 8-bit immediate to destination register, preserving upper 56 bits. -/
structure AddR8Imm8 where
  dst : Reg8
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=ADD;part=operation -/
instance : X86_64Instruction AddR8Imm8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let rexNeeded := dstExt || dstMandatory
    let rexPrefix := if rexNeeded then #[makeRex false false false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x80, makeModRM 3 0 dstCode, i.imm]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := i.imm
    let res := dVal + sVal
    let s' := s.setGpr8 i.dst res
    let s'' := s'.setFlagsAdd8 dVal sVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.dst).2.2
    let len := (if rexNeeded then 1 else 0) + 3
    { s'' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "ADD.alu8", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"add {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"add_r8_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg8 i.dst
  validationOracle i := if hwSafeReg8 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm (reg8To64 i.dst) rng
  roundtripCases :=
    (allReg8List.map (AddR8Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AddR8Imm8.mk .al ·)) ++
    (curatedUInt8Cases.map (AddR8Imm8.mk .r15b ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def add_r32 (dst src : Reg32) : AnyX86_64Instruction := ⟨AddR32R32.mk dst src⟩
def add_r32_imm8 (dst : Reg32) (imm : UInt8) : AnyX86_64Instruction := ⟨AddR32Imm8.mk dst imm⟩
def add_r32_imm32 (dst : Reg32) (imm : UInt32) : AnyX86_64Instruction := ⟨AddR32Imm32.mk dst imm⟩
def add_r16 (dst src : Reg16) : AnyX86_64Instruction := ⟨AddR16R16.mk dst src⟩
def add_r16_imm8 (dst : Reg16) (imm : UInt8) : AnyX86_64Instruction := ⟨AddR16Imm8.mk dst imm⟩
def add_r16_imm16 (dst : Reg16) (imm : UInt16) : AnyX86_64Instruction := ⟨AddR16Imm16.mk dst imm⟩
def add_r8 (dst src : Reg8) : AnyX86_64Instruction := ⟨AddR8R8.mk dst src⟩
def add_r8_imm8 (dst : Reg8) (imm : UInt8) : AnyX86_64Instruction := ⟨AddR8Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the ADD family: `0x01` (ADD r64/r32/r16), `0x00` (ADD r8), `0x80 /0` (ADD r8, imm8),
    `0x81 /0` (ADD imm32/imm16), and `0x83 /0` (ADD imm8). Errors for any other byte pattern. -/
def addTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parsePrefixesAndOpcode bytes offset with
  | .error e => .error e
  | .ok (has0x66, _, rexW, rexR, _, rexB, opcode, opOffset) =>
    if has0x66 then
      if opcode == 0x01 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, pos) =>
          let dst := codeToReg16 rm rexB
          let src := codeToReg16 reg rexR
          .ok (add_r16 dst src, pos - offset)
      else if opcode == 0x83 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          if reg == 0 then
            let dst := codeToReg16 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (add_r16_imm8 dst imm8, (modPos + 1) - offset)
          else .error "addTryDecode: 0x83 sub-opcode is not ADD"
      else if opcode == 0x81 then
        match readModRM bytes opOffset with
        | .error e => .error e
        | .ok (_, reg, rm, modPos) =>
          if reg == 0 then
            let dst := codeToReg16 rm rexB
            match readUInt16LE bytes modPos with
            | .error e => .error e
            | .ok imm16 => .ok (add_r16_imm16 dst imm16, (modPos + 2) - offset)
          else .error "addTryDecode: 0x81 sub-opcode is not ADD"
      else .error s!"addTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} with 0x66 prefix is not ADD"
    else if opcode == 0x00 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg8 rm rexB
        let src := codeToReg8 reg rexR
        .ok (add_r8 dst src, pos - offset)
    else if opcode == 0x80 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 0 then
          let dst := codeToReg8 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 => .ok (add_r8_imm8 dst imm8, (modPos + 1) - offset)
        else .error "addTryDecode: 0x80 sub-opcode is not ADD"
    else if opcode == 0x01 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if rexW then
          let dst := codeToReg64 rm rexB
          let src := codeToReg64 reg rexR
          .ok (add_r64 dst src, pos - offset)
        else
          let dst := codeToReg32 rm rexB
          let src := codeToReg32 reg rexR
          .ok (add_r32 dst src, pos - offset)
    else if opcode == 0x81 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 0 then
          if rexW then
            let dst := codeToReg64 rm rexB
            match readUInt32LE bytes modPos with
            | .error e => .error e
            | .ok imm32 =>
              let pos := modPos + 4
              if dst == .rsp && !rexB then .ok (add_rsp32 imm32, pos - offset)
              else .ok (add_r64_imm32 dst imm32, pos - offset)
          else
            let dst := codeToReg32 rm rexB
            match readUInt32LE bytes modPos with
            | .error e => .error e
            | .ok imm32 => .ok (add_r32_imm32 dst imm32, (modPos + 4) - offset)
        else .error "addTryDecode: 0x81 sub-opcode is not ADD"
    else if opcode == 0x83 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 0 then
          if rexW then
            let dst := codeToReg64 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 =>
              let pos := modPos + 1
              if dst == .rsp && !rexB then .ok (add_rsp imm8, pos - offset)
              else .ok (add_r64_imm8 dst imm8, pos - offset)
          else
            let dst := codeToReg32 rm rexB
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok imm8 => .ok (add_r32_imm8 dst imm8, (modPos + 1) - offset)
        else .error "addTryDecode: 0x83 sub-opcode is not ADD"
    else
      .error s!"addTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not ADD"

end Gasm.Targets.X86_64.Instructions


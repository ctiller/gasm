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

/- REF: intel-sdm#vol=2;instr=SUB;part=description -/
/-- SUB RSP, imm8 instruction: decrements stack pointer to allocate stack frame. -/
structure SubRspImm8 where
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SUB;part=operation -/
instance : X86_64Instruction SubRspImm8 where
  encode i :=
    ByteArray.mk #[0x48, 0x83, 0xEC, i.imm]

  step i s :=
    let dVal := s.gprs .rsp
    let sVal := signExtend8To64 i.imm
    let res := dVal - sVal
    let s' := s.setGpr64 .rsp res
    let s'' := s'.setFlagsSub64 dVal sVal
    { s'' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "SUB.rsp", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"sub rsp, byte {i.imm.toNat}"
  toLean i := s!"sub_rsp {formatHex8 i.imm}"
  canFuzzHardware _ := false -- Stack pointer modifications cannot be executed in-place on host thread stack
  validationOracle _ := .nasmEncoding "Stack pointer modifications cannot be executed in-place on host thread stack -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases := curatedUInt8Cases.map SubRspImm8.mk

/- REF: intel-sdm#vol=2;instr=SUB;part=description -/
/-- SUB r64, r64: Subtracts 64-bit source register from destination register and updates condition flags. -/
structure SubR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SUB;part=operation -/
instance : X86_64Instruction SubR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x29, makeModRM 3 srcCode dstCode]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let res := dVal - sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsSub64 dVal sVal
    { s'' with rip := s.rip + 3 }

  toUops i :=
    if i.dst == i.src then
      -- Zeroing idiom: recognized by modern frontends
      [{ mnemonic := "SUB.zeroing", uopClass := .intALU, eligiblePorts := [], latencyCycles := 0, reciprocalThroughput := 0.0 }]
    else
      [{ mnemonic := "SUB.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"sub {i.dst}, {i.src}"
  toLean i := s!"sub_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (SubR64R64.mk · .rax)) ++ (allReg64List.map (SubR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => SubR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=SUB;part=description -/
/-- SUB r64, imm8: Subtracts sign-extended 8-bit immediate from destination register and updates condition flags. -/
structure SubR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SUB;part=operation -/
instance : X86_64Instruction SubR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x83, makeModRM 3 5 dstCode, i.imm]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtend8To64 i.imm
    let res := dVal - sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsSub64 dVal sVal
    { s'' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "SUB.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"sub {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"sub_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64ListNoRsp.map (SubR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (SubR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (SubR64Imm8.mk .r15 ·))

/- REF: intel-sdm#vol=2;instr=SUB;part=description -/
/-- SUB RSP, imm32 instruction: decrements stack pointer with 32-bit immediate to allocate large stack frame. -/
structure SubRspImm32 where
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SUB;part=operation -/
instance : X86_64Instruction SubRspImm32 where
  encode i :=
    ByteArray.mk #[0x48, 0x81, 0xEC] ++ uint32ToLittleEndian i.imm

  step i s :=
    let dVal := s.gprs .rsp
    let sVal := i.imm.toUInt64
    let res := dVal - sVal
    let s' := s.setGpr64 .rsp res
    let s'' := s'.setFlagsSub64 dVal sVal
    { s'' with rip := s.rip + 7 }

  toUops _ := [{ mnemonic := "SUB.rsp32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  -- `dword` qualifier: see `Add.lean`'s `AddRspImm32.toNASM` comment -- same NASM
  -- shortest-encoding ambiguity (found via P4(a)'s registry-derived encoding fuzzer,
  -- docs/X86_ISA_EXPANSION_PREREQUISITES.md), same fix.
  toNASM i := s!"sub rsp, dword {i.imm.toNat}"
  toLean i := s!"sub_rsp32 {formatHex32 i.imm}"
  canFuzzHardware _ := false -- Stack pointer modifications cannot be executed in-place on host thread stack
  validationOracle _ := .nasmEncoding "Stack pointer modifications cannot be executed in-place on host thread stack -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases := curatedUInt32Cases.map SubRspImm32.mk

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SUB RSP, imm8 helper. -/
def sub_rsp (imm : UInt8) : AnyX86_64Instruction :=
  ⟨SubRspImm8.mk imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SUB RSP, imm32 helper. -/
def sub_rsp32 (imm : UInt32) : AnyX86_64Instruction :=
  ⟨SubRspImm32.mk imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SUB r64, r64 helper. -/
def sub_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨SubR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SUB r64, imm8 helper. -/
def sub_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨SubR64Imm8.mk dst imm⟩

/- REF: intel-sdm#vol=2;instr=SUB;part=description -/
/-- SUB r64, imm32: Subtracts sign-extended 32-bit immediate from destination register and updates condition flags. -/
structure SubR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=SUB;part=operation -/
instance : X86_64Instruction SubR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x81, makeModRM 3 5 dstCode] ++ uint32ToLittleEndian i.imm

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let res := dVal - sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsSub64 dVal sVal
    { s'' with rip := s.rip + 7 }

  toUops _ := [{ mnemonic := "SUB.imm32", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"sub {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"sub_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64ListNoRsp.map (SubR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (SubR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (SubR64Imm32.mk .r15 ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- SUB r64, imm32 helper. -/
def sub_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨SubR64Imm32.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the SUB family: `0x29` (SUB r64, r64), `0x81 /5` (SUB r64, imm32,
    canonicalizing to `SubRspImm32` for an unextended RSP destination), and `0x83 /5` (SUB r64,
    imm8, same RSP canonicalization). Errors for any other byte pattern. -/
def subTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x29 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg64 rm rexB
        let src := codeToReg64 reg rexR
        .ok (sub_r64 dst src, pos - offset)
    else if opcode == 0x81 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 5 then
          let dst := codeToReg64 rm rexB
          match readUInt32LE bytes modPos with
          | .error e => .error e
          | .ok imm32 =>
            let pos := modPos + 4
            if dst == .rsp && !rexB then .ok (sub_rsp32 imm32, pos - offset)
            else .ok (sub_r64_imm32 dst imm32, pos - offset)
        else
          .error "subTryDecode: 0x81 sub-opcode is not SUB"
    else if opcode == 0x83 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 5 then
          let dst := codeToReg64 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 =>
            let pos := modPos + 1
            if dst == .rsp && !rexB then .ok (sub_rsp imm8, pos - offset)
            else .ok (sub_r64_imm8 dst imm8, pos - offset)
        else
          .error "subTryDecode: 0x83 sub-opcode is not SUB"
    else
      .error s!"subTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not SUB"

end Gasm.Targets.X86_64.Instructions

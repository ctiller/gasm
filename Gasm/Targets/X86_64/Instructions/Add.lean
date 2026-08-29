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

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the ADD family: `0x01` (ADD r64, r64), `0x81 /0` (ADD r64, imm32,
    canonicalizing to `AddRspImm32` when the destination is RSP with REX.B unset, mirroring
    `encode`'s own RSP special case), and `0x83 /0` (ADD r64, imm8, same RSP canonicalization).
    Returns an error (not this family's opcode/sub-opcode) for every other byte pattern, so the
    thin dispatcher in `Decoder.lean` falls through to the next family. -/
def addTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: deliberately nested `match` rather than `do`-notation: `AnyX86_64Instruction` (the
  -- payload of this function's own return type) lives a universe above the `Bool`/`UInt8`/`Nat`
  -- payloads `parseRexAndOpcode`/`readModRM`/`readUInt32LE` return, and `do`-notation's generic
  -- `Bind`/`Monad` typeclass resolution requires every bind in one chain to share a single
  -- universe — the same reason `Decoder.lean`'s original monolithic decoder used explicit
  -- `match` chains throughout instead of `do`-notation.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x01 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg64 rm rexB
        let src := codeToReg64 reg rexR
        .ok (add_r64 dst src, pos - offset)
    else if opcode == 0x81 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 0 then
          let dst := codeToReg64 rm rexB
          match readUInt32LE bytes modPos with
          | .error e => .error e
          | .ok imm32 =>
            let pos := modPos + 4
            if dst == .rsp && !rexB then .ok (add_rsp32 imm32, pos - offset)
            else .ok (add_r64_imm32 dst imm32, pos - offset)
        else
          .error "addTryDecode: 0x81 sub-opcode is not ADD"
    else if opcode == 0x83 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 0 then
          let dst := codeToReg64 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 =>
            let pos := modPos + 1
            if dst == .rsp && !rexB then .ok (add_rsp imm8, pos - offset)
            else .ok (add_r64_imm8 dst imm8, pos - offset)
        else
          .error "addTryDecode: 0x83 sub-opcode is not ADD"
    else
      .error s!"addTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not ADD"

end Gasm.Targets.X86_64.Instructions

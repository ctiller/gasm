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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (AndR64R64.mk · .rax)) ++ (allReg64List.map (AndR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => AndR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, imm8 helper. -/
def and_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨AndR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, reg64 helper. -/
def and_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨AndR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the AND family: `0x21` (AND r64, r64) and `0x83 /4` (AND r64, imm8).
    This codebase has no AND r64, imm32 form (no `0x81 /4` case). Errors for any other byte
    pattern. -/
def andTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x21 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg64 rm rexB
        let src := codeToReg64 reg rexR
        .ok (and_r64 dst src, pos - offset)
    else if opcode == 0x83 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, modPos) =>
        if reg == 4 then
          let dst := codeToReg64 rm rexB
          match readUInt8 bytes modPos with
          | .error e => .error e
          | .ok imm8 => .ok (and_r64_imm8 dst imm8, (modPos + 1) - offset)
        else
          .error "andTryDecode: 0x83 sub-opcode is not AND"
    else
      .error s!"andTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not AND"

end Gasm.Targets.X86_64.Instructions

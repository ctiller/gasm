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

/- REF: intel-sdm#vol=2;instr=LEA;part=description -/
/-- LEA reg64, [RIP + disp32] instruction: loads effective address relative to next RIP. -/
structure LeaRipRel where
  dst  : Reg64
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=LEA;part=operation -/
instance : X86_64Instruction LeaRipRel where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    -- dst occupies ModRM.reg (rm=5 is the fixed RIP-relative escape), so its extension bit is
    -- REX.R, not REX.B. This was previously swapped, silently misencoding `lea_rip` with any
    -- extended (r8-r15) destination register (caught by the exhaustive roundtripCases gate).
    let rex := makeRex true dstExt false false
    let modrm := makeModRM 0 dstCode 5
    ByteArray.mk #[rex, 0x8D, modrm] ++ int32ToLittleEndian i.disp
  step i s :=
    let nextRip := s.rip + 7
    let effAddr := nextRip + signExtend32To64 i.disp
    let s' := s.setGpr64 i.dst effAddr
    { s' with rip := nextRip }
  toUops _ := [{ mnemonic := "LEA.rip", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"lea {i.dst}, [rel $+7 {formatDisp32 i.disp}]"
  toLean i := s!"lea_rip .{i.dst} ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "RIP-relative effective-address computation depends on the harness's own code position, not a fuzzable operand -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (LeaRipRel.mk · 0)) ++ (curatedInt32Cases.map (LeaRipRel.mk .rax ·)) ++
    (curatedInt32Cases.map (LeaRipRel.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=LEA;part=description -/
/-- LEA reg64, [RSP + disp8] instruction: loads effective address relative to stack pointer. -/
structure LeaRspDisp where
  dst  : Reg64
  disp : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=LEA;part=operation -/
instance : X86_64Instruction LeaRspDisp where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let rex := makeRex true dstExt false false
    let sib := makeSIB 0 4 4
    if i.disp == 0 then
      let modrm := makeModRM 0 dstCode 4
      ByteArray.mk #[rex, 0x8D, modrm, sib]
    else
      let modrm := makeModRM 1 dstCode 4
      ByteArray.mk #[rex, 0x8D, modrm, sib, i.disp]
  step i s :=
    let effAddr := s.rsp + signExtend8To64 i.disp
    let s' := s.setGpr64 i.dst effAddr
    let len := if i.disp == 0 then 4 else 5
    { s' with rip := s.rip + len }
  toUops _ := [{ mnemonic := "LEA.rsp", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i :=
    if i.disp == 0 then
      s!"lea {i.dst}, [rsp]"
    else
      s!"lea {i.dst}, [rsp {formatDisp8 i.disp}]"
  toLean i := s!"lea_rsp .{i.dst} {formatHex8 i.disp}"
  canFuzzHardware _ := false -- Stack pointer relative address computation depends on host process stack address
  validationOracle _ := .nasmEncoding "Stack pointer relative address computation depends on host process stack address -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases :=
    (allReg64List.map (LeaRspDisp.mk · 0)) ++ (curatedUInt8Cases.map (LeaRspDisp.mk .rax ·)) ++
    (curatedUInt8Cases.map (LeaRspDisp.mk .r15 ·))
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=LEA;part=description -/
/-- LEA reg64, [RSP + disp32] instruction: loads effective address relative to stack pointer with 32-bit displacement. -/
structure LeaRspDisp32 where
  dst  : Reg64
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=LEA;part=operation -/
instance : X86_64Instruction LeaRspDisp32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let rex := makeRex true dstExt false false
    let sib := makeSIB 0 4 4
    let modrm := makeModRM 2 dstCode 4
    ByteArray.mk #[rex, 0x8D, modrm, sib] ++ int32ToLittleEndian i.disp
  step i s :=
    let effAddr := s.rsp + signExtend32To64 i.disp
    let s' := s.setGpr64 i.dst effAddr
    { s' with rip := s.rip + 8 }
  toUops _ := [{ mnemonic := "LEA.rsp32", uopClass := .intALU, eligiblePorts := [.p1, .p5], latencyCycles := 1, reciprocalThroughput := 0.5 }]
  toNASM i := s!"lea {i.dst}, [rsp {formatDisp32 i.disp}]"
  toLean i := s!"lea_rsp32 .{i.dst} ({i.disp})"
  canFuzzHardware _ := false -- Stack pointer relative address computation depends on host process stack address
  validationOracle _ := .nasmEncoding "Stack pointer relative address computation depends on host process stack address -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases :=
    (allReg64List.map (LeaRspDisp32.mk · 0)) ++ (curatedInt32Cases.map (LeaRspDisp32.mk .rax ·)) ++
    (curatedInt32Cases.map (LeaRspDisp32.mk .r15 ·))
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- LEA reg64, [RIP + disp32] helper. -/
def lea_rip (dst : Reg64) (disp : Int32) : AnyX86_64Instruction :=
  ⟨LeaRipRel.mk dst disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- LEA reg64, [RSP + disp8] helper. -/
def lea_rsp (dst : Reg64) (disp : UInt8) : AnyX86_64Instruction :=
  ⟨LeaRspDisp.mk dst disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- LEA reg64, [RSP + disp32] helper. -/
def lea_rsp32 (dst : Reg64) (disp : Int32) : AnyX86_64Instruction :=
  ⟨LeaRspDisp32.mk dst disp⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the LEA family: `0x8D` with `mod=0,rm=5` (RIP-relative),
    `mod=0/1/2,rm=4` (SIB-encoded RSP-relative, disp0/disp8/disp32). Rejects (rather than
    misdecodes) an R12-based SIB-base-4 encoding (`rexB` set), since `LeaRspDisp`/`LeaRspDisp32`
    have no base-register field to represent R12 — mirrors the soundness fix documented on the
    original monolithic decoder's 0x8D branch. Errors for any other byte pattern. -/
def leaTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (hasRex, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x8D then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (mod, reg, rm, modPos) =>
        let dst := codeToReg64 reg (if hasRex then rexR else false)
        if mod == 0 && rm == 5 then
          match readInt32LE bytes modPos with
          | .error e => .error e
          | .ok disp32 => .ok (lea_rip dst disp32, (modPos + 4) - offset)
        else if mod == 0 && rm == 4 then
          if rexB then
            .error "leaTryDecode: unsupported base register (R12 via REX.B) for 0x8D SIB form"
          else
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok _sib => .ok (lea_rsp dst 0, (modPos + 1) - offset)
        else if mod == 1 && rm == 4 then
          if rexB then
            .error "leaTryDecode: unsupported base register (R12 via REX.B) for 0x8D SIB form"
          else
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok _sib =>
              match readUInt8 bytes (modPos + 1) with
              | .error e => .error e
              | .ok disp8 => .ok (lea_rsp dst disp8, (modPos + 2) - offset)
        else if mod == 2 && rm == 4 then
          if rexB then
            .error "leaTryDecode: unsupported base register (R12 via REX.B) for 0x8D SIB form"
          else
            match readUInt8 bytes modPos with
            | .error e => .error e
            | .ok _sib =>
              match readInt32LE bytes (modPos + 1) with
              | .error e => .error e
              | .ok disp32 => .ok (lea_rsp32 dst disp32, (modPos + 5) - offset)
        else
          .error "leaTryDecode: unsupported addressing mode for 0x8D LEA"
    else
      .error s!"leaTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not LEA"

end Gasm.Targets.X86_64.Instructions

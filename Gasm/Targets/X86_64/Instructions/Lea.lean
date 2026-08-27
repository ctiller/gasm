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
  generateFuzzStates _ rng := ([], rng)
  roundtripCases :=
    (allReg64List.map (LeaRipRel.mk · 0)) ++ (curatedInt32Cases.map (LeaRipRel.mk .rax ·)) ++
    (curatedInt32Cases.map (LeaRipRel.mk .r15 ·))

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
      s!"lea {i.dst}, [rsp + 0x{String.ofList (Nat.toDigits 16 i.disp.toNat)}]"
  toLean i := s!"lea_rsp .{i.dst} {formatHex8 i.disp}"
  canFuzzHardware _ := false -- Stack pointer relative address computation depends on host process stack address
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases :=
    (allReg64List.map (LeaRspDisp.mk · 0)) ++ (curatedUInt8Cases.map (LeaRspDisp.mk .rax ·)) ++
    (curatedUInt8Cases.map (LeaRspDisp.mk .r15 ·))

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
  generateFuzzStates _ rng := generateStandardFuzzStatesForImm .rsp rng
  roundtripCases :=
    (allReg64List.map (LeaRspDisp32.mk · 0)) ++ (curatedInt32Cases.map (LeaRspDisp32.mk .rax ·)) ++
    (curatedInt32Cases.map (LeaRspDisp32.mk .r15 ·))

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

end Gasm.Targets.X86_64.Instructions

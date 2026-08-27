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
  toNASM i := s!"and {i.dst}, 0x{String.ofList (Nat.toDigits 16 i.imm.toNat)}"
  toLean i := s!"and_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for AND according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (AndR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (AndR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (AndR64Imm8.mk .r15 ·))

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
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (AndR64R64.mk · .rax)) ++ (allReg64List.map (AndR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => AndR64R64.mk p.1 p.2)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, imm8 helper. -/
def and_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨AndR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- AND reg64, reg64 helper. -/
def and_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨AndR64R64.mk dst src⟩

end Gasm.Targets.X86_64.Instructions

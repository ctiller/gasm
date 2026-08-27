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

/- REF: intel-sdm#vol=2;instr=OR;part=description -/
/-- OR r64, r64: Bitwise inclusive OR between destination and source 64-bit registers. -/
structure OrR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OR;part=operation -/
instance : X86_64Instruction OrR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x09, makeModRM 3 srcCode dstCode]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let res := dVal ||| sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsLogic64 res
    { s'' with rip := s.rip + 3 }

  toUops _ := [{ mnemonic := "OR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"or {i.dst}, {i.src}"
  toLean i := s!"or_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for OR according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (OrR64R64.mk · .rax)) ++ (allReg64List.map (OrR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => OrR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=OR;part=description -/
/-- OR r64, imm8: Bitwise inclusive OR between destination 64-bit register and sign-extended 8-bit immediate. -/
structure OrR64Imm8 where
  dst : Reg64
  imm : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OR;part=operation -/
instance : X86_64Instruction OrR64Imm8 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x83, makeModRM 3 1 dstCode, i.imm]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtend8To64 i.imm
    let res := dVal ||| sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsLogic64 res
    { s'' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "OR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"or {i.dst}, byte {i.imm.toNat}"
  toLean i := s!"or_r64_imm8 .{i.dst} {formatHex8 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for OR according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (OrR64Imm8.mk · 0x00)) ++ (curatedUInt8Cases.map (OrR64Imm8.mk .rax ·)) ++
    (curatedUInt8Cases.map (OrR64Imm8.mk .r15 ·))

/- REF: intel-sdm#vol=2;instr=OR;part=description -/
/-- OR r64, imm32: Bitwise inclusive OR between destination 64-bit register and sign-extended 32-bit immediate. -/
structure OrR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OR;part=operation -/
instance : X86_64Instruction OrR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0x81, makeModRM 3 1 dstCode] ++ uint32ToLittleEndian i.imm

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let res := dVal ||| sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsLogic64 res
    { s'' with rip := s.rip + 7 }

  toUops _ := [{ mnemonic := "OR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"or {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"or_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for OR according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (OrR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (OrR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (OrR64Imm32.mk .r15 ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OR r64, r64 helper. -/
def or_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨OrR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OR r64, imm8 helper. -/
def or_r64_imm8 (dst : Reg64) (imm : UInt8) : AnyX86_64Instruction :=
  ⟨OrR64Imm8.mk dst imm⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OR r64, imm32 helper. -/
def or_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨OrR64Imm32.mk dst imm⟩

end Gasm.Targets.X86_64.Instructions

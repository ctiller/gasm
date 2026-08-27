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

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r64, r64: Computes bitwise logical AND between two 64-bit registers, sets condition flags (ZF, SF, PF), clears CF and OF, without modifying registers. -/
structure TestR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x85, makeModRM 3 srcCode dstCode]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic64 temp
    { s' with rip := s.rip + 3 }

  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, {i.src}"
  toLean i := s!"test_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (TestR64R64.mk · .rax)) ++ (allReg64List.map (TestR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => TestR64R64.mk p.1 p.2)

/- REF: intel-sdm#vol=2;instr=TEST;part=description -/
/-- TEST r64, imm32: Computes bitwise logical AND between 64-bit register and sign-extended 32-bit immediate, sets condition flags without modifying registers. -/
structure TestR64Imm32 where
  dst : Reg64
  imm : UInt32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=TEST;part=operation -/
instance : X86_64Instruction TestR64Imm32 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xF7, makeModRM 3 0 dstCode] ++ uint32ToLittleEndian i.imm

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := signExtendUInt32To64 i.imm
    let temp := dVal &&& sVal
    let s' := s.setFlagsLogic64 temp
    { s' with rip := s.rip + 7 }

  toUops _ := [{ mnemonic := "TEST.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"test {i.dst}, dword {i.imm.toNat}"
  toLean i := s!"test_r64_imm32 .{i.dst} {formatHex32 i.imm}"
  undefinedFlagsMask _ := 16 -- AF is undefined for TEST according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst
  generateFuzzStates i rng := generateStandardFuzzStatesForImm i.dst rng
  roundtripCases :=
    (allReg64List.map (TestR64Imm32.mk · 0x00000000)) ++ (curatedUInt32Cases.map (TestR64Imm32.mk .rax ·)) ++
    (curatedUInt32Cases.map (TestR64Imm32.mk .r15 ·))

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- TEST r64, r64 helper. -/
def test_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨TestR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- TEST r64, imm32 helper. -/
def test_r64_imm32 (dst : Reg64) (imm : UInt32) : AnyX86_64Instruction :=
  ⟨TestR64Imm32.mk dst imm⟩

end Gasm.Targets.X86_64.Instructions

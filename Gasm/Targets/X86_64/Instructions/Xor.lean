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

/- REF: intel-sdm#vol=2;instr=XOR;part=description -/
/-- XOR reg32, reg32 instruction: clears/xors general-purpose register. -/
structure XorR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XOR;part=operation -/
instance : X86_64Instruction XorR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexNeeded := dstExt || srcExt
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x31, makeModRM 3 srcCode dstCode]

  step i s :=
    let dVal := (s.gprs (reg32To64 i.dst)).toUInt32
    let sVal := (s.gprs (reg32To64 i.src)).toUInt32
    let res := dVal ^^^ sVal
    let s' := (s.setGpr32 i.dst res).setFlagsLogic 32 res.toUInt64
    let len := if (reg32Code i.dst).2 || (reg32Code i.src).2 then 3 else 2
    { s' with rip := s.rip + len }

  toUops i :=
    if i.dst == i.src then
      -- Zeroing idiom: eliminated in the Rename stage with 0 execution latency and 0 execution port allocation
      [{ mnemonic := "XOR.zeroing", uopClass := .intALU, eligiblePorts := [], latencyCycles := 0, reciprocalThroughput := 0.0 }]
    else
      [{ mnemonic := "XOR.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"xor {i.dst}, {i.src}"
  toLean i := s!"xor_r32 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 16 -- AF is undefined for XOR according to Intel SDM
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (XorR32R32.mk · .eax)) ++ (allReg32List.map (XorR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => XorR32R32.mk p.1 p.2)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XOR reg32, reg32 helper. -/
def xor_r32 (dst src : Reg32) : AnyX86_64Instruction :=
  ⟨XorR32R32.mk dst src⟩

end Gasm.Targets.X86_64.Instructions

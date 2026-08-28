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

/- REF: intel-sdm#vol=2;instr=XCHG;part=description -/
/-- XCHG r64, r64: Swaps the contents of two 64-bit general-purpose registers without affecting condition flags. -/
structure XchgR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XCHG;part=operation -/
instance : X86_64Instruction XchgR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x87, makeModRM 3 srcCode dstCode]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let s' := (s.setGpr64 i.dst sVal).setGpr64 i.src dVal
    { s' with rip := s.rip + 3 }

  toUops _ := [
    { mnemonic := "XCHG.alu1", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "XCHG.alu2", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"xchg {i.dst}, {i.src}"
  toLean i := s!"xchg_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (XchgR64R64.mk · .rax)) ++ (allReg64List.map (XchgR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => XchgR64R64.mk p.1 p.2)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XCHG r64, r64 helper. -/
def xchg_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨XchgR64R64.mk dst src⟩

end Gasm.Targets.X86_64.Instructions

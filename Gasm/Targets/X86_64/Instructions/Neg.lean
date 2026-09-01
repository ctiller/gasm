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

/- REF: intel-sdm#vol=2;instr=NEG;part=description -/
/-- NEG r64: Replaces the value of destination 64-bit register with its two's complement (0 - val) and updates arithmetic flags. -/
structure NegR64 where
  dst : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=NEG;part=operation -/
instance : X86_64Instruction NegR64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    ByteArray.mk #[makeRex true false false dstExt, 0xF7, makeModRM 3 3 dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let res := 0 - dVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsNeg64 dVal
    { s'' with rip := s.rip + 3 }
  toUops _ := [{ mnemonic := "NEG.alu", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }]
  toNASM i := s!"neg {i.dst}"
  toLean i := s!"neg_r64 .{i.dst}"
  canFuzzHardware i := hwSafeReg64 i.dst
  validationOracle i := if hwSafeReg64 i.dst then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor1Reg i.dst rng
  roundtripCases := allReg64List.map NegR64.mk
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- NEG r64 helper. -/
def neg_r64 (dst : Reg64) : AnyX86_64Instruction :=
  ⟨NegR64.mk dst⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Declarative decoding rules for the NEG family: `0xF7 /3` (NEG r64). -/
def negDecodeRules : List DecodeRule := [
  { opcode := .one 0xF7,
    modrmReg := some 3,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "neg_r64: missing ModR/M byte"
      | some m =>
        let dst := codeToReg64 m.rm ctx.rexB
        .ok (neg_r64 dst, m.pos - ctx.startOffset)
  }
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the NEG family, evaluating its declarative rules. -/
def negTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules negDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions

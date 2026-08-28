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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor1Reg i.dst rng
  roundtripCases := allReg64List.map NegR64.mk

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- NEG r64 helper. -/
def neg_r64 (dst : Reg64) : AnyX86_64Instruction :=
  ⟨NegR64.mk dst⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the NEG family: `0xF7 /3` (the Group 3 opcode NEG shares with
    TEST/NOT/DIV, disambiguated by ModR/M.reg). Errors for any other byte pattern. -/
def negTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, rexB, opcode, opOffset) =>
    if opcode == 0xF7 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        if reg == 3 then
          let dst := codeToReg64 rm rexB
          .ok (neg_r64 dst, pos - offset)
        else
          .error "negTryDecode: 0xF7 sub-opcode is not NEG"
    else
      .error s!"negTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not NEG"

end Gasm.Targets.X86_64.Instructions

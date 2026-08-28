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

/- REF: intel-sdm#vol=2;instr=IMUL;part=description -/
/-- IMUL r64, r64: Signed two-operand 64-bit integer multiplication with 64-bit result, setting CF and OF on signed truncation. -/
structure ImulR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IMUL;part=operation -/
instance : X86_64Instruction ImulR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true dstExt false srcExt, 0x0F, 0xAF, makeModRM 3 dstCode srcCode]

  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let res := dVal * sVal
    let s' := s.setGpr64 i.dst res
    let s'' := s'.setFlagsImul64 dVal sVal
    { s'' with rip := s.rip + 4 }

  toUops _ := [{ mnemonic := "IMUL.alu", uopClass := .intALU, eligiblePorts := [.p1], latencyCycles := 3, reciprocalThroughput := 1.0 }]
  toNASM i := s!"imul {i.dst}, {i.src}"
  toLean i := s!"imul_r64 .{i.dst} .{i.src}"
  undefinedFlagsMask _ := 0xD4 -- PF, AF, ZF, SF are undefined according to Intel SDM
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (ImulR64R64.mk · .rax)) ++ (allReg64List.map (ImulR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => ImulR64R64.mk p.1 p.2)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IMUL r64, r64 helper. -/
def imul_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨ImulR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-design-only-not-implemented-by-this-change -/
/-- Co-located decoder for the IMUL family: `0x0F 0xAF` (IMUL r64, r64). Errors for any other
    byte pattern. -/
def imulTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x0F then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok op2 =>
        if op2 == 0xAF then
          match readModRM bytes (opOffset + 1) with
          | .error e => .error e
          | .ok (_, reg, rm, pos) =>
            let dst := codeToReg64 reg rexR
            let src := codeToReg64 rm rexB
            .ok (imul_r64 dst src, pos - offset)
        else
          .error "imulTryDecode: 0x0F sub-opcode is not IMUL"
    else
      .error s!"imulTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not IMUL"

end Gasm.Targets.X86_64.Instructions

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
/-- XCHG r64, r64: Swaps the contents of two 64-bit general-purpose registers without affecting condition flags.

NOTE for future authors (`docs/MEMORY_MODEL.md` §§4–5.1, stage M2-X): this reg-reg form touches no memory and
carries no atomicity semantics — `memAccesses` is honestly `[]`. XCHG with a *memory* operand is
architecturally LOCK'd on x86 (implicitly atomic, with or without the prefix; intel-sdm XCHG
description). Memory forms land with M2-X and declare one `.atomicRmw` event under that model.
The portable Linux futex/mutex baseline specifically requires a naturally aligned 32-bit memory
form and practical 32-bit compare-exchange support; 64-bit forms may be added for independent ISA
coverage. Adding either outside M2-X would create an unannotated atomic. -/
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
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact or RDTSC harness exists yet, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (XchgR64R64.mk · .rax)) ++ (allReg64List.map (XchgR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => XchgR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XCHG r64, r64 helper. -/
def xchg_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨XchgR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the XCHG family: `0x87` (XCHG r64, r64). Errors for any other byte
    pattern. -/
def xchgTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, rexR, _, rexB, opcode, opOffset) =>
    if opcode == 0x87 then
      match readModRM bytes opOffset with
      | .error e => .error e
      | .ok (_, reg, rm, pos) =>
        let dst := codeToReg64 rm rexB
        let src := codeToReg64 reg rexR
        .ok (xchg_r64 dst src, pos - offset)
    else
      .error s!"xchgTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not XCHG"

end Gasm.Targets.X86_64.Instructions

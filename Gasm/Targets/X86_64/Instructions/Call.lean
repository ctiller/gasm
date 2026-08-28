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

/- REF: intel-sdm#vol=2;instr=CALL;part=description -/
/-- CALL [RIP + disp32] instruction: indirect near call through memory displacement. -/
structure CallRipRel where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
instance : X86_64Instruction CallRipRel where
  encode i :=
    ByteArray.mk #[0xFF, 0x15] ++ int32ToLittleEndian i.disp

  step i s :=
    let nextRip := s.rip + 6
    let targetIat := nextRip + signExtend32To64 i.disp
    let targetFunc := s.read64 targetIat
    { (s.push64 nextRip) with rip := targetFunc }

  toUops _ := [
    { mnemonic := "CALL.loadTarget", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"call [rel $+6 {formatDisp32 i.disp}]"
  toLean i := s!"call_rip ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "CALL transfers control (RIP) and pushes a return address onto RSP; HardwareHarness has no branch/landing-pad support for control-flow instructions yet (PLAN.md Phase 3) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map CallRipRel.mk

/- REF: intel-sdm#vol=2;instr=CALL;part=description -/
/-- CALL rel32 instruction: direct near relative call. -/
structure CallRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
instance : X86_64Instruction CallRel32 where
  encode i :=
    ByteArray.mk #[0xE8] ++ int32ToLittleEndian i.disp

  step i s :=
    let nextRip := s.rip + 5
    let target := nextRip + signExtend32To64 i.disp
    { (s.push64 nextRip) with rip := target }

  toUops _ := [
    { mnemonic := "CALL.storeAddr", uopClass := .storeAddr, eligiblePorts := [.p2, .p3, .p7, .p8], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.storeData", uopClass := .storeData, eligiblePorts := [.p4, .p9], latencyCycles := 1, reciprocalThroughput := 0.5 },
    { mnemonic := "CALL.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  -- `$+5` is load-bearing, not decorative (found via P4(a)'s registry-derived encoding fuzzer,
  -- docs/X86_ISA_EXPANSION_PREREQUISITES.md, on the `curatedInt32Cases` INT32_MIN witness --
  -- other values could coincidentally still byte-match depending on the call's position in the
  -- generated program, which is exactly why this bug was invisible until a registry-derived,
  -- position-varying generator existed). `step` computes the branch target as `s.rip + 5 +
  -- signExtend32To64 i.disp` -- i.e. `i.disp` IS the already-relative-to-next-instruction rel32
  -- value `encode` writes verbatim. Without a `$`-anchored expression, NASM has no reference
  -- point and treats `formatDisp32 i.disp`'s text as an ABSOLUTE target address, computing its
  -- own rel32 as `target - next_instruction_address` -- which only coincidentally equals
  -- `i.disp` when the call happens to sit at offset 0. `CallRipRel.toNASM` immediately below
  -- already gets this right (`[rel $+6 ...]`); this form was simply missing the analogous `$+5`
  -- anchor for its own 5-byte encoding.
  toNASM i := s!"call $+5 {formatDisp32 i.disp}"
  toLean i := s!"call_rel32 ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "CALL transfers control (RIP) and pushes a return address onto RSP; HardwareHarness has no branch/landing-pad support for control-flow instructions yet (PLAN.md Phase 3) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map CallRel32.mk

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CALL [RIP + disp32] helper. -/
def call_rip (disp : Int32) : AnyX86_64Instruction :=
  ⟨CallRipRel.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CALL rel32 helper. -/
def call_rel32 (disp : Int32) : AnyX86_64Instruction :=
  ⟨CallRel32.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the CALL family: `0xE8` (CALL rel32) and `0xFF /2` with the specific
    `0x15` ModR/M byte (indirect `CALL [RIP + disp32]`). Errors for any other byte pattern. -/
def callTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, _, opcode, opOffset) =>
    if opcode == 0xE8 then
      match readInt32LE bytes opOffset with
      | .error e => .error e
      | .ok disp32 => .ok (call_rel32 disp32, (opOffset + 4) - offset)
    else if opcode == 0xFF then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok modrmByte =>
        if modrmByte == 0x15 then
          match readInt32LE bytes (opOffset + 1) with
          | .error e => .error e
          | .ok disp32 => .ok (call_rip disp32, (opOffset + 5) - offset)
        else
          .error "callTryDecode: unsupported ModR/M for 0xFF CALL"
    else
      .error s!"callTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not CALL"

end Gasm.Targets.X86_64.Instructions

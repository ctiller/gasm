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
import Gasm.Targets.X86_64.MemCostModel

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: intel-sdm#vol=2;instr=CALL;part=description -/
/-- CALL [RIP + disp32] instruction: indirect near call through memory displacement. -/
structure CallRipRel where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `CallRipRel`'s declared memory accesses (TWO: the indirect target load, then the return-
    address push), hoisted to a top-level `def` and shared by both `memAccesses` and `toUops`
    below (via `memUops`) -- see `Mov.lean`'s `movRspDispByteAccesses` doc comment for why.
    `targetIat` is RIP-relative (base := none): `disp` folds in the instruction's own fixed
    6-byte encoded length so evaluating against the pre-step state (which still has the
    *current*, not next, rip) yields the same address `step` computes. -/
@[simp] def callRipRelAccesses (i : CallRipRel) : List MemAccessSpec :=
  [⟨.load, .w64, ⟨none, none, 6 + signExtend32To64 i.disp⟩⟩, ⟨.store, .w64, ⟨some .rsp, none, -8⟩⟩]

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
instance : X86_64Instruction CallRipRel where
  encode i :=
    ByteArray.mk #[0xFF, 0x15] ++ int32ToLittleEndian i.disp

  step i s :=
    let nextRip := s.rip + 6
    let targetIat := nextRip + signExtend32To64 i.disp
    let targetFunc := s.read64 targetIat
    { (s.push64 nextRip) with rip := targetFunc }

  -- The derived memory uops (load the indirect target, then store the return address) precede
  -- the hand-written `.branch` uop, matching the pre-migration literal's order and
  -- `callRipRelAccesses`'s own [load, store] order (`derivedMemUops` preserves declaration
  -- order: memUops(load) ++ memUops(store) = [loadUop, storeAddrUop, storeDataUop]).
  toUops i := derivedMemUops (callRipRelAccesses i) defaultMemCostModel ++ [
    { mnemonic := "CALL.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"call [rel $+6 {formatDisp32 i.disp}]"
  toLean i := s!"call_rip ({i.disp})"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "CALL transfers control (RIP) and pushes a return address onto RSP; HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map CallRipRel.mk
  memAccesses := callRipRelAccesses

/- REF: intel-sdm#vol=2;instr=CALL;part=description -/
/-- CALL rel32 instruction: direct near relative call. -/
structure CallRel32 where
  disp : Int32
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `CallRel32`'s declared memory access, hoisted to a top-level `def` and shared by both
    `memAccesses` and `toUops` below (via `memUops`) -- see `Mov.lean`'s
    `movRspDispByteAccesses` doc comment for why. -/
@[simp] def callRel32Accesses (_ : CallRel32) : List MemAccessSpec :=
  [⟨.store, .w64, ⟨some .rsp, none, -8⟩⟩]

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
instance : X86_64Instruction CallRel32 where
  encode i :=
    ByteArray.mk #[0xE8] ++ int32ToLittleEndian i.disp

  step i s :=
    let nextRip := s.rip + 5
    let target := nextRip + signExtend32To64 i.disp
    { (s.push64 nextRip) with rip := target }

  toUops i := derivedMemUops (callRel32Accesses i) defaultMemCostModel ++ [
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
  validationOracle _ := .nasmEncoding "CALL transfers control (RIP) and pushes a return address onto RSP; HardwareHarness has no branch/landing-pad support for control-flow instructions yet (see docs/X86_ISA_EXPANSION_PREREQUISITES.md P4) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := curatedInt32Cases.map CallRel32.mk
  memAccesses := callRel32Accesses

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CALL [RIP + disp32] helper. -/
def call_rip (disp : Int32) : AnyX86_64Instruction :=
  ⟨CallRipRel.mk disp⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- CALL rel32 helper. -/
def call_rel32 (disp : Int32) : AnyX86_64Instruction :=
  ⟨CallRel32.mk disp⟩

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
/-- A packaged direct near call allocates exactly one return-address slot. -/
theorem call_rel32_step_rsp (disp : Int32) (state : X86_64MachineState) :
    (X86_64Instruction.step (call_rel32 disp) state).rsp = state.rsp - 8 := by
  rfl

/- REF: intel-sdm#vol=2;instr=CALL;part=operation -/
/-- The newly allocated call slot contains the architectural fallthrough address. -/
theorem call_rel32_step_return_slot (disp : Int32) (state : X86_64MachineState) :
    (X86_64Instruction.step (call_rel32 disp) state).read64
      (X86_64Instruction.step (call_rel32 disp) state).rsp = state.rip + 5 := by
  change (state.push64 (state.rip + 5)).pop64.1 = state.rip + 5
  exact (Gasm.Targets.X86_64.push64_pop64_roundtrip state (state.rip + 5)).1

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the CALL family: `0xE8` (CALL rel32) and `0xFF /2` with the specific
    `0x15` ModR/M byte (indirect `CALL [RIP + disp32]`). Errors for any other byte pattern. -/
def callTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (hasRex, _, _, _, _, opcode, opOffset) =>
    if hasRex then
      .error "callTryDecode: noncanonical REX prefix for CALL"
    else if opcode == 0xE8 then
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

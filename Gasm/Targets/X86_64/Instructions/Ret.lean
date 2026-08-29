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

/- REF: intel-sdm#vol=2;instr=RET;part=description -/
/-- RET near instruction: pops return address from stack and transfers control. -/
structure RetOp where
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `RetOp`'s declared memory access, hoisted to a top-level `def` and shared by both
    `memAccesses` and `toUops` below (via `memUops`) -- see `Mov.lean`'s
    `movRspDispByteAccesses` doc comment for why. -/
@[simp] def retOpAccesses (_ : RetOp) : List MemAccessSpec :=
  [⟨.load, .w64, ⟨some .rsp, none, 0⟩⟩]

/- REF: intel-sdm#vol=2;instr=RET;part=operation -/
instance : X86_64Instruction RetOp where
  encode _ := ByteArray.mk #[0xC3]

  step _ s :=
    let (retAddr, s') := s.pop64
    { s' with rip := retAddr }

  -- The derived memory (`.load`, popping the return address) uop precedes the hand-written
  -- `.branch` uop, matching the pre-migration literal's order (`docs/MEMORY_HOOK.md` §5.1: the
  -- hook derives memory-class uops; non-memory uops like `.branch` are not part of `memAccesses`
  -- and stay hand-written here, same as `CallRipRel`/`CallRel32` below).
  toUops i := derivedMemUops (retOpAccesses i) defaultMemCostModel ++ [
    { mnemonic := "RET.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM _ := "ret"
  toLean _ := "ret_op"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "RET pops a return address off RSP and transfers control (RIP); HardwareHarness has no landing-pad support for control-flow instructions yet (PLAN.md Phase 3) -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [RetOp.mk]
  memAccesses := retOpAccesses

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- RET helper. -/
def ret_op : AnyX86_64Instruction :=
  ⟨RetOp.mk⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the RET family: `0xC3` (unconditional near RET). Errors for any other
    byte pattern. -/
def retTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, _, opcode, pos) =>
    if opcode == 0xC3 then .ok (ret_op, pos - offset)
    else .error s!"retTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not RET"

end Gasm.Targets.X86_64.Instructions

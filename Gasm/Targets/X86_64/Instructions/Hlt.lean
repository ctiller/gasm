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

/- REF: intel-sdm#vol=2;instr=HLT;part=description -/
/-- HLT instruction: stops instruction execution and places the processor in a HALT state. -/
structure HltOp where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=HLT;part=operation -/
instance : X86_64Instruction HltOp where
  encode _ := ByteArray.mk #[0xF4]
  step _ s :=
    -- Stops machine execution; flagged as halted to terminate trace/loop evaluators
    { s with rip := s.rip + 1, fault := some .halted }
  toUops _ := [
    { mnemonic := "HLT", uopClass := .intALU, eligiblePorts := [.p0], latencyCycles := 1, reciprocalThroughput := 1.0 }
  ]
  toNASM _ := "hlt"
  toLean _ := "hlt_op"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "HLT halts the CPU; cannot be executed inside the harness's per-vector test loop -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [HltOp.mk]
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- HLT helper. -/
def hlt_op : AnyX86_64Instruction :=
  ⟨HltOp.mk⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the HLT family: `0xF4`. Errors for any other byte pattern. -/
def hltTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, _, opcode, pos) =>
    if opcode == 0xF4 then .ok (hlt_op, pos - offset)
    else .error s!"hltTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not HLT"

end Gasm.Targets.X86_64.Instructions

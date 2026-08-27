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

/- REF: intel-sdm#vol=2;instr=RET;part=description -/
/-- RET near instruction: pops return address from stack and transfers control. -/
structure RetOp where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=RET;part=operation -/
instance : X86_64Instruction RetOp where
  encode _ := ByteArray.mk #[0xC3]

  step _ s :=
    let (retAddr, s') := s.pop64
    { s' with rip := retAddr }

  toUops _ := [
    { mnemonic := "RET.popTarget", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 4, reciprocalThroughput := 0.5 },
    { mnemonic := "RET.branch", uopClass := .branch, eligiblePorts := [.p0, .p6], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM _ := "ret"
  toLean _ := "ret_op"
  canFuzzHardware _ := false
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [RetOp.mk]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- RET helper. -/
def ret_op : AnyX86_64Instruction :=
  ⟨RetOp.mk⟩

end Gasm.Targets.X86_64.Instructions

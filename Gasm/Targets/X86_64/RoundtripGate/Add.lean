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

import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the ADD family, lifted into the open existential wrapper. -/
def addFamilyCases : List AnyX86_64Instruction :=
  ((X86_64Instruction.roundtripCases : List AddR64R64).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR64Imm8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddRspImm8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddRspImm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR64Imm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR32R32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR32Imm8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR32Imm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR16R16).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR16Imm8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR16Imm16).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR8R8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List AddR8Imm8).map fun i => (⟨i⟩ : AnyX86_64Instruction))

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the ADD family: every `roundtripCases` witness decodes back. -/
theorem addFamily_roundtripGate : addFamilyCases.all (decodesOk addTryDecode) = true := by
  set_option maxRecDepth 8000 in decide


/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- In-bucket exclusivity for the ADD family: no two of this family's own byte patterns
    collide ambiguously. A direct corollary of `addFamily_roundtripGate` via
    `RoundtripGate.inBucketExclusiveOf` (see that lemma's docstring for why this is derived
    rather than a fresh `decide` obligation). -/
theorem addFamily_inBucketExclusive :
    ∀ i ∈ addFamilyCases, ∀ j ∈ addFamilyCases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j :=
  inBucketExclusiveOf addFamily_roundtripGate

end Gasm.Targets.X86_64.RoundtripGate

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

import Gasm.Targets.X86_64.Instructions.Out
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the OUT family, lifted into the open existential wrapper. -/
def outFamilyCases : List AnyX86_64Instruction :=
  ((X86_64Instruction.roundtripCases : List OutImm8Al).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List OutDxAl).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List OutImm8Eax).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List OutDxEax).map fun i => (⟨i⟩ : AnyX86_64Instruction))

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the OUT family: every `roundtripCases` witness decodes back. -/
theorem outFamily_roundtripGate : outFamilyCases.all (decodesOk outTryDecode) = true := by decide


/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- In-bucket exclusivity for the OUT family: no two of this family's own byte patterns
    collide ambiguously. A direct corollary of `outFamily_roundtripGate` via
    `RoundtripGate.inBucketExclusiveOf` (see that lemma's docstring for why this is derived
    rather than a fresh `decide` obligation). -/
theorem outFamily_inBucketExclusive :
    ∀ i ∈ outFamilyCases, ∀ j ∈ outFamilyCases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j :=
  inBucketExclusiveOf outFamily_roundtripGate

end Gasm.Targets.X86_64.RoundtripGate

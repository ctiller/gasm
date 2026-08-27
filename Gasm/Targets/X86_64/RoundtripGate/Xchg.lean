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

import Gasm.Targets.X86_64.Instructions.Xchg
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the XCHG family, lifted into the open existential wrapper. -/
def xchgFamilyCases : List AnyX86_64Instruction :=
  (X86_64Instruction.roundtripCases : List XchgR64R64).map fun i => (⟨i⟩ : AnyX86_64Instruction)

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the XCHG family: every `roundtripCases` witness decodes back. -/
theorem xchgFamily_roundtripGate : xchgFamilyCases.all decodesOk = true := by decide

end Gasm.Targets.X86_64.RoundtripGate

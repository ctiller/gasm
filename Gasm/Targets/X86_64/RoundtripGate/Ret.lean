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

import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the RET family, lifted into the open existential wrapper. -/
def retFamilyCases : List AnyX86_64Instruction :=
  (X86_64Instruction.roundtripCases : List RetOp).map fun i => (⟨i⟩ : AnyX86_64Instruction)

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the RET family: every `roundtripCases` witness decodes back. -/
theorem retFamily_roundtripGate : retFamilyCases.all (decodesOk retTryDecode) = true := by decide

private def retDecodesExactlyAs (bytes : ByteArray) (expected : AnyX86_64Instruction) : Bool :=
  match retTryDecode bytes 0 with
  | .ok (decoded, consumed) =>
      consumed == bytes.size &&
        X86_64Instruction.encode decoded == bytes &&
        X86_64Instruction.toLean decoded == X86_64Instruction.toLean expected
  | .error _ => false

private def retDecodeRejects (bytes : ByteArray) : Bool :=
  match retTryDecode bytes 0 with
  | .ok _ => false
  | .error _ => true

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- The selected near return has one canonical byte and consumes exactly that byte. -/
theorem retOp_canonical_reverse_control :
    retDecodesExactlyAs (ByteArray.mk #[0xC3]) ret_op = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- No REX identity is emitted for `RET`; representative REX bytes, doubled/legacy prefixes,
    truncation, the unrepresented C2 form, and a neighboring opcode all fail closed. -/
theorem retOp_hostile_bytes_rejected :
    [ByteArray.mk #[0x40, 0xC3],
     ByteArray.mk #[0x41, 0xC3],
     ByteArray.mk #[0x48, 0xC3],
     ByteArray.mk #[0x4F, 0xC3],
     ByteArray.mk #[0x40, 0x40, 0xC3],
     ByteArray.mk #[0x66, 0xC3],
     ByteArray.mk #[0x40],
     ByteArray.mk #[0xC2, 0x00, 0x00],
     ByteArray.mk #[0xC4]].all retDecodeRejects = true := by
  decide


/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- In-bucket exclusivity for the RET family: no two of this family's own byte patterns
    collide ambiguously. A direct corollary of `retFamily_roundtripGate` via
    `RoundtripGate.inBucketExclusiveOf` (see that lemma's docstring for why this is derived
    rather than a fresh `decide` obligation). -/
theorem retFamily_inBucketExclusive :
    ∀ i ∈ retFamilyCases, ∀ j ∈ retFamilyCases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j :=
  inBucketExclusiveOf retFamily_roundtripGate

end Gasm.Targets.X86_64.RoundtripGate

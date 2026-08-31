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

import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the PUSH family, lifted into the open existential wrapper. -/
def pushFamilyCases : List AnyX86_64Instruction :=
  (X86_64Instruction.roundtripCases : List PushR64).map fun i => (⟨i⟩ : AnyX86_64Instruction)

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the PUSH family: every `roundtripCases` witness decodes back. -/
theorem pushFamily_roundtripGate : pushFamilyCases.all (decodesOk pushTryDecode) = true := by decide

private def pushDecodesExactlyAs (bytes : ByteArray) (expected : AnyX86_64Instruction) : Bool :=
  match pushTryDecode bytes 0 with
  | .ok (decoded, consumed) =>
      consumed == bytes.size &&
        X86_64Instruction.encode decoded == bytes &&
        X86_64Instruction.toLean decoded == X86_64Instruction.toLean expected
  | .error _ => false

private def pushDecodeRejects (bytes : ByteArray) : Bool :=
  match pushTryDecode bytes 0 with
  | .ok _ => false
  | .error _ => true

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- The opcode-register identity uses no prefix for low registers and exactly REX.B for extended
    registers. These endpoint controls also pin full consumption, exact re-encoding, and the
    recovered Lean identity. -/
theorem pushR64_canonical_reverse_controls :
    [(ByteArray.mk #[0x50], push_r64 .rax),
     (ByteArray.mk #[0x57], push_r64 .rdi),
     (ByteArray.mk #[0x41, 0x50], push_r64 .r8),
     (ByteArray.mk #[0x41, 0x57], push_r64 .r15)].all
      (fun pair => pushDecodesExactlyAs pair.1 pair.2) = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- PUSH rejects a redundant REX prefix for low registers and every REX.W/R/X alias for either
    register bank. Doubled/legacy prefixes, truncation, and a neighboring opcode also fail closed. -/
theorem pushR64_hostile_bytes_rejected :
    [ByteArray.mk #[0x40, 0x50],
     ByteArray.mk #[0x48, 0x50],
     ByteArray.mk #[0x44, 0x50],
     ByteArray.mk #[0x42, 0x50],
     ByteArray.mk #[0x49, 0x50],
     ByteArray.mk #[0x45, 0x50],
     ByteArray.mk #[0x43, 0x50],
     ByteArray.mk #[0x4F, 0x57],
     ByteArray.mk #[0x40, 0x41, 0x50],
     ByteArray.mk #[0x66, 0x50],
     ByteArray.mk #[0x40],
     ByteArray.mk #[0x58]].all pushDecodeRejects = true := by
  decide


/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- In-bucket exclusivity for the PUSH family: no two of this family's own byte patterns
    collide ambiguously. A direct corollary of `pushFamily_roundtripGate` via
    `RoundtripGate.inBucketExclusiveOf` (see that lemma's docstring for why this is derived
    rather than a fresh `decide` obligation). -/
theorem pushFamily_inBucketExclusive :
    ∀ i ∈ pushFamilyCases, ∀ j ∈ pushFamilyCases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j :=
  inBucketExclusiveOf pushFamily_roundtripGate

end Gasm.Targets.X86_64.RoundtripGate

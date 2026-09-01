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

import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the CALL family, lifted into the open existential wrapper. -/
def callFamilyCases : List AnyX86_64Instruction :=
  ((X86_64Instruction.roundtripCases : List CallRipRel).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List CallRel32).map fun i => (⟨i⟩ : AnyX86_64Instruction))

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the CALL family, including the `0xE8` direct rel32 form
    (`CallRel32` / `call_rel32`) this change added a decoder branch for. -/
theorem callFamily_roundtripGate : callFamilyCases.all (decodesOk callTryDecode) = true := by decide

private def callDecodesExactlyAs (bytes : ByteArray) (expected : AnyX86_64Instruction) : Bool :=
  match callTryDecode bytes 0 with
  | .ok (decoded, consumed) =>
      consumed == bytes.size &&
        X86_64Instruction.encode decoded == bytes &&
        X86_64Instruction.toLean decoded == X86_64Instruction.toLean expected
  | .error _ => false

private def callDecodeRejects (bytes : ByteArray) : Bool :=
  match callTryDecode bytes 0 with
  | .ok _ => false
  | .error _ => true

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Direct and fixed RIP-relative calls recover their exact selected identities at zero and both
    signed-disp32 endpoints, with full consumption and byte-for-byte re-encoding. -/
theorem call_canonical_reverse_controls :
    [(ByteArray.mk #[0xE8, 0, 0, 0, 0], call_rel32 0),
     (ByteArray.mk #[0xE8, 0xFF, 0xFF, 0xFF, 0x7F], call_rel32 0x7FFFFFFF),
     (ByteArray.mk #[0xE8, 0, 0, 0, 0x80], call_rel32 (-0x80000000)),
     (ByteArray.mk #[0xFF, 0x15, 0, 0, 0, 0], call_rip 0),
     (ByteArray.mk #[0xFF, 0x15, 0xFF, 0xFF, 0xFF, 0x7F], call_rip 0x7FFFFFFF),
     (ByteArray.mk #[0xFF, 0x15, 0, 0, 0, 0x80], call_rip (-0x80000000))].all
      (fun pair => callDecodesExactlyAs pair.1 pair.2) = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- CALL has no selected REX-prefixed identity. The fixed indirect form admits only literal
    `FF 15`; other group extensions, register/address forms, prefixes, and truncations reject. -/
theorem call_hostile_bytes_rejected :
    [ByteArray.mk #[0x40, 0xE8, 0, 0, 0, 0],
     ByteArray.mk #[0x41, 0xE8, 0, 0, 0, 0],
     ByteArray.mk #[0x48, 0xE8, 0, 0, 0, 0],
     ByteArray.mk #[0x4F, 0xE8, 0, 0, 0, 0],
     ByteArray.mk #[0x40, 0x40, 0xE8, 0, 0, 0, 0],
     ByteArray.mk #[0x66, 0xE8, 0, 0, 0, 0],
     ByteArray.mk #[0x40, 0xFF, 0x15, 0, 0, 0, 0],
     ByteArray.mk #[0x41, 0xFF, 0x15, 0, 0, 0, 0],
     ByteArray.mk #[0x48, 0xFF, 0x15, 0, 0, 0, 0],
     ByteArray.mk #[0x4F, 0xFF, 0x15, 0, 0, 0, 0],
     ByteArray.mk #[0xFF, 0x05, 0, 0, 0, 0],
     ByteArray.mk #[0xFF, 0x1D, 0, 0, 0, 0],
     ByteArray.mk #[0xFF, 0xD0],
     ByteArray.mk #[0xFF, 0x14, 0x24],
     ByteArray.mk #[0xFF, 0x55, 0x00],
     ByteArray.mk #[0xE8],
     ByteArray.mk #[0xE8, 0, 0, 0],
     ByteArray.mk #[0xFF],
     ByteArray.mk #[0xFF, 0x15, 0, 0, 0]].all callDecodeRejects = true := by
  decide


/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- In-bucket exclusivity for the CALL family: no two of this family's own byte patterns
    collide ambiguously. A direct corollary of `callFamily_roundtripGate` via
    `RoundtripGate.inBucketExclusiveOf` (see that lemma's docstring for why this is derived
    rather than a fresh `decide` obligation). -/
theorem callFamily_inBucketExclusive :
    ∀ i ∈ callFamilyCases, ∀ j ∈ callFamilyCases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j :=
  inBucketExclusiveOf callFamily_roundtripGate

end Gasm.Targets.X86_64.RoundtripGate

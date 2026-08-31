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

import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.RoundtripGate.Common

namespace Gasm.Targets.X86_64.RoundtripGate

open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Every `roundtripCases` witness for the MOV/MOVZX family, lifted into the open existential
    wrapper. -/
def movFamilyCases : List AnyX86_64Instruction :=
  ((X86_64Instruction.roundtripCases : List MovR32Imm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovR64Imm64).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovR64R64).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovRspDispByte).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovRspDispImm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovRspDispImm64).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovMem8Reg8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovMem32DispReg32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovMem64DispReg64).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovMem64DispImm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovReg64Mem64Disp).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovReg32Mem32Disp).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovReg8Mem8Disp).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovzxR64Mem8).map fun i => (⟨i⟩ : AnyX86_64Instruction))

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the MOV/MOVZX family. This is the regression gate for both
    operand-width dispatch directions: `MovReg32Mem32Disp.roundtripCases` fails if `0x8B`
    without REX.W decodes as the 64-bit `MovReg64Mem64Disp`, while
    `MovMem32DispReg32.roundtripCases` fails if `0x89` without REX.W decodes as the 64-bit
    `MovMem64DispReg64`. `decodesOk` compares `toLean`, so a decoder that preserves the bytes
    while selecting the wrong semantic structure is rejected. Plain `decide` exceeds the
    kernel's default reduction stack depth on this family's largest case list, so this raises
    `maxRecDepth` rather than falling back to `native_decide`. -/
theorem movFamily_roundtripGate : movFamilyCases.all (decodesOk movTryDecode) = true := by
  set_option maxRecDepth 4000 in decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Test-only predicate for the fail-closed side of the MOV decoder contract. -/
private def movDecodeRejects (bytes : ByteArray) : Bool :=
  match movTryDecode bytes 0 with
  | .error _ => true
  | .ok _ => false

private def movDecodesExactlyAs (bytes : ByteArray) (expected : AnyX86_64Instruction) : Bool :=
  match movTryDecode bytes 0 with
  | .error _ => false
  | .ok (decoded, consumed) =>
      consumed == bytes.size &&
      X86_64Instruction.encode decoded == bytes &&
      X86_64Instruction.toLean decoded == X86_64Instruction.toLean expected

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Direct reverse controls for every canonical REX/SIB corner of the exact-disp8 low-byte load.
    In particular, SPL requires a bare REX prefix, while r8b-r15b and r8-r15 bases independently
    select REX.R and REX.B. -/
theorem mov8mem_canonical_reverse_controls :
    [(ByteArray.mk #[0x8A, 0x40, 0x7F], mov_reg8_mem8_disp .al .rax 0x7F),
     (ByteArray.mk #[0x40, 0x8A, 0x60, 0x00], mov_reg8_mem8_disp .spl .rax 0x00),
     (ByteArray.mk #[0x44, 0x8A, 0x78, 0x80], mov_reg8_mem8_disp .r15b .rax 0x80),
     (ByteArray.mk #[0x8A, 0x44, 0x24, 0x00], mov_reg8_mem8_disp .al .rsp 0x00),
     (ByteArray.mk #[0x41, 0x8A, 0x44, 0x24, 0x00], mov_reg8_mem8_disp .al .r12 0x00),
     (ByteArray.mk #[0x8A, 0x45, 0x00], mov_reg8_mem8_disp .al .rbp 0x00),
     (ByteArray.mk #[0x41, 0x8A, 0x45, 0x00], mov_reg8_mem8_disp .al .r13 0x00),
     (ByteArray.mk #[0x45, 0x8A, 0x7C, 0x24, 0x7F],
       mov_reg8_mem8_disp .r15b .r12 0x7F)].all
      (fun pair => movDecodesExactlyAs pair.1 pair.2) = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- The low-byte decoder fails closed on legacy high-byte aliases and every shape outside its
    exact mod01+disp8 identity. -/
theorem mov8mem_hostile_bytes_rejected :
    [ByteArray.mk #[0x8A, 0x60, 0x00],
     ByteArray.mk #[0x8A, 0x68, 0x00],
     ByteArray.mk #[0x8A, 0x70, 0x00],
     ByteArray.mk #[0x8A, 0x78, 0x00],
     ByteArray.mk #[0x8A, 0x00],
     ByteArray.mk #[0x8A, 0x05, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x8A, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x8A, 0x80, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x8A, 0xC0],
     ByteArray.mk #[0x8A, 0x44, 0x00, 0x7F],
     ByteArray.mk #[0x8A, 0x44, 0x64, 0x7F],
     ByteArray.mk #[0x8A, 0x44, 0x20, 0x7F],
     ByteArray.mk #[0x42, 0x8A, 0x44, 0x24, 0x7F],
     ByteArray.mk #[0x48, 0x8A, 0x40, 0x7F],
     ByteArray.mk #[0x40, 0x8A, 0x40, 0x7F],
     ByteArray.mk #[0x40, 0x40, 0x8A, 0x60, 0x00],
     ByteArray.mk #[0x67, 0x8A, 0x40, 0x7F],
     ByteArray.mk #[0x2E, 0x8A, 0x40, 0x7F],
     ByteArray.mk #[0x8A],
     ByteArray.mk #[0x8A, 0x44],
     ByteArray.mk #[0x8A, 0x44, 0x24]].all movDecodeRejects = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Direct reverse controls for every canonical length/identity corner of the exact-disp8 W32
    load. They include no-REX/no-SIB (3 bytes), exactly one optional component (4 bytes), both
    optional components (5 bytes), RSP/R12 SIB identity, RBP/R13 forced zero displacement,
    both displacement endpoints, and destination/base aliasing. -/
theorem mov32mem_canonical_reverse_controls :
    [(ByteArray.mk #[0x8B, 0x40, 0x7F], mov_reg32_mem32_disp .eax .rax 0x7F),
     (ByteArray.mk #[0x44, 0x8B, 0x78, 0x80], mov_reg32_mem32_disp .r15d .rax 0x80),
     (ByteArray.mk #[0x8B, 0x44, 0x24, 0x00], mov_reg32_mem32_disp .eax .rsp 0x00),
     (ByteArray.mk #[0x41, 0x8B, 0x44, 0x24, 0x00], mov_reg32_mem32_disp .eax .r12 0x00),
     (ByteArray.mk #[0x8B, 0x45, 0x00], mov_reg32_mem32_disp .eax .rbp 0x00),
     (ByteArray.mk #[0x41, 0x8B, 0x45, 0x00], mov_reg32_mem32_disp .eax .r13 0x00),
     (ByteArray.mk #[0x8B, 0x40, 0x80], mov_reg32_mem32_disp .eax .rax 0x80),
     (ByteArray.mk #[0x45, 0x8B, 0x7C, 0x24, 0x7F],
       mov_reg32_mem32_disp .r15d .r12 0x7F)].all
      (fun pair => movDecodesExactlyAs pair.1 pair.2) = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- The W32 decoder is deliberately exact-disp8 and fail-closed: mod00/10/11, RIP-relative and
    no-base shapes, indexed or noncanonical SIB, REX.X, redundant/doubled REX, address/segment
    prefixes, and truncations cannot be relabeled as the canonical production family. -/
theorem mov32mem_hostile_bytes_rejected :
    [ByteArray.mk #[0x8B, 0x00],
     ByteArray.mk #[0x8B, 0x05, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x8B, 0x80, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x8B, 0xC0],
     ByteArray.mk #[0x8B, 0x44, 0x00, 0x7F],
     ByteArray.mk #[0x8B, 0x44, 0x64, 0x7F],
     ByteArray.mk #[0x8B, 0x44, 0x20, 0x7F],
     ByteArray.mk #[0x8B, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x42, 0x8B, 0x44, 0x24, 0x7F],
     ByteArray.mk #[0x40, 0x8B, 0x40, 0x7F],
     ByteArray.mk #[0x40, 0x41, 0x8B, 0x40, 0x7F],
     ByteArray.mk #[0x67, 0x8B, 0x40, 0x7F],
     ByteArray.mk #[0x64, 0x8B, 0x40, 0x7F],
     ByteArray.mk #[0x8B, 0x40],
     ByteArray.mk #[0x8B, 0x44, 0x24]].all movDecodeRejects = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- REX.W on the same opcode is not accepted as W32: it remains the distinct valid W64 family. -/
theorem mov8b_rexW_remains_w64 :
    movDecodesExactlyAs (ByteArray.mk #[0x48, 0x8B, 0x40, 0x7F])
      (mov_reg64_mem64_disp .rax .rax 0x7F) = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Tightening the shared 0x8B address parser must also keep the existing W64 family fail-closed:
    indexed/noncanonical SIB, REX.X, RIP-relative, and a noncanonical disp8-zero alias reject. -/
theorem mov8b64_unsupported_addresses_rejected :
    [ByteArray.mk #[0x48, 0x8B, 0x04, 0x00],
     ByteArray.mk #[0x4A, 0x8B, 0x04, 0x24],
     ByteArray.mk #[0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x48, 0x8B, 0x44, 0x00, 0x7F],
     ByteArray.mk #[0x48, 0x8B, 0x40, 0x00]].all movDecodeRejects = true := by
  decide

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Unsupported 0x89 address shapes must not be relabeled as the closed base-plus-disp8 form.
    The vectors cover indexed SIB, REX.X applied to the SIB no-index field, RIP-relative rm=5,
    and indexed mod=1 SIB, at both W32 and W64 operand widths. -/
theorem mov89_unsupported_addresses_rejected :
    [ByteArray.mk #[0x89, 0x04, 0x00],
     ByteArray.mk #[0x42, 0x89, 0x04, 0x24],
     ByteArray.mk #[0x89, 0x05, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x89, 0x44, 0x00, 0x7f],
     ByteArray.mk #[0x48, 0x89, 0x04, 0x00],
     ByteArray.mk #[0x4a, 0x89, 0x04, 0x24],
     ByteArray.mk #[0x48, 0x89, 0x05, 0x00, 0x00, 0x00, 0x00],
     ByteArray.mk #[0x48, 0x89, 0x44, 0x00, 0x7f]].all movDecodeRejects = true := by
  decide


/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- In-bucket exclusivity for the MOV family: no two of this family's own byte patterns
    collide ambiguously. A direct corollary of `movFamily_roundtripGate` via
    `RoundtripGate.inBucketExclusiveOf` (see that lemma's docstring for why this is derived
    rather than a fresh `decide` obligation). -/
theorem movFamily_inBucketExclusive :
    ∀ i ∈ movFamilyCases, ∀ j ∈ movFamilyCases,
      X86_64Instruction.encode i = X86_64Instruction.encode j →
      X86_64Instruction.toLean i = X86_64Instruction.toLean j :=
  inBucketExclusiveOf movFamily_roundtripGate

end Gasm.Targets.X86_64.RoundtripGate

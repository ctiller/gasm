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
  ((X86_64Instruction.roundtripCases : List MovMem64DispReg64).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovMem64DispImm32).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovReg64Mem64Disp).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovzxR64Mem8).map fun i => (⟨i⟩ : AnyX86_64Instruction)) ++
  ((X86_64Instruction.roundtripCases : List MovReg32RspDisp32).map fun i => (⟨i⟩ : AnyX86_64Instruction))

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Exhaustive roundtrip gate for the MOV/MOVZX family — this is the regression gate for the
    0x8B REX.W soundness bug: `MovReg32RspDisp32.roundtripCases` includes representative
    displacements, and `decodesOk`'s `toLean` check fails loudly if `0x8B` ever again decodes a
    32-bit RSP load as the 64-bit `MovReg64Mem64Disp` structure. Plain `decide` exceeds the
    kernel's default reduction stack depth on this family's largest case list, so this raises
    `maxRecDepth` rather than falling back to `native_decide`. -/
theorem movFamily_roundtripGate : movFamilyCases.all decodesOk = true := by
  set_option maxRecDepth 4000 in decide

end Gasm.Targets.X86_64.RoundtripGate

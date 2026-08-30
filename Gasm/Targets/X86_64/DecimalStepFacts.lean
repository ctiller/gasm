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

import Gasm.Targets.X86_64.DecimalSegments

/-!
# Cached instruction facts for the x86-64 decimal schedule

These are the small architectural observations consumed by the decimal pass proof.  Keeping their
instruction-semantic normalization in a stable leaf lets schedule and invariant changes reuse the
compiled facts instead of unfolding `X86_64Instruction.step` again.
-/

namespace Gasm.Targets.X86_64.DecimalStepFacts

open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem divByTenCoreQuotient (state : X86_64MachineState)
    (highZero : state.gprs .rdx = 0) (divisorTen : state.gprs .r10 = 10) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs .rax =
      UInt64.ofNat ((state.gprs .rax).toNat / 10) := by
  simp only [X86_64Instruction.step]
  rw [divisorTen, highZero]
  have bound : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF := by
    have := (state.gprs .rax).toNat_lt
    omega
  have notOverflow : ¬ 0xFFFFFFFFFFFFFFFF < (state.gprs .rax).toNat / 10 :=
    Nat.not_lt_of_ge bound
  simp [notOverflow, X86_64MachineState.setGpr64]

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem divByTenCoreRemainder (state : X86_64MachineState)
    (highZero : state.gprs .rdx = 0) (divisorTen : state.gprs .r10 = 10) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs .rdx =
      UInt64.ofNat ((state.gprs .rax).toNat % 10) := by
  simp only [X86_64Instruction.step]
  rw [divisorTen, highZero]
  have bound : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF := by
    have := (state.gprs .rax).toNat_lt
    omega
  have notOverflow : ¬ 0xFFFFFFFFFFFFFFFF < (state.gprs .rax).toNat / 10 :=
    Nat.not_lt_of_ge bound
  simp [notOverflow, X86_64MachineState.setGpr64]

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem xorEdxCoreZero (state : X86_64MachineState) :
    (X86_64Instruction.step (XorR32R32.mk .edx .edx) state).gprs .rdx = 0 := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64]

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem divCorePreservesGpr (state : X86_64MachineState) (r : Reg64)
    (notRax : r ≠ .rax) (notRdx : r ≠ .rdx) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs r = state.gprs r := by
  simp only [X86_64Instruction.step]
  split
  · rfl
  · split
    · rfl
    · simp [X86_64MachineState.setGpr64, notRax, notRdx]

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem divCorePreservesMemory (state : X86_64MachineState) :
    (X86_64Instruction.step (DivR64.mk .r10) state).memory = state.memory := by
  simp only [X86_64Instruction.step]
  split
  · rfl
  · split <;> rfl

/-- Exact memory projection of the seven-instruction extraction pass.  This theorem is deliberately
compiled in the instruction-fact leaf: consumers rewrite one projection instead of asking the
kernel to normalize the complete nested machine state. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem extractionFinal_memory (backDisp : UInt8) (initial : X86_64MachineState) :
    (extractionFinal backDisp initial).memory =
      X86_64Mem.write .w64 ((extractionStates initial).2.1.rsp - 8)
        ((extractionStates initial).2.1.gprs .rdx + 0x30)
        (extractionStates initial).2.1.memory := by
  rfl

end Gasm.Targets.X86_64.DecimalStepFacts

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

import Gasm.Targets.X86_64.CFGBridge
import Gasm.Targets.X86_64.MacroAssembler

namespace Gasm.Targets.X86_64.MacroAssembler.Condition

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-branch-blocks -/
/-- Reuse one target-owned branch predicate as the core typed-CFG condition. This changes only its
    nominal presentation; the `holds` predicate is definitionally identical. -/
def conditionCode : X86BranchCondition → Gasm.Core.ConditionCode X86_64
  | .equal => ⟨"equal", X86BranchCondition.equal.holds⟩
  | .notEqual => ⟨"not-equal", X86BranchCondition.notEqual.holds⟩
  | .less => ⟨"signed-less", X86BranchCondition.less.holds⟩
  | .lessEqual => ⟨"signed-less-equal", X86BranchCondition.lessEqual.holds⟩
  | .greater => ⟨"signed-greater", X86BranchCondition.greater.holds⟩
  | .greaterEqual => ⟨"signed-greater-equal", X86BranchCondition.greaterEqual.holds⟩
  | .below => ⟨"unsigned-below", X86BranchCondition.below.holds⟩
  | .above => ⟨"unsigned-above", X86BranchCondition.above.holds⟩
  | .aboveOrEqual => ⟨"unsigned-above-equal", X86BranchCondition.aboveOrEqual.holds⟩

@[simp] theorem conditionCode_holds (kind : X86BranchCondition) (state : X86_64MachineState) :
    (conditionCode kind).holds state ↔ kind.holds state := by
  cases kind <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-comparison-condition-macros -/
/-- One exact register comparison with law-bearing equal and unsigned-below flag semantics.

    This is an ordinary local macro segment. It neither selects a branch destination nor proves a
    CFG edge, layout, runtime transition, or artifact fact. -/
def compare (left right : Reg64) : Segment where
  name := s!"cmp {left}, {right}"
  code := [cmp_r64 left right]
  contract := {
    ensures := fun before after =>
      (X86BranchCondition.equal.holds after ↔ before.gprs left = before.gprs right) ∧
      (X86BranchCondition.below.holds after ↔ before.gprs left < before.gprs right)
    clobberedGprs := []
    flags := .unspecified
    memory := .preserved
    rip := .unspecified
  }
  localSound := by
    intro state _
    constructor
    · simp only [X86BranchCondition.holds, runLocalSteps]
      change
        ((({ state with stdinBuffer := ByteArray.empty, incomingRequests := [] }).setFlagsCmp64
            (state.gprs left) (state.gprs right)).zf = true ↔
          state.gprs left = state.gprs right)
      by_cases equal : state.gprs left = state.gprs right
      · rw [X86_64MachineState.setFlagsCmp64_zf_of_eq _ _ _ equal]
        simp [equal]
      · rw [X86_64MachineState.setFlagsCmp64_zf_of_ne _ _ _ equal]
        simp [equal]
    · simp only [X86BranchCondition.holds, runLocalSteps]
      rw [cmp_r64_step_cf left right state]
  preservesGpr := by
    intro state register _
    rfl
  preservesMemory := by
    intro _ state
    rfl
  preservesFlags := by simp
  preservesRip := by simp
  controlFlowFree := by
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact .compare left right

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-comparison-condition-macros -/
theorem compare_equal (left right : Reg64) (state : X86_64MachineState) :
    X86BranchCondition.equal.holds (runLocalSteps (compare left right).code state) ↔
      state.gprs left = state.gprs right :=
  (compare left right).localSound state trivial |>.1

/- REF: docs/MACRO_ASSEMBLER.md#x86-64-comparison-condition-macros -/
theorem compare_below (left right : Reg64) (state : X86_64MachineState) :
    X86BranchCondition.below.holds (runLocalSteps (compare left right).code state) ↔
      state.gprs left < state.gprs right :=
  (compare left right).localSound state trivial |>.2

end Gasm.Targets.X86_64.MacroAssembler.Condition

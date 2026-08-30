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

import Lean

/-!
# Local list execution and frame composition

This module contains only the target-independent algebra shared by local instruction proofs.
Targets still own their instruction semantics, admitted instruction classes, clobber
classifications, contracts, and connections to production execution and emitted artifacts.
The library lifts those owned facts; it never manufactures target evidence.
-/

namespace Gasm.Proof.LocalExecution

universe u v w x

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- Apply concrete step functions in list order. This is only list-fold algebra: it says nothing
    about fetch, faults, fuel, host effects, termination, or artifact identity. -/
@[simp] def runSteps {Instruction : Type u} {State : Type v} (step : Instruction → State → State) :
    List Instruction → State → State
  | [], state => state
  | instruction :: rest, state => runSteps step rest (step instruction state)

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- Executing appended local lists is sequential composition, in the same left-to-right order as
    `runSteps`. -/
theorem runSteps_append {Instruction : Type u} {State : Type v} (step : Instruction → State → State)
    (xs ys : List Instruction) (state : State) :
    runSteps step (xs ++ ys) state = runSteps step ys (runSteps step xs state) := by
  induction xs generalizing state with
  | nil => rfl
  | cons instruction rest ih => simp [runSteps, ih]

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- Lift a target-owned one-step preservation law to a list of local steps. -/
theorem runSteps_preserves {Instruction : Type u} {State : Type v} {Observed : Type w}
    (step : Instruction → State → State) (observe : State → Observed)
    (stepPreserves : ∀ instruction state, observe (step instruction state) = observe state)
    (code : List Instruction) (state : State) :
    observe (runSteps step code state) = observe state := by
  induction code generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      rw [runSteps, ih, stepPreserves]

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- Lift target-owned per-instruction clobber facts to preservation outside the conservative union
    of the list's clobbers. Duplicate and reordered clobber entries do not affect the theorem. -/
theorem runSteps_preservesOutside {Instruction : Type u} {State : Type v} {Key : Type w}
    {Observed : Type x}
    (step : Instruction → State → State) (clobbered : Instruction → List Key)
    (observe : State → Key → Observed)
    (stepPreserves : ∀ instruction state key, key ∉ clobbered instruction →
      observe (step instruction state) key = observe state key)
    (code : List Instruction) (state : State) (key : Key)
    (notClobbered : key ∉ code.flatMap clobbered) :
    observe (runSteps step code state) key = observe state key := by
  induction code generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at notClobbered
      rw [runSteps, ih _ notClobbered.2, stepPreserves _ _ _ notClobbered.1]

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- Compose two preservation facts for an unindexed observation. -/
theorem preserves_comp {State : Type u} {Observed : Type v} (first second : State → State)
    (observe : State → Observed)
    (firstPreserves : ∀ state, observe (first state) = observe state)
    (secondPreserves : ∀ state, observe (second state) = observe state)
    (state : State) :
    observe (second (first state)) = observe state := by
  rw [secondPreserves, firstPreserves]

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- Compose two frame facts. The semantic boundary asks only that the key is outside each
    footprint; it does not expose a clobber-list order or uniqueness requirement. -/
theorem preservesOutside_comp {State : Type u} {Key : Type v} {Observed : Type w}
    (first second : State → State)
    (observe : State → Key → Observed) (firstClobbers secondClobbers : List Key)
    (firstPreserves : ∀ state key, key ∉ firstClobbers →
      observe (first state) key = observe state key)
    (secondPreserves : ∀ state key, key ∉ secondClobbers →
      observe (second state) key = observe state key)
    (state : State) (key : Key)
    (notFirst : key ∉ firstClobbers) (notSecond : key ∉ secondClobbers) :
    observe (second (first state)) key = observe state key := by
  rw [secondPreserves _ _ notSecond, firstPreserves _ _ notFirst]

/- REF: docs/PROOF_TACTICS.md#lift-target-steps-through-small-generic-algebras -/
/-- List-append specialization of `preservesOutside_comp`. Append is only a conservative union
    representation; consumers need no facts about clobber order or uniqueness. -/
theorem preservesOutside_comp_append {State : Type u} {Key : Type v} {Observed : Type w}
    (first second : State → State)
    (observe : State → Key → Observed) (firstClobbers secondClobbers : List Key)
    (firstPreserves : ∀ state key, key ∉ firstClobbers →
      observe (first state) key = observe state key)
    (secondPreserves : ∀ state key, key ∉ secondClobbers →
      observe (second state) key = observe state key)
    (state : State) (key : Key) (notClobbered : key ∉ firstClobbers ++ secondClobbers) :
    observe (second (first state)) key = observe state key := by
  simp only [List.mem_append, not_or] at notClobbered
  exact preservesOutside_comp first second observe firstClobbers secondClobbers
    firstPreserves secondPreserves state key notClobbered.1 notClobbered.2

end Gasm.Proof.LocalExecution

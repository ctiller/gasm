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

import Gasm.Core.Types

/-!
Generic bounded exploration for executable memory models.

The soundness theorem is the mandatory trust direction: every enumerated state is reachable by the
normative transition relation and therefore satisfies its pinned consistency predicate.  This file
does not claim reverse completeness.  A model checker that advertises complete bounded outcomes
must prove that separately for its concrete successor enumerator and finite scope.
-/

namespace Gasm.MemoryModel.FiniteSearch

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- A normative transition relation with a decidable, finite testing presentation supplied later. -/
structure TransitionSystem (State : Type u) where
  initial : State → Prop
  step : State → State → Prop

namespace TransitionSystem

variable {State : Type u}

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Reachability in exactly `fuel` normative transitions. -/
inductive ReachesAt (sys : TransitionSystem State) : Nat → State → Prop where
  | zero {s} : sys.initial s → ReachesAt sys 0 s
  | step {n s t} : ReachesAt sys n s → sys.step s t → ReachesAt sys (n + 1) t

end TransitionSystem

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- A finite presentation whose seed and successor lists are sound for a normative system. -/
structure Enumerator (sys : TransitionSystem State) where
  seeds : List State
  successors : State → List State
  seeds_sound {s} : s ∈ seeds → sys.initial s
  successors_sound {s t} : t ∈ successors s → sys.step s t

namespace Enumerator

variable {State : Type u} {sys : TransitionSystem State}

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- States enumerated after exactly `fuel` transitions. -/
def layer (e : Enumerator sys) : Nat → List State
  | 0 => e.seeds
  | n + 1 => (e.layer n).flatMap e.successors

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- States enumerated at any depth up to and including `fuel`. -/
def search (e : Enumerator sys) (fuel : Nat) : List State :=
  (List.range (fuel + 1)).flatMap e.layer

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Every state in an exact-depth layer has a normative execution of that depth. -/
theorem layer_sound (e : Enumerator sys) {fuel : Nat} {s : State}
    (hmem : s ∈ e.layer fuel) : sys.ReachesAt fuel s := by
  induction fuel generalizing s with
  | zero =>
      exact .zero (e.seeds_sound hmem)
  | succ n ih =>
      simp only [layer, List.mem_flatMap] at hmem
      obtain ⟨prior, hprior, hnext⟩ := hmem
      exact .step (ih hprior) (e.successors_sound hnext)

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Search never invents an execution: membership returns an exact normative path and its bound. -/
theorem search_sound (e : Enumerator sys) {fuel : Nat} {s : State}
    (hmem : s ∈ e.search fuel) : ∃ depth, depth ≤ fuel ∧ sys.ReachesAt depth s := by
  simp only [search, List.mem_flatMap] at hmem
  obtain ⟨depth, hdepth, hs⟩ := hmem
  have hlt : depth < fuel + 1 := List.mem_range.mp hdepth
  exact ⟨depth, Nat.lt_succ_iff.mp hlt, e.layer_sound hs⟩

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- A pinned consistency predicate preserved by every normative transition. -/
structure ConsistencyInvariant (sys : TransitionSystem State) where
  consistent : State → Prop
  initial_consistent {s} : sys.initial s → consistent s
  step_consistent {s t} : consistent s → sys.step s t → consistent t

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Normative reachability implies the pinned consistency predicate. -/
theorem ConsistencyInvariant.of_reachesAt (inv : ConsistencyInvariant sys)
    {fuel : Nat} {s : State} (hreach : sys.ReachesAt fuel s) : inv.consistent s := by
  induction hreach with
  | zero hinit => exact inv.initial_consistent hinit
  | step hreach hstep ih => exact inv.step_consistent ih hstep

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Mandatory enumerator trust direction: every reported execution satisfies pinned consistency. -/
theorem search_consistent (e : Enumerator sys) (inv : ConsistencyInvariant sys)
    {fuel : Nat} {s : State} (hmem : s ∈ e.search fuel) : inv.consistent s := by
  obtain ⟨_, _, hreach⟩ := e.search_sound hmem
  exact inv.of_reachesAt hreach

end Enumerator

end Gasm.MemoryModel.FiniteSearch

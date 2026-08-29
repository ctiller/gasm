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

import Gasm.MemoryModel.FiniteSearch

/-!
Controls for the mandatory finite-search trust direction.

The second control is intentionally incomplete: it enumerates only the initial state even though a
normative successor is reachable. It still satisfies `search_sound`. This demonstrates that the
generic no-invention theorem confers no reverse completeness claim.
-/

namespace Gasm.MemoryModel.FiniteSearch.NegativeControls

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
def successorSystem : TransitionSystem Nat where
  initial s := s = 0
  step s t := t = s + 1

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- A list reporting `2` as an immediate successor of `0` cannot carry the enumerator proof. -/
theorem unsound_successor_rejected (e : Enumerator successorSystem)
    (hbad : 2 ∈ e.successors 0) : False := by
  have hstep := e.successors_sound hbad
  simp [successorSystem] at hstep

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Sound but deliberately incomplete: it explores no successor of the initial state. -/
def incompleteEnumerator : Enumerator successorSystem where
  seeds := [0]
  successors := fun _ => []
  seeds_sound := by
    intro s hs
    simpa [successorSystem] using hs
  successors_sound := by simp

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
theorem incomplete_layer_excludes_one (depth : Nat) :
    1 ∉ incompleteEnumerator.layer depth := by
  cases depth <;> simp [Enumerator.layer, incompleteEnumerator]

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- State `1` is normatively reachable in one step. -/
theorem one_reachable : successorSystem.ReachesAt 1 1 := by
  exact .step (.zero rfl) rfl

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- Yet the incomplete enumerator omits it at every bound. -/
theorem incomplete_search_excludes_one (fuel : Nat) :
    1 ∉ incompleteEnumerator.search fuel := by
  intro hmem
  simp only [Enumerator.search, List.mem_flatMap] at hmem
  obtain ⟨depth, _, hone⟩ := hmem
  exact incomplete_layer_excludes_one depth hone

/- REF: docs/MEMORY_MODEL.md#12-required-proof-package -/
/-- The one-way theorem still applies: every state the incomplete search does report is reachable. -/
theorem incomplete_search_remains_sound {fuel state : Nat}
    (hmem : state ∈ incompleteEnumerator.search fuel) :
    ∃ depth, depth ≤ fuel ∧ successorSystem.ReachesAt depth state :=
  incompleteEnumerator.search_sound hmem

end Gasm.MemoryModel.FiniteSearch.NegativeControls

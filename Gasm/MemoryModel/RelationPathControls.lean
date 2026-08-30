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

import Gasm.MemoryModel.RelationPath

/-!
Positive and negative structural controls for labelled paths.

These private fixtures establish inhabitation and guard the one-way trust boundary. They prove no
target execution admission, projection completeness, observable consequence, or execution authority.
-/

namespace Gasm.MemoryModel.RelationPath.Controls

private inductive FixtureNode where
  | first
  | second
  | third
  deriving DecidableEq

private inductive FixtureLabel where
  | firstStep
  | secondStep
  deriving DecidableEq

private def chainEdge
    (source : FixtureNode) (label : FixtureLabel) (target : FixtureNode) : Prop :=
  (source = .first ∧ label = .firstStep ∧ target = .second) ∨
  (source = .second ∧ label = .secondStep ∧ target = .third)

private def cycleEdge
    (source : FixtureNode) (label : FixtureLabel) (target : FixtureNode) : Prop :=
  (source = .first ∧ label = .firstStep ∧ target = .second) ∨
  (source = .second ∧ label = .secondStep ∧ target = .first)

private def firstEdgeOnly
    (source : FixtureNode) (label : FixtureLabel) (target : FixtureNode) : Prop :=
  source = .first ∧ label = .firstStep ∧ target = .second

private def emptyEdge : FixtureNode → FixtureLabel → FixtureNode → Prop :=
  fun _ _ _ => False

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem exact_two_edge_path :
    LabeledPath chainEdge .first .third [.firstStep, .secondStep] :=
  .cons (middle := .second) (by simp [chainEdge]) (.single (by simp [chainEdge]))

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem two_edge_reachable : StrictReachable chainEdge .first .third :=
  strictReachable_trans (strictReachable_of_edge (show chainEdge .first .firstStep .second by
      simp [chainEdge]))
    (strictReachable_of_edge (show chainEdge .second .secondStep .third by simp [chainEdge]))

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem cycle_is_not_acyclic : ¬ Acyclic cycleEdge := by
  intro acyclic
  exact acyclic .first ⟨[.firstStep, .secondStep],
    .cons (middle := .second) (by simp [cycleEdge]) (.single (by simp [cycleEdge]))⟩

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem empty_is_acyclic : Acyclic emptyEdge := by
  intro node reachable
  obtain ⟨labels, path⟩ := reachable
  cases path with
  | single step => exact step.elim
  | cons step _ => exact step.elim

private theorem no_path_from_second {target : FixtureNode} {labels : List FixtureLabel} :
    ¬ LabeledPath firstEdgeOnly .second target labels := by
  intro path
  cases path with
  | single step => cases step.1
  | cons step _ => cases step.1

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#31-source-relations-and-observable-projection -/
private theorem first_edge_only_is_subrelation {source target : FixtureNode}
    {label : FixtureLabel} (step : firstEdgeOnly source label target) :
    chainEdge source label target :=
  Or.inl step

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#31-source-relations-and-observable-projection -/
private theorem incomplete_subrelation_drops_reachability :
    StrictReachable chainEdge .first .third ∧
      ¬ StrictReachable firstEdgeOnly .first .third := by
  refine ⟨two_edge_reachable, ?_⟩
  intro reachable
  obtain ⟨labels, path⟩ := reachable
  cases path with
  | single step => cases step.2.2
  | cons step rest =>
      apply no_path_from_second
      simpa only [step.2.2] using rest

private def eraseLabel : FixtureLabel → Unit := fun _ => ()

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#31-source-relations-and-observable-projection -/
/-- Counterexample to a general recovery theorem: a many-to-one map can identify distinct source
labels. A particular restricted edge set could recover labels only from additional hypotheses. -/
private theorem noninjective_map_blocks_general_recovery :
    ∃ left right, left ≠ right ∧ eraseLabel left = eraseLabel right := by
  refine ⟨.firstStep, .secondStep, ?_⟩
  constructor
  · intro equal
    cases equal
  · rfl

end Gasm.MemoryModel.RelationPath.Controls

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

/-!
Structural labelled paths for memory-model relations.

This module preserves the exact source-label sequence of every nonempty path. `StrictReachable` is
the transitive closure `edge+`, not reflexive-transitive reachability. Its existential hides the
exact label list, so later observable-edge and trace-fidelity certificates must retain the
`LabeledPath` witness rather than only a `StrictReachable` proposition.

The module supplies no event admission, target consistency, observable projection, consequence, or
execution authority. A later profile must independently select admitted edges and prove both
directions of any claimed trace fidelity; the monotonicity lemmas here provide only their stated
forward implication.
-/

namespace Gasm.MemoryModel.RelationPath

universe u v w

variable {Node : Type u} {Label : Type v} {TargetLabel : Type w}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- A nonempty path whose list records every source edge label in traversal order. -/
inductive LabeledPath (edge : Node → Label → Node → Prop) :
    Node → Node → List Label → Prop where
  | single {source target label} :
      edge source label target → LabeledPath edge source target [label]
  | cons {source middle target label labels} :
      edge source label middle →
      LabeledPath edge middle target labels →
      LabeledPath edge source target (label :: labels)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Induced strict reachability: at least one labelled source edge is required. -/
def StrictReachable (edge : Node → Label → Node → Prop) (source target : Node) : Prop :=
  ∃ labels, LabeledPath edge source target labels

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- No node is reachable from itself by a nonempty labelled path. -/
def Acyclic (edge : Node → Label → Node → Prop) : Prop :=
  ∀ node, ¬ StrictReachable edge node node

namespace LabeledPath

variable {edge : Node → Label → Node → Prop}
variable {source middle target : Node} {labels leftLabels rightLabels : List Label}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
theorem labels_nonempty (path : LabeledPath edge source target labels) : labels ≠ [] := by
  cases path <;> simp

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Concatenation retains the exact left-to-right source-label sequence. -/
theorem append
    (left : LabeledPath edge source middle leftLabels)
    (right : LabeledPath edge middle target rightLabels) :
    LabeledPath edge source target (leftLabels ++ rightLabels) := by
  induction left with
  | single first =>
      simpa using LabeledPath.cons first right
  | cons first rest ih =>
      simpa using LabeledPath.cons first (ih right)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- An explicit edge implication transports a path without adding edges or changing labels. -/
theorem mapEdges {targetEdge : Node → Label → Node → Prop}
    (mapEdge : ∀ {a label b}, edge a label b → targetEdge a label b)
    (path : LabeledPath edge source target labels) :
    LabeledPath targetEdge source target labels := by
  induction path with
  | single step => exact .single (mapEdge step)
  | cons step rest ih => exact .cons (mapEdge step) ih

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Relabelling is sound only from the caller-supplied per-edge refinement. It does not recover the
source label or establish reverse fidelity. -/
theorem mapLabels (rename : Label → TargetLabel)
    {targetEdge : Node → TargetLabel → Node → Prop}
    (mapEdge : ∀ {a label b}, edge a label b → targetEdge a (rename label) b)
    (path : LabeledPath edge source target labels) :
    LabeledPath targetEdge source target (labels.map rename) := by
  induction path with
  | single step => simpa using LabeledPath.single (mapEdge step)
  | cons step rest ih => simpa using LabeledPath.cons (mapEdge step) ih

end LabeledPath

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#31-source-relations-and-observable-projection -/
theorem strictReachable_of_edge {edge : Node → Label → Node → Prop} {source target : Node}
    {label : Label} (step : edge source label target) : StrictReachable edge source target :=
  ⟨[label], .single step⟩

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#31-source-relations-and-observable-projection -/
theorem strictReachable_trans {edge : Node → Label → Node → Prop} {source middle target : Node}
    (left : StrictReachable edge source middle) (right : StrictReachable edge middle target) :
    StrictReachable edge source target := by
  obtain ⟨leftLabels, leftPath⟩ := left
  obtain ⟨rightLabels, rightPath⟩ := right
  exact ⟨leftLabels ++ rightLabels, leftPath.append rightPath⟩

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#31-source-relations-and-observable-projection -/
/-- Reachability is monotone under an explicit source-edge implication. This is not a reverse
completeness or projection-fidelity theorem. -/
theorem strictReachable_mono {edge targetEdge : Node → Label → Node → Prop}
    (mapEdge : ∀ {a label b}, edge a label b → targetEdge a label b)
    {source target : Node} (path : StrictReachable edge source target) :
    StrictReachable targetEdge source target := by
  obtain ⟨labels, witness⟩ := path
  exact ⟨labels, witness.mapEdges mapEdge⟩

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Every subrelation of an acyclic labelled relation is acyclic. -/
theorem acyclic_of_subrelation {edge superEdge : Node → Label → Node → Prop}
    (included : ∀ {a label b}, edge a label b → superEdge a label b)
    (superAcyclic : Acyclic superEdge) : Acyclic edge := by
  intro node cycle
  exact superAcyclic node (strictReachable_mono included cycle)

end Gasm.MemoryModel.RelationPath

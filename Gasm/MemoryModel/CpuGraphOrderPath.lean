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

import Gasm.MemoryModel.CpuGraph
import Gasm.MemoryModel.RelationPath

/-!
Labelled-path consequences of the structural CPU graph orders.

This module selects exactly one existing relation before taking a path: all edges are either CPU
program order, or coherence order at one fixed Normal-memory location. `Unit` is only the label of
that already-selected relation. It carries no causal kind, scope, target relation, or order evidence;
it is not a heterogeneous relation vocabulary, cannot mix coherence locations, and may not enter a
heterogeneous path without a separate tagged refinement witness.

The resulting acyclicity is structural. It supplies no architecture consistency, target event
fidelity, per-agent or total program order, execution admission, observable projection/fidelity,
synchronization consequence, or execution authority. Existential strict reachability cannot replace
the exact `LabeledPath` witness. In particular, no analogous closure is provided for reads-from or
from-read, for which the generic graph declares no transitivity law.
-/

namespace Gasm.MemoryModel.CpuGraph

open RelationPath

namespace Graph

universe u v w x

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- The labelled-path view of the graph's already-selected CPU program-order relation. -/
def poEdge (g : Graph EventId Location Value AtomicObject) : EventId → Unit → EventId → Prop :=
  fun source _ target => g.po source target

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- The labelled-path view of coherence at one fixed Normal-memory location. -/
def coEdgeAt (g : Graph EventId Location Value AtomicObject)
    (loc : Location) : EventId → Unit → EventId → Prop :=
  fun source _ target => g.co source target loc

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- A nonempty program-order path collapses to the graph's transitive program-order relation. -/
theorem WellFormed.po_of_path (h : g.WellFormed) {source target : EventId}
    {labels : List Unit} (path : LabeledPath (poEdge g) source target labels) :
    g.po source target := by
  induction path with
  | single step => exact step
  | cons step _ ih => exact h.po_trans step ih

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Structural program order has no nonempty cycle. -/
theorem WellFormed.po_acyclic (h : g.WellFormed) : Acyclic (poEdge g) := by
  intro event cycle
  obtain ⟨labels, path⟩ := cycle
  exact h.po_irrefl event (h.po_of_path path)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- A nonempty path in one location's coherence order collapses to that location's `co` edge. -/
theorem WellFormed.co_of_path (h : g.WellFormed) {loc : Location}
    {source target : EventId} {labels : List Unit}
    (path : LabeledPath (coEdgeAt g loc) source target labels) :
    g.co source target loc := by
  induction path with
  | single step => exact step
  | cons step _ ih => exact h.co_trans step ih

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Coherence order at any one modeled Normal-memory location has no nonempty cycle. -/
theorem WellFormed.co_acyclic (h : g.WellFormed) (loc : Location) :
    Acyclic (coEdgeAt g loc) := by
  intro event cycle
  obtain ⟨labels, path⟩ := cycle
  exact h.co_irrefl event loc (h.co_of_path path)

end Graph

end Gasm.MemoryModel.CpuGraph

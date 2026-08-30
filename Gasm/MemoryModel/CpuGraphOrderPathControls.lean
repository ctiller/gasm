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

import Gasm.MemoryModel.CpuGraphOrderPath

/-!
Private controls exercising the CPU structural-order path bridge.

The controls construct exact two-edge witnesses from caller-supplied graph edges, check their
collapse, and reject explicit cycles through the exported acyclicity theorems. They add no graph,
target, consistency, or authority surface.
-/

namespace Gasm.MemoryModel.CpuGraph.OrderPathControls

open RelationPath
open Graph

universe u v w x

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem two_po_edges_collapse (h : g.WellFormed) {first middle last : EventId}
    (firstStep : g.po first middle) (secondStep : g.po middle last) : g.po first last := by
  apply h.po_of_path
  exact .cons (label := ()) firstStep (.single (label := ()) secondStep)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem po_two_edge_cycle_rejected (h : g.WellFormed) {first second : EventId}
    (forward : g.po first second) (backward : g.po second first) : False := by
  apply h.po_acyclic first
  exact ⟨[(), ()], .cons forward (.single backward)⟩

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem two_co_edges_collapse (h : g.WellFormed) {loc : Location}
    {first middle last : EventId}
    (firstStep : g.co first middle loc) (secondStep : g.co middle last loc) :
    g.co first last loc := by
  apply h.co_of_path
  exact .cons (label := ()) firstStep (.single (label := ()) secondStep)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem co_two_edge_cycle_rejected (h : g.WellFormed) (loc : Location)
    {first second : EventId}
    (forward : g.co first second loc) (backward : g.co second first loc) : False := by
  apply h.co_acyclic loc first
  exact ⟨[(), ()], .cons forward (.single backward)⟩

end Gasm.MemoryModel.CpuGraph.OrderPathControls

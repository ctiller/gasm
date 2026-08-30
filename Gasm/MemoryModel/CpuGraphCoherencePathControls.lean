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

import Gasm.MemoryModel.CpuGraphCoherencePath

/-!
Private controls for fixed-location coherence-path consequences.

These controls exercise endpoint classification, initial-target rejection, and the private
singleton path supplied by `initial_first`. They add no public semantic or authority surface.
-/

namespace Gasm.MemoryModel.CpuGraph.CoherencePathControls

open RelationPath
open Graph

universe u v w x

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem two_edges_classify_endpoints (h : g.WellFormed) {loc : Location}
    {first middle last : EventId} (firstStep : g.co first middle loc)
    (secondStep : g.co middle last loc) :
    first ∈ g.events ∧ last ∈ g.events ∧ loc ∈ g.locations ∧
      g.writeAt first loc ∧ g.writeAt last loc := by
  apply h.co_path_fragments
  exact .cons (label := ()) firstStep (.single (label := ()) secondStep)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem initial_target_rejected (h : g.WellFormed) {loc : Location}
    {source init : EventId} (hi : g.initialAt init loc) {labels : List Unit}
    (path : LabeledPath (coEdgeAt g loc) source init labels) : False :=
  h.no_co_path_to_initial hi path

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem initial_first_supplies_singleton_path (h : g.WellFormed) {loc : Location}
    {init write : EventId} (hi : g.initialAt init loc) (hw : g.writeAt write loc)
    (hne : init ≠ write) : LabeledPath (coEdgeAt g loc) init write [()] :=
  .single (h.initial_first hi hw hne)

end Gasm.MemoryModel.CpuGraph.CoherencePathControls

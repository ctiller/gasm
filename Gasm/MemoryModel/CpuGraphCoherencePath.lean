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
Structural consequences of exact fixed-location coherence paths.

The location is selected before path construction, so these theorems cannot combine coherence edges
from different fragments. They classify endpoints and reject paths into a structural initial write;
they add no relation union, reads-from/from-read closure, architecture consistency, target fidelity,
execution admission, observable projection, or authority consequence.
-/

namespace Gasm.MemoryModel.CpuGraph

open RelationPath

namespace Graph

universe u v w x

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- A fixed-location coherence path has member write endpoints at that modeled location. -/
theorem WellFormed.co_path_fragments (h : g.WellFormed) {loc : Location}
    {source target : EventId} {labels : List Unit}
    (path : LabeledPath (coEdgeAt g loc) source target labels) :
    source ∈ g.events ∧ target ∈ g.events ∧ loc ∈ g.locations ∧
      g.writeAt source loc ∧ g.writeAt target loc := by
  have hco := h.co_of_path path
  obtain ⟨sourceMem, targetMem, locationMem⟩ := h.co_endpoints hco
  obtain ⟨sourceWrite, targetWrite⟩ := h.co_classes hco
  exact ⟨sourceMem, targetMem, locationMem, sourceWrite, targetWrite⟩

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- No nonempty fixed-location coherence path can target that location's structural initial write. -/
theorem WellFormed.no_co_path_to_initial (h : g.WellFormed) {loc : Location}
    {source init : EventId} {labels : List Unit} (hi : g.initialAt init loc) :
    ¬ LabeledPath (coEdgeAt g loc) source init labels := by
  intro path
  exact h.not_co_to_initial hi (h.co_of_path path)

end Graph

end Gasm.MemoryModel.CpuGraph

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

/-!
Private signature controls for `CpuGraph.WellFormed` helper theorems.

The event and location types deliberately have no `DecidableEq` derivation or local classical
instance. Applying every exported helper over these types ensures that proof implementation
convenience does not become a downstream premise. The controls construct no graph, target
projection, execution, consistency, fidelity, admission, or authority witness.
-/

namespace Gasm.MemoryModel.CpuGraph.PremiseControls

open Graph

private structure EventId where
  predicate : Nat → Prop

private structure Location where
  predicate : Nat → Prop

private abbrev TestGraph := Graph EventId Location Unit Unit

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem unique_rf (g : TestGraph) (h : g.WellFormed)
    {read : EventId} {loc : Location} (hread : g.readAt read loc) :
    ∃ source, g.rf source read loc ∧ ∀ other, g.rf other read loc → other = source :=
  h.existsUnique_rf hread

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem rf_value (g : TestGraph) (h : g.WellFormed)
    {source read : EventId} {loc : Location} (hrf : g.rf source read loc) :
    g.writeValue source loc = g.readValue read loc :=
  h.rf_value hrf

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem no_co_to_initial (g : TestGraph) (h : g.WellFormed)
    {write init : EventId} {loc : Location} (hi : g.initialAt init loc) :
    ¬ g.co write init loc :=
  h.not_co_to_initial hi

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem from_read_witness (g : TestGraph) (h : g.WellFormed)
    {read write : EventId} {loc : Location} (hfr : g.fr read write loc) :
    read ≠ write ∧ ∃ source, g.rf source read loc ∧ g.co source write loc :=
  h.fr_witness hfr

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem atomic_source (g : TestGraph) (h : g.WellFormed)
    {read : EventId} (ha : g.isAtomicRead read) :
    ∃ source atomicUnit,
      g.atomicObject read = some atomicUnit ∧
      g.atomicObject source = some atomicUnit ∧
      g.atomicCompatible source read ∧
      ∀ loc, g.readAt read loc →
        g.rf source read loc ∧ g.writeValue source loc = g.readValue read loc :=
  h.atomic_rf_source ha

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem split_source_rejected (g : TestGraph) (h : g.WellFormed)
    {first second read : EventId} {loc : Location}
    (hfirst : g.rf first read loc) (hsecond : g.rf second read loc) :
    ¬ first ≠ second :=
  h.rejects_split_fragment_source hfirst hsecond

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem self_rf_rejected (g : TestGraph) (h : g.WellFormed)
    (event : EventId) (loc : Location) : ¬ g.rf event event loc :=
  h.rejects_self_rf event loc

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem failed_co_rejected (g : TestGraph) (h : g.WellFormed)
    {failed other : EventId} {loc : Location} (hf : g.isFailedWrite failed) :
    ¬ g.co failed other loc ∧ ¬ g.co other failed loc :=
  h.failed_write_not_in_co hf

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem failed_rf_rejected (g : TestGraph) (h : g.WellFormed)
    {failed read : EventId} {loc : Location} (hf : g.isFailedWrite failed) :
    ¬ g.rf failed read loc :=
  h.failed_write_not_rf_source hf

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem successful_rmw_is_adjacent (g : TestGraph) (h : g.WellFormed)
    {source rmw : EventId} {loc : Location}
    (hrmw : g.isAtomicRmw rmw) (hsuccess : ¬ g.isFailedWrite rmw)
    (hrf : g.rf source rmw loc) :
    g.co source rmw loc ∧
      ¬ ∃ middle, g.co source middle loc ∧ g.co middle rmw loc :=
  h.successful_rmw_predecessor hrmw hsuccess hrf

end Gasm.MemoryModel.CpuGraph.PremiseControls

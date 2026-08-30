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
Structural graph laws for the first CPU Normal-memory projection.

This is not the heterogeneous global event envelope. Platform/device events and relations are
owned by their target profiles; they need not acquire CPU `rf`/`co`/`fr` edges. A target projects
only its admitted CPU Normal-memory fragments into this graph, then separately proves its
architecture consistency predicate.

Two projection obligations intentionally remain outside `WellFormed`. Matching `AtomicObject`
values do not prove access class, width, alignment, footprint, or single-copy atomicity; the target
event projection and instruction-fidelity theorem must establish those facts. Likewise, this slice
checks `po` endpoints, irreflexivity, and transitivity but does not yet establish per-thread scoping
or totality. Those laws require the target's event-key/thread projection and cannot be claimed from
`WellFormed` alone.

An initial event associated with an atomic object initializes only that exact, fixed v1 object;
targets partition structural initial events when distinct atomic objects are present. Initial writes
are not themselves atomic operations. `atomicCompatible` is target-supplied evidence covering the
source class (including the initial-source case), object generation/liveness, footprint, width,
alignment, and Normal-memory attributes that raw `AtomicObject` tag equality cannot establish.
-/

namespace Gasm.MemoryModel.CpuGraph

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A finite, fragment-granular CPU Normal-memory execution graph.

`Location` is the chosen aligned/non-overlapping v1 coherence fragment (normally a byte). Keeping
it abstract lets a later checked range projection retain the same structural laws. Event identity
is stable and generative only within one execution; no global allocation order is assumed. -/
structure Graph (EventId : Type u) (Location : Type v) (Value : Type w)
    (AtomicObject : Type x) where
  events : List EventId
  locations : List Location
  readAt : EventId → Location → Prop
  writeAt : EventId → Location → Prop
  initialAt : EventId → Location → Prop
  isAtomicRead : EventId → Prop
  isAtomicRmw : EventId → Prop
  isFailedWrite : EventId → Prop
  atomicObject : EventId → Option AtomicObject
  atomicCompatible : EventId → EventId → Prop
  readValue : EventId → Location → Option Value
  writeValue : EventId → Location → Option Value
  po : EventId → EventId → Prop
  rf : EventId → EventId → Location → Prop
  co : EventId → EventId → Location → Prop

namespace Graph

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Normal-memory from-read is derived, never independently selected graph data. -/
def fr (g : Graph EventId Location Value AtomicObject)
    (read laterWrite : EventId) (loc : Location) : Prop :=
  read ≠ laterWrite ∧ ∃ source, g.rf source read loc ∧ g.co source laterWrite loc

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Structural validity, independent of x86 TSO or future Arm consistency.

Ordinary reads have one source per fragment and may assemble fragments from different writes.
Approved single-copy-atomic reads strengthen this to one same-object source event for every fragment
of the observation. The target projection must separately prove that the object and events have
compatible access classes, widths, alignment, footprints, and single-copy atomicity. -/
structure WellFormed (g : Graph EventId Location Value AtomicObject) : Prop where
  events_nodup : g.events.Nodup
  locations_nodup : g.locations.Nodup
  read_fragment_mem {r loc} : g.readAt r loc → r ∈ g.events ∧ loc ∈ g.locations
  write_fragment_mem {w loc} : g.writeAt w loc → w ∈ g.events ∧ loc ∈ g.locations
  initial_fragment_mem {init loc} : g.initialAt init loc → init ∈ g.events ∧ loc ∈ g.locations
  atomic_read_mem {r} : g.isAtomicRead r → r ∈ g.events
  atomic_read_nonempty {r} : g.isAtomicRead r → ∃ loc, g.readAt r loc
  atomic_rmw_is_atomic_read {e} : g.isAtomicRmw e → g.isAtomicRead e
  failed_write_mem {w} : g.isFailedWrite w → w ∈ g.events
  atomic_object_mem {e unit} : g.atomicObject e = some unit → e ∈ g.events
  initial_is_write {init loc} : g.initialAt init loc → g.writeAt init loc
  read_has_value {r loc} : g.readAt r loc → ∃ value, g.readValue r loc = some value
  write_has_value {w loc} : g.writeAt w loc → ∃ value, g.writeValue w loc = some value
  read_value_has_fragment {r loc value} : g.readValue r loc = some value → g.readAt r loc
  write_value_has_fragment {w loc value} : g.writeValue w loc = some value → g.writeAt w loc
  failed_write_has_no_fragment {w} : g.isFailedWrite w → ∀ loc, ¬ g.writeAt w loc
  po_endpoints {a b} : g.po a b → a ∈ g.events ∧ b ∈ g.events
  po_irrefl (a) : ¬ g.po a a
  po_trans {a b c} : g.po a b → g.po b c → g.po a c
  rf_endpoints {w r loc} : g.rf w r loc → w ∈ g.events ∧ r ∈ g.events ∧ loc ∈ g.locations
  rf_classes {w r loc} : g.rf w r loc → g.writeAt w loc ∧ g.readAt r loc
  rf_value_agreement {w r loc} : g.rf w r loc → g.writeValue w loc = g.readValue r loc
  rf_irrefl (e) (loc) : ¬ g.rf e e loc
  rf_total {r loc} : g.readAt r loc → ∃ w, g.rf w r loc
  rf_functional {w₁ w₂ r loc} : g.rf w₁ r loc → g.rf w₂ r loc → w₁ = w₂
  co_endpoints {a b loc} : g.co a b loc → a ∈ g.events ∧ b ∈ g.events ∧ loc ∈ g.locations
  co_classes {a b loc} : g.co a b loc → g.writeAt a loc ∧ g.writeAt b loc
  co_irrefl (a) (loc) : ¬ g.co a a loc
  co_trans {a b c loc} : g.co a b loc → g.co b c loc → g.co a c loc
  co_total {a b loc} :
    g.writeAt a loc → g.writeAt b loc → a ≠ b → g.co a b loc ∨ g.co b a loc
  initial_exists {loc} : loc ∈ g.locations → ∃ init, g.initialAt init loc
  initial_unique {a b loc} : g.initialAt a loc → g.initialAt b loc → a = b
  initial_first {init w loc} :
    g.initialAt init loc → g.writeAt w loc → init ≠ w → g.co init w loc
  atomic_co_uniform {a b unit loc₁ loc₂} :
    g.atomicObject a = some unit →
    g.atomicObject b = some unit →
    g.writeAt a loc₁ → g.writeAt b loc₁ →
    g.writeAt a loc₂ → g.writeAt b loc₂ →
    (g.co a b loc₁ ↔ g.co a b loc₂)
  atomic_read_single_source {r} :
    g.isAtomicRead r →
      ∃ source unit,
        g.atomicObject r = some unit ∧
        g.atomicObject source = some unit ∧
        g.atomicCompatible source r ∧
        ∀ loc, g.readAt r loc → g.rf source r loc
  successful_rmw_same_footprint {e} :
    g.isAtomicRmw e → ¬ g.isFailedWrite e → ∀ loc, g.readAt e loc ↔ g.writeAt e loc
  successful_rmw_adjacent {source rmw loc} :
    g.isAtomicRmw rmw → ¬ g.isFailedWrite rmw → g.rf source rmw loc →
      g.co source rmw loc ∧
      ¬ ∃ middle, g.co source middle loc ∧ g.co middle rmw loc

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A read fragment has exactly one reads-from source. -/
theorem WellFormed.existsUnique_rf (h : g.WellFormed) {r : EventId} {loc : Location}
    (hr : g.readAt r loc) : ∃ w, g.rf w r loc ∧ ∀ y, g.rf y r loc → y = w := by
  obtain ⟨w, hw⟩ := h.rf_total hr
  exact ⟨w, hw, fun y hy => h.rf_functional hy hw⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Reads-from preserves the exact fragment value. -/
theorem WellFormed.rf_value (h : g.WellFormed) {w r : EventId} {loc : Location}
    (hrf : g.rf w r loc) : g.writeValue w loc = g.readValue r loc :=
  h.rf_value_agreement hrf

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- No coherence edge may target the structural initial write for its location. -/
theorem WellFormed.not_co_to_initial (h : g.WellFormed) {w init : EventId} {loc : Location}
    (hi : g.initialAt init loc) : ¬ g.co w init loc := by
  intro hco
  have hw := (h.co_classes hco).1
  have hne : init ≠ w := by
    intro heq
    subst w
    exact h.co_irrefl init loc hco
  have hfirst := h.initial_first hi hw hne
  exact h.co_irrefl w loc (h.co_trans hco hfirst)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Expands a derived `fr` edge to its reads-from and coherence witnesses. -/
theorem WellFormed.fr_witness (_h : g.WellFormed) {r w : EventId} {loc : Location}
    (hfr : g.fr r w loc) : r ≠ w ∧ ∃ source, g.rf source r loc ∧ g.co source w loc :=
  hfr

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Every fragment of an approved single-copy-atomic observation comes from the same source event. -/
theorem WellFormed.atomic_rf_source (h : g.WellFormed) {r : EventId}
    (ha : g.isAtomicRead r) :
    ∃ source unit,
      g.atomicObject r = some unit ∧
      g.atomicObject source = some unit ∧
      g.atomicCompatible source r ∧
      ∀ loc, g.readAt r loc →
        g.rf source r loc ∧ g.writeValue source loc = g.readValue r loc := by
  obtain ⟨source, unit, hrUnit, hsUnit, hcompat, hsource⟩ := h.atomic_read_single_source ha
  exact ⟨source, unit, hrUnit, hsUnit, hcompat, fun loc hread =>
    ⟨hsource loc hread, h.rf_value_agreement (hsource loc hread)⟩⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Negative control: two distinct sources for one read fragment make a graph malformed. -/
theorem WellFormed.rejects_split_fragment_source (h : g.WellFormed)
    {w₁ w₂ r : EventId} {loc : Location} (h₁ : g.rf w₁ r loc) (h₂ : g.rf w₂ r loc) :
    ¬ w₁ ≠ w₂ := by
  intro hne
  exact hne (h.rf_functional h₁ h₂)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Negative control: a combined read/write event cannot source its own read fragment. -/
theorem WellFormed.rejects_self_rf (h : g.WellFormed) (e : EventId) (loc : Location) :
    ¬ g.rf e e loc :=
  h.rf_irrefl e loc

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Negative control: a failed RMW/exclusive write cannot appear in modification order. -/
theorem WellFormed.failed_write_not_in_co (h : g.WellFormed) {failed other : EventId}
    {loc : Location} (hf : g.isFailedWrite failed) :
    ¬ g.co failed other loc ∧ ¬ g.co other failed loc := by
  constructor <;> intro hco
  · exact h.failed_write_has_no_fragment hf loc (h.co_classes hco).1
  · exact h.failed_write_has_no_fragment hf loc (h.co_classes hco).2

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Negative control: a failed RMW/exclusive write cannot source any read fragment. -/
theorem WellFormed.failed_write_not_rf_source (h : g.WellFormed) {failed read : EventId}
    {loc : Location} (hf : g.isFailedWrite failed) : ¬ g.rf failed read loc := by
  intro hrf
  exact h.failed_write_has_no_fragment hf loc (h.rf_classes hrf).1

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A successful combined RMW reads its immediate coherence predecessor on every read fragment. -/
theorem WellFormed.successful_rmw_predecessor (h : g.WellFormed)
    {source rmw : EventId} {loc : Location}
    (hrmw : g.isAtomicRmw rmw) (hsuccess : ¬ g.isFailedWrite rmw)
    (hrf : g.rf source rmw loc) :
    g.co source rmw loc ∧ ¬ ∃ middle, g.co source middle loc ∧ g.co middle rmw loc :=
  h.successful_rmw_adjacent hrmw hsuccess hrf

end Graph

end Gasm.MemoryModel.CpuGraph

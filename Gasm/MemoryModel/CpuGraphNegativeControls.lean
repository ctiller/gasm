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

import Gasm.MemoryModel.ProgramOrder

/-!
Negative controls for the generic CPU Normal-memory graph.

Each theorem starts from a representative malformed shape and proves that the existing structural
certificate rejects it. These are proof-level controls, not architecture consistency rules.
-/

namespace Gasm.MemoryModel.CpuGraph.NegativeControls

open Graph

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {Agent : Type y}
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem missing_rf_source {r : EventId} {loc : Location}
    (hread : g.readAt r loc) (hmissing : ∀ w, ¬ g.rf w r loc) : ¬ g.WellFormed := by
  intro hwf
  obtain ⟨w, hrf⟩ := hwf.rf_total hread
  exact hmissing w hrf

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem two_rf_sources {w₁ w₂ r : EventId} {loc : Location}
    (hne : w₁ ≠ w₂) (h₁ : g.rf w₁ r loc) (h₂ : g.rf w₂ r loc) : ¬ g.WellFormed := by
  intro hwf
  exact hne (hwf.rf_functional h₁ h₂)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem rf_self_edge (e : EventId) (loc : Location) (hself : g.rf e e loc) :
    ¬ g.WellFormed := by
  intro hwf
  exact hwf.rf_irrefl e loc hself

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem rf_class_mismatch {w r : EventId} {loc : Location}
    (hrf : g.rf w r loc) (hbad : ¬ (g.writeAt w loc ∧ g.readAt r loc)) : ¬ g.WellFormed := by
  intro hwf
  exact hbad (hwf.rf_classes hrf)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem rf_value_mismatch {w r : EventId} {loc : Location}
    (hrf : g.rf w r loc) (hbad : g.writeValue w loc ≠ g.readValue r loc) : ¬ g.WellFormed := by
  intro hwf
  exact hbad (hwf.rf_value_agreement hrf)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem co_cycle {a b : EventId} {loc : Location}
    (hab : g.co a b loc) (hba : g.co b a loc) : ¬ g.WellFormed := by
  intro hwf
  exact hwf.co_irrefl a loc (hwf.co_trans hab hba)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem co_incomparable {a b : EventId} {loc : Location}
    (ha : g.writeAt a loc) (hb : g.writeAt b loc) (hne : a ≠ b)
    (hab : ¬ g.co a b loc) (hba : ¬ g.co b a loc) : ¬ g.WellFormed := by
  intro hwf
  rcases hwf.co_total ha hb hne with h | h
  · exact hab h
  · exact hba h

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem failed_write_co_endpoint {failed other : EventId} {loc : Location}
    (hf : g.isFailedWrite failed) (hco : g.co failed other loc ∨ g.co other failed loc) :
    ¬ g.WellFormed := by
  intro hwf
  rcases hco with h | h
  · exact hwf.failed_write_has_no_fragment hf loc (hwf.co_classes h).1
  · exact hwf.failed_write_has_no_fragment hf loc (hwf.co_classes h).2

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem missing_initial {loc : Location}
    (hmem : loc ∈ g.locations) (hmissing : ∀ init, ¬ g.initialAt init loc) : ¬ g.WellFormed := by
  intro hwf
  obtain ⟨init, hi⟩ := hwf.initial_exists hmem
  exact hmissing init hi

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem duplicate_initial {a b : EventId} {loc : Location}
    (hne : a ≠ b) (ha : g.initialAt a loc) (hb : g.initialAt b loc) : ¬ g.WellFormed := by
  intro hwf
  exact hne (hwf.initial_unique ha hb)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem nonminimal_initial {init w : EventId} {loc : Location}
    (hi : g.initialAt init loc) (hw : g.writeAt w loc) (hne : init ≠ w)
    (hnotFirst : ¬ g.co init w loc) : ¬ g.WellFormed := by
  intro hwf
  exact hnotFirst (hwf.initial_first hi hw hne)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem identity_fr_forbidden (e : EventId) (loc : Location) : ¬ g.fr e e loc := by
  intro hfr
  exact hfr.1 rfl

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem atomic_split_source {r w₁ w₂ : EventId} {loc₁ loc₂ : Location}
    (ha : g.isAtomicRead r) (hne : w₁ ≠ w₂)
    (hread₁ : g.readAt r loc₁) (hread₂ : g.readAt r loc₂)
    (hrf₁ : g.rf w₁ r loc₁) (hrf₂ : g.rf w₂ r loc₂) : ¬ g.WellFormed := by
  intro hwf
  obtain ⟨source, _, _, _, _, hsource⟩ := hwf.atomic_read_single_source ha
  have hs₁ : source = w₁ := hwf.rf_functional (hsource loc₁ hread₁) hrf₁
  have hs₂ : source = w₂ := hwf.rf_functional (hsource loc₂ hread₂) hrf₂
  exact hne (hs₁.symm.trans hs₂)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem atomic_missing_compatibility {r : EventId}
    (ha : g.isAtomicRead r) (hbad : ∀ source, ¬ g.atomicCompatible source r) :
    ¬ g.WellFormed := by
  intro hwf
  obtain ⟨source, _, _, _, hcompat, _⟩ := hwf.atomic_read_single_source ha
  exact hbad source hcompat

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem atomic_nonuniform_co {a b : EventId} {unit : AtomicObject} {loc₁ loc₂ : Location}
    (haUnit : g.atomicObject a = some unit) (hbUnit : g.atomicObject b = some unit)
    (ha₁ : g.writeAt a loc₁) (hb₁ : g.writeAt b loc₁)
    (ha₂ : g.writeAt a loc₂) (hb₂ : g.writeAt b loc₂)
    (hco₁ : g.co a b loc₁) (hco₂ : ¬ g.co a b loc₂) : ¬ g.WellFormed := by
  intro hwf
  exact hco₂ ((hwf.atomic_co_uniform haUnit hbUnit ha₁ hb₁ ha₂ hb₂).mp hco₁)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem successful_rmw_without_adjacency {source rmw : EventId} {loc : Location}
    (hrmw : g.isAtomicRmw rmw) (hsuccess : ¬ g.isFailedWrite rmw)
    (hrf : g.rf source rmw loc)
    (hbad : ¬ g.co source rmw loc ∨ ∃ middle, g.co source middle loc ∧ g.co middle rmw loc) :
    ¬ g.WellFormed := by
  intro hwf
  obtain ⟨hco, hadjacent⟩ := hwf.successful_rmw_adjacent hrmw hsuccess hrf
  rcases hbad with h | h
  · exact h hco
  · exact hadjacent h

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem po_cross_agent (p : g.ProgramOrderProjection Agent) {a b : EventId}
    {agent₁ agent₂ : Agent} {sa sb : Nat}
    (hne : agent₁ ≠ agent₂)
    (ha : p.programPoint a = some (agent₁, sa))
    (hb : p.programPoint b = some (agent₂, sb)) : ¬ g.po a b := by
  intro hpo
  obtain ⟨agent, _, _, ha', hb', _⟩ := p.po_iff.mp hpo
  have h₁ : agent₁ = agent := congrArg (fun pair => pair.1) (Option.some.inj (ha.symm.trans ha'))
  have h₂ : agent₂ = agent := congrArg (fun pair => pair.1) (Option.some.inj (hb.symm.trans hb'))
  exact hne (h₁.trans h₂.symm)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem po_nonpoint_edge (p : g.ProgramOrderProjection Agent) {a b : EventId}
    (ha : p.programPoint a = none) : ¬ g.po a b :=
  p.no_po_from_none ha b

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem po_initial_edge (p : g.ProgramOrderProjection Agent) {init other : EventId} {loc : Location}
    (hi : g.initialAt init loc) : ¬ g.po init other ∧ ¬ g.po other init :=
  ⟨(p.initial_not_in_po hi).1 other, (p.initial_not_in_po hi).2 other⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem po_duplicate_sequence (p : g.ProgramOrderProjection Agent) {a b : EventId}
    {agent : Agent} {sequence : Nat} (hne : a ≠ b)
    (ha : p.programPoint a = some (agent, sequence))
    (hb : p.programPoint b = some (agent, sequence)) : False :=
  hne (p.sequence_unique ha hb)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
theorem po_missing_same_agent_order (p : g.ProgramOrderProjection Agent) {a b : EventId}
    {agent : Agent} {sa sb : Nat}
    (ha : p.programPoint a = some (agent, sa))
    (hb : p.programPoint b = some (agent, sb))
    (hlt : sa < sb) (hmissing : ¬ g.po a b) : False :=
  hmissing (p.po_iff.mpr ⟨agent, sa, sb, ha, hb, hlt⟩)

/-!
Compile-time-only sentinels for the absence of an ambient equality-decision premise. They exercise
the graph and program-order control families over hostile identities; they do not test the controls'
semantics or construct a graph, projection, execution, fidelity, admission, or authority witness.
-/

private structure HostileEventId where
  predicate : Nat → Prop

private structure HostileLocation where
  predicate : Nat → Prop

private structure HostileAgent where
  predicate : Nat → Prop

private abbrev HostileGraph := Graph HostileEventId HostileLocation Unit Unit

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem graph_control_has_no_equality_premise (g : HostileGraph)
    {read : HostileEventId} {loc : HostileLocation}
    (hread : g.readAt read loc) (hmissing : ∀ source, ¬ g.rf source read loc) :
    ¬ g.WellFormed :=
  missing_rf_source hread hmissing

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem program_order_control_has_no_equality_premise (g : HostileGraph)
    (p : g.ProgramOrderProjection HostileAgent) {a b : HostileEventId}
    {firstAgent secondAgent : HostileAgent} {firstSeq secondSeq : Nat}
    (hne : firstAgent ≠ secondAgent)
    (ha : p.programPoint a = some (firstAgent, firstSeq))
    (hb : p.programPoint b = some (secondAgent, secondSeq)) : ¬ g.po a b :=
  po_cross_agent p hne ha hb

end Gasm.MemoryModel.CpuGraph.NegativeControls

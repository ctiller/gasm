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
Target-projection certificate for CPU program order.

This certificate is external to `CpuGraph.Graph`: a target selects which graph events are CPU
program events and assigns them an agent-local sequence. Structural initial events and events with
no CPU program point acquire no `po` edges. Different agents remain unordered by CPU `po`; platform
and device order belongs to their native relations.

This module certifies generic graph structure only. It grants neither target execution fidelity nor
execution/admission authority. Concrete M2-X/M2-A admission must additionally prove that every
admitted instruction-origin CPU event has exactly its `EventKey`-derived agent and local sequence,
while structural initial and non-CPU events have no program point. It must also refine every
consumed `atomicCompatible source read` witness to the concrete target descriptor facts: approved
source access class or the exact structural-initial case, object generation and liveness, equal
footprint, width and alignment, Normal-memory attributes, and target single-copy atomicity. Those
target metadata and fidelity theorems deliberately remain outside this generic graph layer.
-/

namespace Gasm.MemoryModel.CpuGraph

namespace Graph

variable {EventId : Type u} {Location : Type v} {Value : Type w} {AtomicObject : Type x}
variable {Agent : Type y}
variable [DecidableEq EventId]
variable {g : Graph EventId Location Value AtomicObject}

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Evidence that `g.po` is exactly strict order on target-projected CPU program points.

`Nat` is the v1 `LocalSequence`: it gives an economical strict total order without imposing a
global allocation order on event identities or agents. -/
structure ProgramOrderProjection (g : Graph EventId Location Value AtomicObject) (Agent : Type y)
    where
  programPoint : EventId → Option (Agent × Nat)
  point_mem {e agent sequence} : programPoint e = some (agent, sequence) → e ∈ g.events
  sequence_unique {a b agent sequence} :
    programPoint a = some (agent, sequence) →
    programPoint b = some (agent, sequence) →
    a = b
  initial_no_point {init loc} : g.initialAt init loc → programPoint init = none
  po_iff {a b} :
    g.po a b ↔
      ∃ agent sa sb,
        programPoint a = some (agent, sa) ∧
        programPoint b = some (agent, sb) ∧
        sa < sb

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Reusable fragment/program-order structure, without target fidelity or admission authority.

Keeping the exact program-order projection beside, rather than inside, `Graph` lets targets select
their own CPU agent identity while making it impossible to cite fragment/coherence well-formedness
alone as proof of per-agent program order. M2-X/M2-A execution admission additionally requires the
module-level target-origin, descriptor-fidelity, and consistency certificates described above. -/
structure StructuralCpuProjection
    (g : Graph EventId Location Value AtomicObject) (Agent : Type y) where
  fragments : g.WellFormed
  programOrder : ProgramOrderProjection g Agent

namespace ProgramOrderProjection

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A CPU program-order edge has graph-member endpoints. -/
theorem po_endpoints (p : ProgramOrderProjection g Agent) {a b : EventId}
    (hpo : g.po a b) : a ∈ g.events ∧ b ∈ g.events := by
  obtain ⟨agent, sa, sb, ha, hb, _⟩ := p.po_iff.mp hpo
  exact ⟨p.point_mem ha, p.point_mem hb⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Program order relates events on one CPU execution agent only. -/
theorem po_same_agent (p : ProgramOrderProjection g Agent) {a b : EventId}
    (hpo : g.po a b) :
    ∃ agent sa sb,
      p.programPoint a = some (agent, sa) ∧
      p.programPoint b = some (agent, sb) := by
  obtain ⟨agent, sa, sb, ha, hb, _⟩ := p.po_iff.mp hpo
  exact ⟨agent, sa, sb, ha, hb⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- An event without a CPU program point has no outgoing CPU program-order edge. -/
theorem no_po_from_none (p : ProgramOrderProjection g Agent) {a : EventId}
    (ha : p.programPoint a = none) : ∀ b, ¬ g.po a b := by
  intro b hpo
  obtain ⟨agent, sa, _, hpoint, _, _⟩ := p.po_iff.mp hpo
  simp [ha] at hpoint

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- An event without a CPU program point has no incoming CPU program-order edge. -/
theorem no_po_to_none (p : ProgramOrderProjection g Agent) {b : EventId}
    (hb : p.programPoint b = none) : ∀ a, ¬ g.po a b := by
  intro a hpo
  obtain ⟨agent, _, sb, _, hpoint, _⟩ := p.po_iff.mp hpo
  simp [hb] at hpoint

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- CPU program order is irreflexive. -/
theorem po_irrefl (p : ProgramOrderProjection g Agent) (a : EventId) : ¬ g.po a a := by
  intro hpo
  obtain ⟨agent, sa, sb, ha, hb, hlt⟩ := p.po_iff.mp hpo
  have hp : (agent, sa) = (agent, sb) := Option.some.inj (ha.symm.trans hb)
  have hs : sa = sb := congrArg Prod.snd hp
  subst sb
  exact Nat.lt_irrefl sa hlt

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- CPU program order is transitive. -/
theorem po_trans (p : ProgramOrderProjection g Agent) {a b c : EventId}
    (hab : g.po a b) (hbc : g.po b c) : g.po a c := by
  obtain ⟨agent₁, sa, sb, ha, hb₁, hablt⟩ := p.po_iff.mp hab
  obtain ⟨agent₂, sb₂, sc, hb₂, hc, hbclt⟩ := p.po_iff.mp hbc
  have hp : (agent₁, sb) = (agent₂, sb₂) := Option.some.inj (hb₁.symm.trans hb₂)
  have hAgent : agent₁ = agent₂ := congrArg Prod.fst hp
  have hSequence : sb = sb₂ := congrArg Prod.snd hp
  subst agent₂
  subst sb₂
  exact p.po_iff.mpr ⟨agent₁, sa, sc, ha, hc, Nat.lt_trans hablt hbclt⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Distinct events on one agent are ordered by their unique local sequences. -/
theorem po_total_same_agent (p : ProgramOrderProjection g Agent) {a b : EventId}
    {agent : Agent} {sa sb : Nat}
    (ha : p.programPoint a = some (agent, sa))
    (hb : p.programPoint b = some (agent, sb))
    (hne : a ≠ b) : g.po a b ∨ g.po b a := by
  have hseq : sa ≠ sb := by
    intro heq
    subst sb
    exact hne (p.sequence_unique ha hb)
  rcases Nat.lt_or_gt_of_ne hseq with hlt | hgt
  · exact Or.inl (p.po_iff.mpr ⟨agent, sa, sb, ha, hb, hlt⟩)
  · exact Or.inr (p.po_iff.mpr ⟨agent, sb, sa, hb, ha, hgt⟩)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Structural initial writes participate in no CPU program-order edge. -/
theorem initial_not_in_po (p : ProgramOrderProjection g Agent) {init : EventId} {loc : Location}
    (hi : g.initialAt init loc) :
    (∀ other, ¬ g.po init other) ∧ (∀ other, ¬ g.po other init) :=
  ⟨p.no_po_from_none (p.initial_no_point hi), p.no_po_to_none (p.initial_no_point hi)⟩

end ProgramOrderProjection

end Graph

end Gasm.MemoryModel.CpuGraph

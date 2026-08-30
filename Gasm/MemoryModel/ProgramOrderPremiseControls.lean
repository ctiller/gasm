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
Private signature controls for `ProgramOrderProjection` helper theorems.

`EventId` deliberately has no `DecidableEq` derivation or local classical instance. Applying every
public helper over this type ensures that generic program-order consequences retain only their
mathematical projection premises. These controls construct no graph, target projection, execution,
fidelity, admission, or authority witness.
-/

namespace Gasm.MemoryModel.CpuGraph.ProgramOrderPremiseControls

open Graph

private structure EventId where
  predicate : Nat → Prop

private abbrev TestGraph := Graph EventId Unit Unit Unit

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem endpoints (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {a b : EventId} (hpo : g.po a b) : a ∈ g.events ∧ b ∈ g.events :=
  p.po_endpoints hpo

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem same_agent (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {a b : EventId} (hpo : g.po a b) :
    ∃ agent sa sb,
      p.programPoint a = some (agent, sa) ∧
      p.programPoint b = some (agent, sb) :=
  p.po_same_agent hpo

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem no_edge_from_none (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {a : EventId} (ha : p.programPoint a = none) : ∀ b, ¬ g.po a b :=
  p.no_po_from_none ha

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem no_edge_to_none (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {b : EventId} (hb : p.programPoint b = none) : ∀ a, ¬ g.po a b :=
  p.no_po_to_none hb

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem irreflexive (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    (a : EventId) : ¬ g.po a a :=
  p.po_irrefl a

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem transitive (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {a b c : EventId} (hab : g.po a b) (hbc : g.po b c) : g.po a c :=
  p.po_trans hab hbc

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem total_on_one_agent (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {a b : EventId} {agent : Unit} {sa sb : Nat}
    (ha : p.programPoint a = some (agent, sa))
    (hb : p.programPoint b = some (agent, sb))
    (hne : a ≠ b) : g.po a b ∨ g.po b a :=
  p.po_total_same_agent ha hb hne

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem initial_excluded (g : TestGraph) (p : g.ProgramOrderProjection Unit)
    {init : EventId} {loc : Unit} (hi : g.initialAt init loc) :
    (∀ other, ¬ g.po init other) ∧ (∀ other, ¬ g.po other init) :=
  p.initial_not_in_po hi

end Gasm.MemoryModel.CpuGraph.ProgramOrderPremiseControls

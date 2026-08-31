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
Thin heterogeneous execution-envelope carriers.

This checkpoint records only finite, execution-local identities and profile-owned labelled relation
occurrences. `Domains.Consequence` and `Domains.ConsequenceOccurrenceId` are opaque vocabulary only:
this module defines no consequence carrier membership, occurrence/path binding, semantics, fidelity,
admission, or authority.
It likewise defines no bindings, aliasing, CPU projection, architecture consistency, execution
admission, visibility, linear authority, or global identity allocation. Profiles select only the
domain types they actually use; this module assigns none of them CPU, platform, device, or API
semantics.
-/

namespace Gasm.MemoryModel.Envelope

universe u

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- Profile-indexed domains for one heterogeneous execution envelope.

Identity values are nominal and execution-local only through membership in a concrete well-formed
carrier. Well-formedness proves uniqueness of listed identities and exact record resolution; it
proves no allocation history, global freshness, cross-execution inequality, or authority. Merely
inhabiting one of these types grants no event membership, origin, authority, or target meaning. -/
structure Domains where
  AgentId : Type u
  ReferenceId : Type u
  Location : Type u
  EventId : Type u
  EventPayload : Type u
  RelationOccurrenceId : Type u
  RelationLabel : Type u
  ConsequenceOccurrenceId : Type u
  Consequence : Type u

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- One profile-owned event payload, optionally attributed to an execution agent. -/
structure EventRecord (d : Domains) where
  agent : Option d.AgentId
  payload : d.EventPayload

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- The exact endpoints and profile-owned label of one nominal relation occurrence. -/
structure RelationRecord (d : Domains) where
  source : d.EventId
  label : d.RelationLabel
  target : d.EventId

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- Finite execution-local carriers and a profile-owned labelled source relation.

Carrier list order is not semantic order. Event order, causality, and target relations are expressed
only through selected relation labels and later certificates. -/
structure Execution (d : Domains) where
  agents : List d.AgentId
  references : List d.ReferenceId
  locations : List d.Location
  events : List d.EventId
  event : d.EventId → Option (EventRecord d)
  relationOccurrences : List d.RelationOccurrenceId
  relationOccurrence : d.RelationOccurrenceId → Option (RelationRecord d)

namespace Execution

variable {d : Domains} {x : Execution d}

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- The derived extensional relation. Nominal occurrences and their record map are the only source
of relation authority; this predicate cannot introduce a second independently-authored edge. -/
def relation (x : Execution d) (source : d.EventId) (label : d.RelationLabel)
    (target : d.EventId) : Prop :=
  ∃ occurrence,
    occurrence ∈ x.relationOccurrences ∧
    x.relationOccurrence occurrence = some ⟨source, label, target⟩

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- Structural carrier validity, without target fidelity or execution authority. -/
structure WellFormed (x : Execution d) : Prop where
  agents_nodup : x.agents.Nodup
  references_nodup : x.references.Nodup
  locations_nodup : x.locations.Nodup
  events_nodup : x.events.Nodup
  relation_occurrences_nodup : x.relationOccurrences.Nodup
  event_coverage (eventId) :
    eventId ∈ x.events ↔ ∃ record, x.event eventId = some record
  event_agent_mem {eventId record agent} :
    x.event eventId = some record → record.agent = some agent → agent ∈ x.agents
  relation_coverage (occurrence) :
    occurrence ∈ x.relationOccurrences ↔
      ∃ record, x.relationOccurrence occurrence = some record
  relation_endpoints {occurrence record} :
    x.relationOccurrence occurrence = some record →
      record.source ∈ x.events ∧ record.target ∈ x.events

namespace WellFormed

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- A resolved event record belongs to the exact execution carrier. -/
theorem event_mem (h : x.WellFormed) {eventId record}
    (resolved : x.event eventId = some record) : eventId ∈ x.events :=
  (h.event_coverage eventId).2 ⟨record, resolved⟩

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- Every listed event resolves to a profile-owned record. -/
theorem event_exists (h : x.WellFormed) {eventId}
    (member : eventId ∈ x.events) : ∃ record, x.event eventId = some record :=
  (h.event_coverage eventId).1 member

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- A resolved nominal relation occurrence belongs to the exact execution carrier. -/
theorem relation_occurrence_mem (h : x.WellFormed) {occurrence record}
    (resolved : x.relationOccurrence occurrence = some record) :
    occurrence ∈ x.relationOccurrences :=
  (h.relation_coverage occurrence).2 ⟨record, resolved⟩

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- Every listed nominal relation occurrence resolves to one record. -/
theorem relation_occurrence_exists (h : x.WellFormed) {occurrence}
    (member : occurrence ∈ x.relationOccurrences) :
    ∃ record, x.relationOccurrence occurrence = some record :=
  (h.relation_coverage occurrence).1 member

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- The source of every selected relation occurrence is an event of this execution. -/
theorem relation_source_mem (h : x.WellFormed) {source label target}
    (related : x.relation source label target) : source ∈ x.events := by
  obtain ⟨occurrence, _, resolved⟩ := related
  exact (h.relation_endpoints resolved).1

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
/-- The target of every selected relation occurrence is an event of this execution. -/
theorem relation_target_mem (h : x.WellFormed) {source label target}
    (related : x.relation source label target) : target ∈ x.events := by
  obtain ⟨occurrence, _, resolved⟩ := related
  exact (h.relation_endpoints resolved).2

end WellFormed

end Execution

end Gasm.MemoryModel.Envelope

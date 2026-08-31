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

import Gasm.MemoryModel.Envelope

/-!
Private inhabitation and malformed-carrier controls for the thin heterogeneous envelope.

These controls prove only structural consistency and rejection. The opaque consequence and nominal
consequence-occurrence identity types are vocabulary only; the controls grant no consequence
carrier membership, occurrence/path binding, semantics, fidelity, admission, or authority. They
likewise grant no target fidelity, execution admission, synchronization, visibility, linear
authority, or M0-completion claim.
-/

namespace Gasm.MemoryModel.Envelope.Controls

private inductive Agent where
  | parent
  | child
  | outside

private inductive Reference where
  | shared
  | outside

private inductive Location where
  | payload
  | outside

private inductive Event where
  | parent
  | child
  | outside

private inductive Payload where
  | parent
  | child

private inductive Label where
  | source

private inductive RelationOccurrence where
  | first
  | second
  | outside

private inductive ConsequenceOccurrence where
  | reserved

private def domains : Domains where
  AgentId := Agent
  ReferenceId := Reference
  Location := Location
  EventId := Event
  EventPayload := Payload
  RelationOccurrenceId := RelationOccurrence
  RelationLabel := Label
  ConsequenceOccurrenceId := ConsequenceOccurrence
  Consequence := Unit

private def record : Event → Option (EventRecord domains)
  | .parent => some ⟨some .parent, .parent⟩
  | .child => some ⟨some .child, .child⟩
  | .outside => none

private def base : Execution domains where
  agents := [.parent, .child]
  references := [.shared]
  locations := [.payload]
  events := [.parent, .child]
  event := record
  relationOccurrences := [.first, .second]
  relationOccurrence := fun
    | .first => some ⟨.parent, .source, .child⟩
    | .second => some ⟨.parent, .source, .child⟩
    | .outside => none

private theorem agent_outside_not_mem : Agent.outside ∉ [Agent.parent, Agent.child] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem reference_shared_nodup : ([Reference.shared] : List Reference).Nodup := by
  exact .cons (by intro _ member; cases member) .nil

private theorem location_payload_nodup : ([Location.payload] : List Location).Nodup := by
  exact .cons (by intro _ member; cases member) .nil

private theorem agent_carrier_nodup : ([Agent.parent, Agent.child] : List Agent).Nodup := by
  exact .cons (by
    intro candidate member
    rw [List.mem_singleton] at member
    subst candidate
    intro equal
    cases equal) (.cons (by intro _ member; cases member) .nil)

private theorem event_carrier_nodup : ([Event.parent, Event.child] : List Event).Nodup := by
  exact .cons (by
    intro candidate member
    rw [List.mem_singleton] at member
    subst candidate
    intro equal
    cases equal) (.cons (by intro _ member; cases member) .nil)

private theorem relation_occurrence_carrier_nodup :
    ([RelationOccurrence.first, RelationOccurrence.second] : List RelationOccurrence).Nodup := by
  exact .cons (by
    intro candidate member
    rw [List.mem_singleton] at member
    subst candidate
    intro equal
    cases equal) (.cons (by intro _ member; cases member) .nil)

private theorem event_outside_not_mem : Event.outside ∉ [Event.parent, Event.child] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem relation_occurrence_outside_not_mem :
    RelationOccurrence.outside ∉ [RelationOccurrence.first, RelationOccurrence.second] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem base_wellFormed : base.WellFormed := by
  constructor
  · exact agent_carrier_nodup
  · exact reference_shared_nodup
  · exact location_payload_nodup
  · exact event_carrier_nodup
  · exact relation_occurrence_carrier_nodup
  · intro eventId
    cases eventId
    · constructor
      · intro _
        exact ⟨⟨some .parent, .parent⟩, rfl⟩
      · intro _
        exact List.Mem.head _
    · constructor
      · intro _
        exact ⟨⟨some .child, .child⟩, rfl⟩
      · intro _
        exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · exact fun member => (event_outside_not_mem member).elim
      · rintro ⟨eventRecord, resolved⟩
        cases resolved
  · intro eventId eventRecord agent resolved assigned
    cases eventId
    · cases resolved
      cases assigned
      exact List.Mem.head _
    · cases resolved
      cases assigned
      exact List.Mem.tail _ (List.Mem.head _)
    · cases resolved
  · intro occurrence
    cases occurrence
    · constructor
      · intro _
        exact ⟨⟨.parent, .source, .child⟩, rfl⟩
      · intro _
        exact List.Mem.head _
    · constructor
      · intro _
        exact ⟨⟨.parent, .source, .child⟩, rfl⟩
      · intro _
        exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · exact fun member => (relation_occurrence_outside_not_mem member).elim
      · rintro ⟨relationRecord, resolved⟩
        cases resolved
  · intro occurrence relationRecord resolved
    cases occurrence
    · cases resolved
      exact ⟨List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩
    · cases resolved
      exact ⟨List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩
    · cases resolved

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem equal_records_preserve_distinct_occurrences :
    RelationOccurrence.first ≠ RelationOccurrence.second ∧
      base.relationOccurrence .first = base.relationOccurrence .second := by
  constructor
  · intro equal
    cases equal
  · rfl

private def duplicateEvent : Execution domains :=
  { base with events := [.parent, .parent, .child] }

private def duplicateAgent : Execution domains :=
  { base with agents := [.parent, .parent, .child] }

private def duplicateReference : Execution domains :=
  { base with references := [.shared, .shared] }

private def duplicateLocation : Execution domains :=
  { base with locations := [.payload, .payload] }

private def duplicateRelationOccurrence : Execution domains :=
  { base with relationOccurrences := [.first, .first, .second] }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem duplicate_event_rejected : ¬ duplicateEvent.WellFormed := by
  intro h
  cases h.events_nodup with
  | cons notMember _ => exact (notMember Event.parent (List.Mem.head _)) rfl

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem duplicate_agent_rejected : ¬ duplicateAgent.WellFormed := by
  intro h
  cases h.agents_nodup with
  | cons notMember _ => exact (notMember Agent.parent (List.Mem.head _)) rfl

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem duplicate_reference_rejected : ¬ duplicateReference.WellFormed := by
  intro h
  cases h.references_nodup with
  | cons notMember _ => exact (notMember Reference.shared (List.Mem.head _)) rfl

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem duplicate_location_rejected : ¬ duplicateLocation.WellFormed := by
  intro h
  cases h.locations_nodup with
  | cons notMember _ => exact (notMember Location.payload (List.Mem.head _)) rfl

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem duplicate_relation_occurrence_rejected :
    ¬ duplicateRelationOccurrence.WellFormed := by
  intro h
  cases h.relation_occurrences_nodup with
  | cons notMember _ => exact (notMember RelationOccurrence.first (List.Mem.head _)) rfl

private def listedWithoutRecord : Execution domains :=
  { base with events := [.parent, .child, .outside] }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem listed_without_record_rejected : ¬ listedWithoutRecord.WellFormed := by
  intro h
  obtain ⟨eventRecord, resolved⟩ :=
    (h.event_coverage .outside).1
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  cases resolved

private def offCarrierRecord : Execution domains :=
  { base with
    event := fun
      | .parent => record .parent
      | .child => record .child
      | .outside => some ⟨none, .parent⟩ }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem off_carrier_record_rejected : ¬ offCarrierRecord.WellFormed := by
  intro h
  have member := h.event_mem (eventId := Event.outside) (record := ⟨none, .parent⟩) (by rfl)
  exact event_outside_not_mem member

private def offCarrierAgent : Execution domains :=
  { base with
    event := fun
      | .parent => some ⟨some .outside, .parent⟩
      | .child => record .child
      | .outside => none }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem off_carrier_agent_rejected : ¬ offCarrierAgent.WellFormed := by
  intro h
  have member := h.event_agent_mem (eventId := Event.parent)
    (record := (⟨some Agent.outside, Payload.parent⟩ : EventRecord domains))
    (agent := Agent.outside) (by rfl) (by rfl)
  exact agent_outside_not_mem member

private def listedRelationWithoutRecord : Execution domains :=
  { base with relationOccurrences := [.first, .second, .outside] }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem listed_relation_without_record_rejected :
    ¬ listedRelationWithoutRecord.WellFormed := by
  intro h
  obtain ⟨relationRecord, resolved⟩ :=
    (h.relation_coverage .outside).1
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  cases resolved

private def offCarrierRelationRecord : Execution domains :=
  { base with
    relationOccurrence := fun
      | .first => base.relationOccurrence .first
      | .second => base.relationOccurrence .second
      | .outside => some ⟨.parent, .source, .child⟩ }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem off_carrier_relation_record_rejected : ¬ offCarrierRelationRecord.WellFormed := by
  intro h
  have member := h.relation_occurrence_mem (occurrence := RelationOccurrence.outside)
    (record := (⟨.parent, .source, .child⟩ : RelationRecord domains)) (by rfl)
  exact relation_occurrence_outside_not_mem member

private def offCarrierSource : Execution domains :=
  { base with
    relationOccurrence := fun
      | .first => some ⟨.outside, .source, .child⟩
      | .second => base.relationOccurrence .second
      | .outside => none }

private def offCarrierTarget : Execution domains :=
  { base with
    relationOccurrence := fun
      | .first => some ⟨.parent, .source, .outside⟩
      | .second => base.relationOccurrence .second
      | .outside => none }

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem off_carrier_relation_source_rejected : ¬ offCarrierSource.WellFormed := by
  intro h
  have member := (h.relation_endpoints (occurrence := RelationOccurrence.first)
    (record := (⟨.outside, .source, .child⟩ : RelationRecord domains)) (by rfl)).1
  exact event_outside_not_mem member

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem off_carrier_relation_target_rejected : ¬ offCarrierTarget.WellFormed := by
  intro h
  have member := (h.relation_endpoints (occurrence := RelationOccurrence.first)
    (record := (⟨.parent, .source, .outside⟩ : RelationRecord domains)) (by rfl)).2
  exact event_outside_not_mem member

end Gasm.MemoryModel.Envelope.Controls

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

import Gasm.MemoryModel.EnvelopeOccurrencePath

/-!
Private positive and malformed-path controls for `EnvelopeOccurrencePath`.

The fixture deliberately contains two distinct occurrence IDs with the same stored relation record.
Both exact one-edge paths erase to the same extensional relation path, demonstrating why erasure has
no generic inverse. These controls grant no well-formedness, target fidelity, consequence,
admission, or execution authority.
-/

namespace Gasm.MemoryModel.EnvelopeOccurrencePath.Controls

open Gasm.MemoryModel.Envelope
open Gasm.MemoryModel.EnvelopeOccurrencePath
open Gasm.MemoryModel.RelationPath

private inductive Agent where | worker
private inductive Reference where | shared
private inductive Location where | byte
private inductive Event where | first | middle | last
private inductive Payload where | step
private inductive Occurrence where | first | second | duplicate | outside
private inductive Label where | before | after
private inductive ConsequenceOccurrence where | none

private def domains : Envelope.Domains where
  AgentId := Agent
  ReferenceId := Reference
  Location := Location
  EventId := Event
  EventPayload := Payload
  RelationOccurrenceId := Occurrence
  RelationLabel := Label
  ConsequenceOccurrenceId := ConsequenceOccurrence
  Consequence := Unit

private def relationRecord : Occurrence → Option (RelationRecord domains)
  | .first | .duplicate => some ⟨.first, .before, .middle⟩
  | .second => some ⟨.middle, .after, .last⟩
  | .outside => none

private def execution : Envelope.Execution domains where
  agents := [.worker]
  references := [.shared]
  locations := [.byte]
  events := [.first, .middle, .last]
  event := fun _ => some ⟨some .worker, .step⟩
  relationOccurrences := [.first, .second, .duplicate]
  relationOccurrence := relationRecord

private theorem exact_two_edge_path :
    OccurrencePath execution .first .last [.first, .second] [.before, .after] := by
  exact .cons ⟨List.Mem.head _, rfl⟩ (.single ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem exact_path_erases_to_extensional_path :
    LabeledPath execution.relation .first .last [.before, .after] :=
  exact_two_edge_path.erase

private theorem first_occurrence_path :
    OccurrencePath execution .first .middle [.first] [.before] :=
  .single ⟨List.Mem.head _, rfl⟩

private theorem duplicate_occurrence_path :
    OccurrencePath execution .first .middle [.duplicate] [.before] :=
  .single ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl⟩

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem distinct_occurrences_may_erase_to_the_same_path :
    LabeledPath execution.relation .first .middle [.before] ∧
      LabeledPath execution.relation .first .middle [.before] :=
  ⟨first_occurrence_path.erase, duplicate_occurrence_path.erase⟩

private theorem outside_not_mem :
    Occurrence.outside ∉ [Occurrence.first, Occurrence.second, Occurrence.duplicate] := by
  intro member
  rw [List.mem_cons, List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal | equal <;> cases equal

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem off_carrier_occurrence_rejected :
    ¬ OccurrenceEdge execution .outside .first .before .middle := by
  intro edge
  exact outside_not_mem edge.1

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem wrong_stored_label_rejected :
    ¬ OccurrenceEdge execution .first .first .after .middle := by
  rintro ⟨_, resolved⟩
  cases resolved

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem wrong_stored_endpoint_rejected :
    ¬ OccurrenceEdge execution .second .first .after .last := by
  rintro ⟨_, resolved⟩
  cases resolved

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
private theorem omitted_occurrence_identity_rejected :
    ¬ OccurrencePath execution .first .last [.first] [.before, .after] := by
  intro path
  have lengths := path.lengths_eq
  change 1 = 2 at lengths
  omega

end Gasm.MemoryModel.EnvelopeOccurrencePath.Controls

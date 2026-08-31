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
import Gasm.MemoryModel.RelationPath

/-!
Exact relation-occurrence paths for the heterogeneous execution envelope.

`OccurrenceEdge` retains the stable execution-local occurrence identity as well as its stored
source, label, and target. `OccurrencePath` retains both the exact occurrence sequence and the
exact label sequence. Its one-way `erase` theorem produces the existing extensional labelled path;
there is deliberately no exact, canonical, or choice-preserving inverse because the extensional
relation forgets which nominal occurrence supplied an edge. An existential lift can choose the
occurrence witness already stored in each extensional edge; that generic roundtrip is deferred here,
not claimed impossible.

This module proves no envelope well-formedness, target fidelity, selected/observable projection,
consequence, admission, chronology, or execution authority. Carrier order is not path order, and
distinct carrier occurrences may store equal relation records unless a separate certificate rules
that out.
-/

namespace Gasm.MemoryModel.EnvelopeOccurrencePath

open Gasm.MemoryModel.Envelope
open Gasm.MemoryModel.RelationPath

universe u

variable {d : Envelope.Domains}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- One exact carrier occurrence and the relation record it stores. -/
def OccurrenceEdge (x : Envelope.Execution d) (occurrence : d.RelationOccurrenceId)
    (source : d.EventId) (label : d.RelationLabel) (target : d.EventId) : Prop :=
  occurrence ∈ x.relationOccurrences ∧
    x.relationOccurrence occurrence = some ⟨source, label, target⟩

namespace OccurrenceEdge

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Forgetting the occurrence identity yields exactly the envelope's extensional relation. -/
theorem toRelation {x : Envelope.Execution d} {occurrence source label target}
    (edge : OccurrenceEdge x occurrence source label target) :
    x.relation source label target :=
  ⟨occurrence, edge.1, edge.2⟩

end OccurrenceEdge

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- A nonempty envelope path retaining the exact occurrence IDs and labels in traversal order. -/
inductive OccurrencePath (x : Envelope.Execution d) :
    d.EventId → d.EventId → List d.RelationOccurrenceId → List d.RelationLabel → Prop where
  | single {source target occurrence label} :
      OccurrenceEdge x occurrence source label target →
      OccurrencePath x source target [occurrence] [label]
  | cons {source middle target occurrence label occurrences labels} :
      OccurrenceEdge x occurrence source label middle →
      OccurrencePath x middle target occurrences labels →
      OccurrencePath x source target (occurrence :: occurrences) (label :: labels)

namespace OccurrencePath

variable {x : Envelope.Execution d}
variable {source middle target : d.EventId}
variable {occurrences leftOccurrences rightOccurrences : List d.RelationOccurrenceId}
variable {labels leftLabels rightLabels : List d.RelationLabel}

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
theorem occurrences_nonempty
    (path : OccurrencePath x source target occurrences labels) : occurrences ≠ [] := by
  cases path <;> simp

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
theorem labels_nonempty
    (path : OccurrencePath x source target occurrences labels) : labels ≠ [] := by
  cases path <;> simp

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Every traversed source edge contributes exactly one occurrence identity and one label. -/
theorem lengths_eq
    (path : OccurrencePath x source target occurrences labels) :
    occurrences.length = labels.length := by
  induction path with
  | single => rfl
  | cons _ _ ih => simp [ih]

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- Concatenation retains both exact source sequences in left-to-right traversal order. -/
theorem append
    (left : OccurrencePath x source middle leftOccurrences leftLabels)
    (right : OccurrencePath x middle target rightOccurrences rightLabels) :
    OccurrencePath x source target
      (leftOccurrences ++ rightOccurrences) (leftLabels ++ rightLabels) := by
  induction left with
  | single first =>
      simpa using OccurrencePath.cons first right
  | cons first rest ih =>
      simpa using OccurrencePath.cons first (ih right)

/- REF: docs/MEMORY_MODEL.md#11-causality-and-observable-traces -/
/-- One-way erasure forgets only occurrence IDs and preserves the exact label path. -/
theorem erase (path : OccurrencePath x source target occurrences labels) :
    LabeledPath x.relation source target labels := by
  induction path with
  | single step => exact .single step.toRelation
  | cons step rest ih => exact .cons step.toRelation ih

end OccurrencePath

end Gasm.MemoryModel.EnvelopeOccurrencePath

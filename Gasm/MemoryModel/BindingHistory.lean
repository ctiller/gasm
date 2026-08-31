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
Structural, execution-local binding histories for the heterogeneous envelope.

This checkpoint records nominal binding instances, inherited or unbound roots, transition
predecessors, captures, and uses of exact captures. It grants no global identity allocation,
chronology, liveness, target fidelity, alias semantics, path evidence, consequence admission, or
execution authority. List order is never semantic order. Target profiles must later connect these
nominal links to selected envelope relation-occurrence paths and prove that a capture names the
latest live binding at its event.

`History.WellFormed x h` is intentionally independent of `x.WellFormed`: it proves endpoint
membership relative to the supplied carriers, not validity of those carriers. Every admitted
consumer must require the envelope and binding-history certificates separately (or through a later
thin bundle that contains both exactly once).

A captured suffix may re-root an inherited current binding with `RootRecord`. This module proves no
naive history truncation, concatenation, or composition theorem: a later splicing certificate must
reconcile an earlier transition introduction with the later prefix root while preserving unique
in-history introduction.
-/

namespace Gasm.MemoryModel.BindingHistory

open Gasm.MemoryModel.Envelope

universe u

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Profile-indexed vocabulary for one binding history. None of these types carries target meaning
without a concrete profile refinement. -/
structure Domains where
  ObjectInstanceId : Type u
  BindingKey : Type u
  BindingGeneration : Type u
  BindingInstanceId : Type u
  Rights : Type u
  LogicalFootprint : Type u
  BackingFootprint : Type u
  RootOccurrenceId : Type u
  TransitionOccurrenceId : Type u
  CaptureOccurrenceId : Type u
  UseOccurrenceId : Type u

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- The sole record authority for one nominal binding instance. -/
structure BindingRecord (d : Domains) where
  key : d.BindingKey
  generation : d.BindingGeneration
  object : d.ObjectInstanceId
  rights : d.Rights
  logicalFootprint : d.LogicalFootprint
  backingFootprint : d.BackingFootprint

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- An execution prefix begins each selected key either unbound or at one inherited binding.
The root supplies no fabricated creation event or global origin claim. -/
structure RootRecord (d : Domains) where
  key : d.BindingKey
  initial : Option d.BindingInstanceId

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A nominal point whose state is derived from exactly one root or transition record. -/
inductive Frontier (d : Domains) where
  | root (occurrence : d.RootOccurrenceId)
  | transition (occurrence : d.TransitionOccurrenceId)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- One bind, unbind, or rebind occurrence. Its before-state is derived from `predecessor`; the
three transition shapes are not duplicated as an independently authored tag. -/
structure TransitionRecord (e : Envelope.Domains) (d : Domains) where
  event : e.EventId
  key : d.BindingKey
  predecessor : Frontier d
  rank : Nat
  after : Option d.BindingInstanceId

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- An event-time capture of the binding stored at one nominal frontier. -/
structure CaptureRecord (e : Envelope.Domains) (d : Domains) where
  event : e.EventId
  reference : e.ReferenceId
  frontier : Frontier d

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A later use names the exact capture it consumes and carries no duplicated binding snapshot. -/
structure UseRecord (e : Envelope.Domains) (d : Domains) where
  event : e.EventId
  capture : d.CaptureOccurrenceId

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Finite nominal carriers and exact record maps for a binding-history checkpoint. -/
structure History (e : Envelope.Domains) (d : Domains) where
  bindingInstances : List d.BindingInstanceId
  bindingRecord : d.BindingInstanceId → Option (BindingRecord d)
  roots : List d.RootOccurrenceId
  rootRecord : d.RootOccurrenceId → Option (RootRecord d)
  transitions : List d.TransitionOccurrenceId
  transitionRecord : d.TransitionOccurrenceId → Option (TransitionRecord e d)
  captures : List d.CaptureOccurrenceId
  captureRecord : d.CaptureOccurrenceId → Option (CaptureRecord e d)
  uses : List d.UseOccurrenceId
  useRecord : d.UseOccurrenceId → Option (UseRecord e d)

namespace History

variable {e : Envelope.Domains} {d : Domains}

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Constructive exclusive choice used for exact in-history introduction sites. -/
def ExclusiveOr (left right : Prop) : Prop :=
  (left ∧ ¬ right) ∨ (right ∧ ¬ left)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Existence of exactly one nominal site, stated without decidable equality. -/
def UniqueSite {α : Type u} (selected : α → Prop) : Prop :=
  ∃ site, selected site ∧ ∀ other, selected other → other = site

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Exact resolution of a frontier, including its key and possibly-unbound state. -/
def FrontierResolves (h : History e d) : Frontier d → d.BindingKey →
    Option d.BindingInstanceId → Prop
  | .root occurrence, key, state =>
      ∃ record, h.rootRecord occurrence = some record ∧
        record.key = key ∧ record.initial = state
  | .transition occurrence, key, state =>
      ∃ record, h.transitionRecord occurrence = some record ∧
        record.key = key ∧ record.after = state

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A root is one possible in-history introduction site for a binding instance. -/
def RootIntroduces (h : History e d) (binding : d.BindingInstanceId)
    (root : d.RootOccurrenceId) : Prop :=
  ∃ record, h.rootRecord root = some record ∧ record.initial = some binding

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A transition after-state is the other possible in-history introduction site. -/
def TransitionIntroduces (h : History e d) (binding : d.BindingInstanceId)
    (transition : d.TransitionOccurrenceId) : Prop :=
  ∃ record, h.transitionRecord transition = some record ∧ record.after = some binding

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- The exact binding derived from a capture's nominal frontier. -/
def Captures (h : History e d) (capture : d.CaptureOccurrenceId)
    (binding : d.BindingInstanceId) : Prop :=
  ∃ record key,
    h.captureRecord capture = some record ∧
    h.FrontierResolves record.frontier key (some binding)

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- The binding used through an exact capture link. This definition performs no key lookup at the
use event and therefore cannot silently redirect after a rebind. -/
def Uses (h : History e d) (use : d.UseOccurrenceId) (binding : d.BindingInstanceId) : Prop :=
  ∃ record, h.useRecord use = some record ∧ h.Captures record.capture binding

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Structural binding-history validity only. In particular, this certificate does not prove that
frontiers are temporally latest or live at capture/use events. -/
structure WellFormed (x : Envelope.Execution e) (h : History e d) : Prop where
  binding_instances_nodup : h.bindingInstances.Nodup
  roots_nodup : h.roots.Nodup
  transitions_nodup : h.transitions.Nodup
  captures_nodup : h.captures.Nodup
  uses_nodup : h.uses.Nodup
  binding_coverage (binding) :
    binding ∈ h.bindingInstances ↔ ∃ record, h.bindingRecord binding = some record
  root_coverage (root) :
    root ∈ h.roots ↔ ∃ record, h.rootRecord root = some record
  transition_coverage (transition) :
    transition ∈ h.transitions ↔ ∃ record, h.transitionRecord transition = some record
  capture_coverage (capture) :
    capture ∈ h.captures ↔ ∃ record, h.captureRecord capture = some record
  use_coverage (use) :
    use ∈ h.uses ↔ ∃ record, h.useRecord use = some record
  root_key_unique {left right leftRecord rightRecord} :
    h.rootRecord left = some leftRecord →
    h.rootRecord right = some rightRecord →
    leftRecord.key = rightRecord.key → left = right
  root_initial_resolves {root rootRecord binding} :
    h.rootRecord root = some rootRecord → rootRecord.initial = some binding →
    ∃ record, h.bindingRecord binding = some record ∧ record.key = rootRecord.key
  transition_event_mem {transition record} :
    h.transitionRecord transition = some record → record.event ∈ x.events
  transition_predecessor {transition record} :
    h.transitionRecord transition = some record →
    ∃ before, h.FrontierResolves record.predecessor record.key before ∧ before ≠ record.after
  transition_rank_decreases {transition record predecessor predecessorRecord} :
    h.transitionRecord transition = some record →
    record.predecessor = .transition predecessor →
    h.transitionRecord predecessor = some predecessorRecord →
    predecessorRecord.rank < record.rank
  transition_after_resolves {transition transitionRecord binding} :
    h.transitionRecord transition = some transitionRecord →
    transitionRecord.after = some binding →
    ∃ record, h.bindingRecord binding = some record ∧ record.key = transitionRecord.key
  successor_unique {left right leftRecord rightRecord} :
    h.transitionRecord left = some leftRecord →
    h.transitionRecord right = some rightRecord →
    leftRecord.predecessor = rightRecord.predecessor → left = right
  binding_key_generation_unique {left right leftRecord rightRecord} :
    h.bindingRecord left = some leftRecord →
    h.bindingRecord right = some rightRecord →
    leftRecord.key = rightRecord.key →
    leftRecord.generation = rightRecord.generation → left = right
  binding_introduction {binding} :
    binding ∈ h.bindingInstances →
      ExclusiveOr (UniqueSite fun root => h.RootIntroduces binding root)
        (UniqueSite fun transition => h.TransitionIntroduces binding transition)
  capture_event_mem {capture record} :
    h.captureRecord capture = some record → record.event ∈ x.events
  capture_reference_mem {capture record} :
    h.captureRecord capture = some record → record.reference ∈ x.references
  capture_frontier_bound {capture record} :
    h.captureRecord capture = some record →
    ∃ key binding, h.FrontierResolves record.frontier key (some binding)
  use_event_mem {use record} :
    h.useRecord use = some record → record.event ∈ x.events
  use_capture_resolves {use record} :
    h.useRecord use = some record →
    ∃ captureRecord, h.captureRecord record.capture = some captureRecord

namespace WellFormed

variable {x : Envelope.Execution e} {h : History e d}

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Every resolved binding instance belongs to the finite carrier. -/
theorem binding_mem (wf : h.WellFormed x) {binding record}
    (resolved : h.bindingRecord binding = some record) : binding ∈ h.bindingInstances :=
  (wf.binding_coverage binding).2 ⟨record, resolved⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- A use resolves its one exact capture; no live-at-use key lookup participates. -/
theorem use_capture (wf : h.WellFormed x) {use record}
    (resolved : h.useRecord use = some record) :
    ∃ captureRecord, h.captureRecord record.capture = some captureRecord :=
  wf.use_capture_resolves resolved

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
/-- Every resolved use derives a binding solely through its exact captured frontier. -/
theorem use_binding (wf : h.WellFormed x) {use record}
    (resolved : h.useRecord use = some record) : ∃ binding, h.Uses use binding := by
  obtain ⟨captureRecord, captureResolved⟩ := wf.use_capture_resolves resolved
  obtain ⟨key, binding, frontierResolved⟩ := wf.capture_frontier_bound captureResolved
  exact ⟨binding, record, resolved, captureRecord, key, captureResolved, frontierResolved⟩

end WellFormed

end History

end Gasm.MemoryModel.BindingHistory

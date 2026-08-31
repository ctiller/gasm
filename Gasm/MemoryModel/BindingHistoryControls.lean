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

import Gasm.MemoryModel.BindingHistory

/-!
Private inhabitation and malformed-history controls for `BindingHistory`.

The positive fixture has a bound inherited root, a capture of that binding, a rebind to a new
instance, and a later use of the exact old capture. A second initially-unbound key is bound by its
first transition. Distinct keys deliberately store equal backing-footprint data; this asserts no
semantic alias or overlap relation.

These controls grant no chronology, latest/live lookup, target fidelity, global origin, history
composition, consequence admission, or execution authority.
-/

namespace Gasm.MemoryModel.BindingHistory.Controls

open Gasm.MemoryModel.Envelope
open Gasm.MemoryModel.BindingHistory

private inductive Agent where | worker
private inductive Reference where | shared | outside
private inductive Location where | byte
private inductive Event where | capture | rebind | bind | use | outside
private inductive Payload where | step
private inductive RelationOccurrence where | none
private inductive RelationLabel where | opaque
private inductive ConsequenceOccurrence where | none

private def envelopeDomains : Envelope.Domains where
  AgentId := Agent
  ReferenceId := Reference
  Location := Location
  EventId := Event
  EventPayload := Payload
  RelationOccurrenceId := RelationOccurrence
  RelationLabel := RelationLabel
  ConsequenceOccurrenceId := ConsequenceOccurrence
  Consequence := Unit

private def execution : Envelope.Execution envelopeDomains where
  agents := [.worker]
  references := [.shared]
  locations := [.byte]
  events := [.capture, .rebind, .bind, .use]
  event := fun
    | .capture | .rebind | .bind | .use => some ⟨some .worker, .step⟩
    | .outside => none
  relationOccurrences := []
  relationOccurrence := fun _ => none

private inductive Object where | storage
private inductive Key where | inherited | fresh
private inductive Generation where | zero | one
private inductive Binding where | inherited0 | inherited1 | fresh0
private inductive Rights where | readWrite
private inductive LogicalFootprint where | inherited | fresh
private inductive BackingFootprint where | shared
private inductive Root where | inherited | fresh | duplicate
private inductive Transition where | rebind | bind | fork | later | outside
private inductive Capture where | old | outside
private inductive Use where | old | outside

private def domains : BindingHistory.Domains where
  ObjectInstanceId := Object
  BindingKey := Key
  BindingGeneration := Generation
  BindingInstanceId := Binding
  Rights := Rights
  LogicalFootprint := LogicalFootprint
  BackingFootprint := BackingFootprint
  RootOccurrenceId := Root
  TransitionOccurrenceId := Transition
  CaptureOccurrenceId := Capture
  UseOccurrenceId := Use

private def bindingRecord : Binding → Option (BindingRecord domains)
  | .inherited0 => some ⟨.inherited, .zero, .storage, .readWrite, .inherited, .shared⟩
  | .inherited1 => some ⟨.inherited, .one, .storage, .readWrite, .inherited, .shared⟩
  | .fresh0 => some ⟨.fresh, .zero, .storage, .readWrite, .fresh, .shared⟩

private def rootRecord : Root → Option (RootRecord domains)
  | .inherited => some ⟨.inherited, some .inherited0⟩
  | .fresh => some ⟨.fresh, none⟩
  | .duplicate => none

private def transitionRecord : Transition →
    Option (TransitionRecord envelopeDomains domains)
  | .rebind => some ⟨.rebind, .inherited, .root .inherited, 1, some .inherited1⟩
  | .bind => some ⟨.bind, .fresh, .root .fresh, 1, some .fresh0⟩
  | .fork | .later | .outside => none

private def captureRecord : Capture → Option (CaptureRecord envelopeDomains domains)
  | .old => some ⟨.capture, .shared, .root .inherited⟩
  | .outside => none

private def useRecord : Use → Option (UseRecord envelopeDomains domains)
  | .old => some ⟨.use, .old⟩
  | .outside => none

private def base : History envelopeDomains domains where
  bindingInstances := [.inherited0, .inherited1, .fresh0]
  bindingRecord := bindingRecord
  roots := [.inherited, .fresh]
  rootRecord := rootRecord
  transitions := [.rebind, .bind]
  transitionRecord := transitionRecord
  captures := [.old]
  captureRecord := captureRecord
  uses := [.old]
  useRecord := useRecord

private theorem binding0_not_tail :
    Binding.inherited0 ∉ [Binding.inherited1, Binding.fresh0] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem binding1_not_tail : Binding.inherited1 ∉ [Binding.fresh0] := by
  intro member
  rw [List.mem_singleton] at member
  cases member

private theorem root_inherited_not_tail : Root.inherited ∉ [Root.fresh] := by
  intro member
  rw [List.mem_singleton] at member
  cases member

private theorem transition_rebind_not_tail : Transition.rebind ∉ [Transition.bind] := by
  intro member
  rw [List.mem_singleton] at member
  cases member

private theorem root_duplicate_not_mem : Root.duplicate ∉ [Root.inherited, Root.fresh] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem transition_fork_not_mem : Transition.fork ∉ [Transition.rebind, Transition.bind] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem transition_later_not_mem : Transition.later ∉ [Transition.rebind, Transition.bind] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem transition_outside_not_mem : Transition.outside ∉ [Transition.rebind, Transition.bind] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem capture_outside_not_mem : Capture.outside ∉ [Capture.old] := by
  intro member
  rw [List.mem_singleton] at member
  cases member

private theorem use_outside_not_mem : Use.outside ∉ [Use.old] := by
  intro member
  rw [List.mem_singleton] at member
  cases member

private theorem event_capture_not_tail :
    Event.capture ∉ [Event.rebind, Event.bind, Event.use] := by
  intro member
  rw [List.mem_cons, List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal | equal <;> cases equal

private theorem event_rebind_not_tail : Event.rebind ∉ [Event.bind, Event.use] := by
  intro member
  rw [List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal <;> cases equal

private theorem event_bind_not_tail : Event.bind ∉ [Event.use] := by
  intro member
  rw [List.mem_singleton] at member
  cases member

private theorem event_outside_not_mem :
    Event.outside ∉ [Event.capture, Event.rebind, Event.bind, Event.use] := by
  intro member
  rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_singleton] at member
  rcases member with equal | equal | equal | equal <;> cases equal

/- REF: docs/MEMORY_MODEL.md#3-layering-and-ownership-of-semantics -/
private theorem execution_wellFormed : execution.WellFormed := by
  constructor
  · exact .cons (by intro _ member; cases member) .nil
  · exact .cons (by intro _ member; cases member) .nil
  · exact .cons (by intro _ member; cases member) .nil
  · exact .cons (by
      intro other member equal
      subst other
      exact event_capture_not_tail member) (.cons (by
        intro other member equal
        subst other
        exact event_rebind_not_tail member) (.cons (by
          intro other member equal
          subst other
          exact event_bind_not_tail member) (.cons (by intro _ member; cases member) .nil)))
  · exact .nil
  · intro event
    cases event
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · constructor
      · exact fun member => (event_outside_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
  · intro event record agent resolved assigned
    cases event <;> cases resolved
    · cases assigned; exact List.Mem.head _
    · cases assigned; exact List.Mem.head _
    · cases assigned; exact List.Mem.head _
    · cases assigned; exact List.Mem.head _
  · intro occurrence
    cases occurrence
    constructor
    · intro member; cases member
    · rintro ⟨record, resolved⟩; cases resolved
  · intro occurrence record resolved
    cases occurrence
    cases resolved

private theorem base_wellFormed : base.WellFormed execution := by
  constructor
  · exact .cons (by
      intro other member equal
      subst other
      exact binding0_not_tail member) (.cons (by
        intro other member equal
        subst other
        exact binding1_not_tail member) (.cons (by intro _ member; cases member) .nil))
  · exact .cons (by
      intro other member equal
      subst other
      exact root_inherited_not_tail member) (.cons (by intro _ member; cases member) .nil)
  · exact .cons (by
      intro other member equal
      subst other
      exact transition_rebind_not_tail member) (.cons (by intro _ member; cases member) .nil)
  · exact .cons (by intro _ member; cases member) .nil
  · exact .cons (by intro _ member; cases member) .nil
  · intro binding
    cases binding
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · intro root
    cases root
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · exact fun member => (root_duplicate_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
  · intro transition
    cases transition
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · exact fun member => (transition_fork_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
    · constructor
      · exact fun member => (transition_later_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
    · constructor
      · exact fun member => (transition_outside_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
  · intro capture
    cases capture
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · exact fun member => (capture_outside_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
  · intro use
    cases use
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · exact fun member => (use_outside_not_mem member).elim
      · rintro ⟨record, resolved⟩; cases resolved
  · intro left right leftRecord rightRecord leftResolved rightResolved keys
    cases left <;> cases right <;> simp [base, rootRecord] at leftResolved rightResolved
      <;> cases leftResolved <;> cases rightResolved <;> cases keys <;> rfl
  · intro root rr binding rootResolved initial
    cases root
    · cases rootResolved
      cases initial
      exact ⟨_, rfl, rfl⟩
    · cases rootResolved
      cases initial
    · cases rootResolved
  · intro transition record resolved
    cases transition <;> simp [base, transitionRecord] at resolved
    · cases resolved; exact List.Mem.tail _ (List.Mem.head _)
    · cases resolved; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · intro transition record resolved
    cases transition <;> simp [base, transitionRecord] at resolved
    · cases resolved
      exact ⟨some .inherited0, ⟨_, rfl, rfl, rfl⟩, by intro equal; cases equal⟩
    · cases resolved
      exact ⟨none, ⟨_, rfl, rfl, rfl⟩, by intro equal; cases equal⟩
  · intro transition record predecessor predecessorRecord resolved predecessorEq predecessorResolved
    cases transition <;> simp [base, transitionRecord] at resolved
    · cases resolved; cases predecessorEq
    · cases resolved; cases predecessorEq
  · intro transition tr binding resolved after
    cases transition <;> simp [base, transitionRecord] at resolved
    · cases resolved
      cases after
      exact ⟨_, rfl, rfl⟩
    · cases resolved
      cases after
      exact ⟨_, rfl, rfl⟩
  · intro left right leftRecord rightRecord leftResolved rightResolved predecessors
    cases left <;> cases right <;> simp [base, transitionRecord] at leftResolved rightResolved
      <;> cases leftResolved <;> cases rightResolved <;> cases predecessors <;> rfl
  · intro left right leftRecord rightRecord leftResolved rightResolved keys generations
    cases left <;> cases right <;> simp [base, bindingRecord] at leftResolved rightResolved
      <;> cases leftResolved <;> cases rightResolved <;> cases keys <;> cases generations <;> rfl
  · intro binding member
    cases binding
    · left
      constructor
      · exact ⟨.inherited, ⟨_, rfl, rfl⟩, by
          intro other introduced
          rcases introduced with ⟨record, resolved, initial⟩
          cases other
          · cases resolved; cases initial; rfl
          · cases resolved; cases initial
          · cases resolved⟩
      · intro transitionUnique
        rcases transitionUnique with ⟨transition, introduced, _⟩
        rcases introduced with ⟨record, resolved, after⟩
        cases transition <;> simp [base, transitionRecord] at resolved
        · cases resolved; cases after
        · cases resolved; cases after
    · right
      constructor
      · exact ⟨.rebind, ⟨_, rfl, rfl⟩, by
          intro other introduced
          rcases introduced with ⟨record, resolved, after⟩
          cases other <;> simp [base, transitionRecord] at resolved
          · cases resolved; cases after; rfl
          · cases resolved; cases after⟩
      · intro rootUnique
        rcases rootUnique with ⟨root, introduced, _⟩
        rcases introduced with ⟨record, resolved, initial⟩
        cases root <;> simp [base, rootRecord] at resolved
        · cases resolved; cases initial
        · cases resolved; cases initial
    · right
      constructor
      · exact ⟨.bind, ⟨_, rfl, rfl⟩, by
          intro other introduced
          rcases introduced with ⟨record, resolved, after⟩
          cases other <;> simp [base, transitionRecord] at resolved
          · cases resolved; cases after
          · cases resolved; cases after; rfl⟩
      · intro rootUnique
        rcases rootUnique with ⟨root, introduced, _⟩
        rcases introduced with ⟨record, resolved, initial⟩
        cases root <;> simp [base, rootRecord] at resolved
        · cases resolved; cases initial
        · cases resolved; cases initial
  · intro capture record resolved
    cases capture <;> simp [base, captureRecord] at resolved
    cases resolved; exact List.Mem.head _
  · intro capture record resolved
    cases capture <;> simp [base, captureRecord] at resolved
    cases resolved; exact List.Mem.head _
  · intro capture record resolved
    cases capture <;> simp [base, captureRecord] at resolved
    cases resolved
    exact ⟨.inherited, .inherited0, ⟨_, rfl, rfl, rfl⟩⟩
  · intro use record resolved
    cases use <;> simp [base, useRecord] at resolved
    cases resolved; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · intro use record resolved
    cases use <;> simp [base, useRecord] at resolved
    cases resolved
    exact ⟨_, rfl⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem positive_fixture_inhabits_both_structures :
    execution.WellFormed ∧ base.WellFormed execution :=
  ⟨execution_wellFormed, base_wellFormed⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem captured_old_binding_survives_rebind :
    ∃ capture,
      base.captureRecord Capture.old = some capture ∧
      base.FrontierResolves capture.frontier Key.inherited (some Binding.inherited0) ∧
      base.transitionRecord Transition.rebind =
        some ⟨.rebind, .inherited, .root .inherited, 1, some .inherited1⟩ ∧
      base.useRecord Use.old = some ⟨.use, .old⟩ := by
  exact ⟨_, rfl, ⟨_, rfl, rfl, rfl⟩, rfl, rfl⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem captured_use_cannot_redirect_to_rebound_binding :
    ¬ base.Uses .old .inherited1 := by
  rintro ⟨use, useResolved, capture, key, captureResolved, frontierResolved⟩
  cases useResolved
  cases captureResolved
  rcases frontierResolved with ⟨root, rootResolved, keyResolved, stateResolved⟩
  cases rootResolved
  cases keyResolved
  cases stateResolved

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem distinct_keys_may_store_equal_backing_data :
    ∃ inherited fresh,
      base.bindingRecord .inherited0 = some inherited ∧
      base.bindingRecord .fresh0 = some fresh ∧
      inherited.key ≠ fresh.key ∧
      inherited.backingFootprint = fresh.backingFootprint := by
  refine ⟨_, _, rfl, rfl, ?_, rfl⟩
  intro equal
  cases equal

private def duplicateRootId : History envelopeDomains domains :=
  { base with roots := [.inherited, .inherited, .fresh] }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem duplicate_root_id_rejected : ¬ duplicateRootId.WellFormed execution := by
  intro wf
  cases wf.roots_nodup with
  | cons notEqual _ =>
      exact (notEqual .inherited (List.Mem.head _)) rfl

private def distinctRootsSameKey : History envelopeDomains domains :=
  { base with
    roots := [.inherited, .fresh, .duplicate]
    rootRecord := fun
      | .duplicate => some ⟨.inherited, none⟩
      | root => rootRecord root }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem distinct_roots_same_key_rejected :
    ¬ distinctRootsSameKey.WellFormed execution := by
  intro wf
  have equal := wf.root_key_unique
    (left := Root.inherited) (right := Root.duplicate)
    (leftRecord := (⟨.inherited, some .inherited0⟩ : RootRecord domains))
    (rightRecord := (⟨.inherited, none⟩ : RootRecord domains))
    (by rfl) (by rfl) rfl
  cases equal

private def sameKeyGeneration : History envelopeDomains domains :=
  { base with bindingRecord := fun
      | .inherited1 =>
          some ⟨.inherited, .zero, .storage, .readWrite, .inherited, .shared⟩
      | binding => bindingRecord binding }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem distinct_bindings_same_key_generation_rejected :
    ¬ sameKeyGeneration.WellFormed execution := by
  intro wf
  have equal := wf.binding_key_generation_unique
    (left := Binding.inherited0) (right := Binding.inherited1)
    (leftRecord := (⟨.inherited, .zero, .storage, .readWrite, .inherited, .shared⟩ :
      BindingRecord domains))
    (rightRecord := (⟨.inherited, .zero, .storage, .readWrite, .inherited, .shared⟩ :
      BindingRecord domains))
    (by rfl) (by rfl) rfl rfl
  cases equal

private def listedTransitionWithoutRecord : History envelopeDomains domains :=
  { base with transitions := [.rebind, .bind, .outside] }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem listed_transition_without_record_rejected :
    ¬ listedTransitionWithoutRecord.WellFormed execution := by
  intro wf
  obtain ⟨record, resolved⟩ :=
    (wf.transition_coverage .outside).1
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  cases resolved

private def offCarrierTransitionRecord : History envelopeDomains domains :=
  { base with transitionRecord := fun
      | .outside => some ⟨.bind, .fresh, .root .fresh, 1, some .fresh0⟩
      | transition => transitionRecord transition }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem off_carrier_transition_record_rejected :
    ¬ offCarrierTransitionRecord.WellFormed execution := by
  intro wf
  have member := (wf.transition_coverage .outside).2
    ⟨(⟨.bind, .fresh, .root .fresh, 1, some .fresh0⟩ :
      TransitionRecord envelopeDomains domains), rfl⟩
  exact transition_outside_not_mem member

private def noopTransition : History envelopeDomains domains :=
  { base with transitionRecord := fun
      | .rebind => some ⟨.rebind, .inherited, .root .inherited, 1, some .inherited0⟩
      | transition => transitionRecord transition }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem noop_transition_rejected : ¬ noopTransition.WellFormed execution := by
  intro wf
  obtain ⟨before, resolved, changed⟩ := wf.transition_predecessor
    (transition := Transition.rebind)
    (record := (⟨.rebind, .inherited, .root .inherited, 1, some .inherited0⟩ :
      TransitionRecord envelopeDomains domains)) (by rfl)
  rcases resolved with ⟨root, rootResolved, key, state⟩
  cases rootResolved
  cases key
  cases state
  exact changed rfl

private def mismatchedKey : History envelopeDomains domains :=
  { base with transitionRecord := fun
      | .rebind => some ⟨.rebind, .fresh, .root .inherited, 1, some .fresh0⟩
      | transition => transitionRecord transition }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem mismatched_predecessor_key_rejected : ¬ mismatchedKey.WellFormed execution := by
  intro wf
  obtain ⟨before, resolved, _⟩ := wf.transition_predecessor
    (transition := Transition.rebind)
    (record := (⟨.rebind, .fresh, .root .inherited, 1, some .fresh0⟩ :
      TransitionRecord envelopeDomains domains)) (by rfl)
  rcases resolved with ⟨root, rootResolved, key, _⟩
  cases rootResolved
  cases key

private def captureUnboundRoot : History envelopeDomains domains :=
  { base with captureRecord := fun
      | .old => some ⟨.capture, .shared, .root .fresh⟩
      | .outside => none }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem capture_unbound_root_rejected : ¬ captureUnboundRoot.WellFormed execution := by
  intro wf
  obtain ⟨key, binding, resolved⟩ := wf.capture_frontier_bound
    (capture := Capture.old)
    (record := (⟨.capture, .shared, .root .fresh⟩ :
      CaptureRecord envelopeDomains domains)) (by rfl)
  rcases resolved with ⟨root, rootResolved, _, state⟩
  cases rootResolved
  cases state

private def missingCaptureForUse : History envelopeDomains domains :=
  { base with useRecord := fun
      | .old => some ⟨.use, .outside⟩
      | .outside => none }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem missing_capture_for_use_rejected : ¬ missingCaptureForUse.WellFormed execution := by
  intro wf
  obtain ⟨capture, resolved⟩ := wf.use_capture_resolves
    (use := Use.old)
    (record := (⟨.use, .outside⟩ : UseRecord envelopeDomains domains)) (by rfl)
  cases resolved

private def forkedPredecessor : History envelopeDomains domains :=
  { base with
    transitions := [.rebind, .bind, .fork]
    transitionRecord := fun
      | .fork => some ⟨.rebind, .inherited, .root .inherited, 2, none⟩
      | transition => transitionRecord transition }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem forked_predecessor_rejected : ¬ forkedPredecessor.WellFormed execution := by
  intro wf
  have equal := wf.successor_unique
    (left := Transition.rebind) (right := Transition.fork)
    (leftRecord := (⟨.rebind, .inherited, .root .inherited, 1, some .inherited1⟩ :
      TransitionRecord envelopeDomains domains))
    (rightRecord := (⟨.rebind, .inherited, .root .inherited, 2, none⟩ :
      TransitionRecord envelopeDomains domains)) (by rfl) (by rfl) rfl
  cases equal

private def nondecreasingRank : History envelopeDomains domains :=
  { base with
    transitions := [.rebind, .bind, .later]
    transitionRecord := fun
      | .later => some ⟨.use, .inherited, .transition .rebind, 1, none⟩
      | transition => transitionRecord transition }

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem nondecreasing_rank_rejected : ¬ nondecreasingRank.WellFormed execution := by
  intro wf
  have less := wf.transition_rank_decreases
    (transition := Transition.later)
    (record := (⟨.use, .inherited, .transition .rebind, 1, none⟩ :
      TransitionRecord envelopeDomains domains))
    (predecessor := Transition.rebind)
    (predecessorRecord := (⟨.rebind, .inherited, .root .inherited, 1,
      some .inherited1⟩ : TransitionRecord envelopeDomains domains))
    (by rfl) rfl (by rfl)
  exact Nat.lt_irrefl 1 less

private def rebindBack : History envelopeDomains domains :=
  { base with
    transitions := [.rebind, .bind, .later]
    transitionRecord := fun
      | .later => some ⟨.use, .inherited, .transition .rebind, 2, some .inherited0⟩
      | transition => transitionRecord transition }

private theorem root_introduces_inherited0_in_rebindBack :
    rebindBack.RootIntroduces .inherited0 .inherited := ⟨_, rfl, rfl⟩

private theorem later_introduces_inherited0_in_rebindBack :
    rebindBack.TransitionIntroduces .inherited0 .later := ⟨_, rfl, rfl⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem rebind_back_to_old_instance_rejected : ¬ rebindBack.WellFormed execution := by
  intro wf
  have introduction := wf.binding_introduction
    (binding := Binding.inherited0) (List.Mem.head _)
  rcases introduction with ⟨_, noTransition⟩ | ⟨_, noRoot⟩
  · apply noTransition
    refine ⟨.later, later_introduces_inherited0_in_rebindBack, ?_⟩
    intro other introduced
    cases other <;> rcases introduced with ⟨record, resolved, after⟩
    · cases resolved; cases after
    · cases resolved; cases after
    · cases resolved
    · cases resolved; cases after; rfl
    · cases resolved
  · apply noRoot
    refine ⟨.inherited, root_introduces_inherited0_in_rebindBack, ?_⟩
    intro other introduced
    cases other <;> rcases introduced with ⟨record, resolved, initial⟩
    · cases resolved; cases initial; rfl
    · cases resolved; cases initial
    · cases resolved

private def twoTransitionReuse : History envelopeDomains domains :=
  { base with
    transitions := [.rebind, .bind, .later]
    transitionRecord := fun
      | .later => some ⟨.use, .inherited, .transition .rebind, 2, some .inherited1⟩
      | transition => transitionRecord transition }

private theorem first_transition_introduces_inherited1_twice :
    twoTransitionReuse.TransitionIntroduces .inherited1 .rebind := ⟨_, rfl, rfl⟩

private theorem later_transition_introduces_inherited1_twice :
    twoTransitionReuse.TransitionIntroduces .inherited1 .later := ⟨_, rfl, rfl⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem two_transitions_same_after_instance_rejected :
    ¬ twoTransitionReuse.WellFormed execution := by
  intro wf
  have introduction := wf.binding_introduction
    (binding := Binding.inherited1) (List.Mem.tail _ (List.Mem.head _))
  rcases introduction with ⟨rootUnique, _⟩ | ⟨transitionUnique, _⟩
  · rcases rootUnique with ⟨root, introduced, _⟩
    rcases introduced with ⟨record, resolved, initial⟩
    cases root <;> cases resolved <;> cases initial
  · rcases transitionUnique with ⟨site, _, unique⟩
    have first := unique .rebind first_transition_introduces_inherited1_twice
    have later := unique .later later_transition_introduces_inherited1_twice
    subst site
    cases later

private def unbindThenReintroduce : History envelopeDomains domains :=
  { base with
    transitions := [.rebind, .bind, .later]
    transitionRecord := fun
      | .rebind => some ⟨.rebind, .inherited, .root .inherited, 1, none⟩
      | .later => some ⟨.use, .inherited, .transition .rebind, 2, some .inherited0⟩
      | transition => transitionRecord transition }

private theorem root_introduces_inherited0_after_unbind :
    unbindThenReintroduce.RootIntroduces .inherited0 .inherited := ⟨_, rfl, rfl⟩

private theorem later_reintroduces_inherited0_after_unbind :
    unbindThenReintroduce.TransitionIntroduces .inherited0 .later := ⟨_, rfl, rfl⟩

/- REF: docs/MEMORY_MODEL.md#4-common-dynamic-memory-event-vocabulary -/
private theorem unbind_then_old_instance_reintroduced_rejected :
    ¬ unbindThenReintroduce.WellFormed execution := by
  intro wf
  have introduction := wf.binding_introduction
    (binding := Binding.inherited0) (List.Mem.head _)
  rcases introduction with ⟨_, noTransition⟩ | ⟨_, noRoot⟩
  · apply noTransition
    refine ⟨.later, later_reintroduces_inherited0_after_unbind, ?_⟩
    intro other introduced
    cases other <;> rcases introduced with ⟨record, resolved, after⟩
    · cases resolved; cases after
    · cases resolved; cases after
    · cases resolved
    · cases resolved; cases after; rfl
    · cases resolved
  · apply noRoot
    refine ⟨.inherited, root_introduces_inherited0_after_unbind, ?_⟩
    intro other introduced
    cases other <;> rcases introduced with ⟨record, resolved, initial⟩
    · cases resolved; cases initial; rfl
    · cases resolved; cases initial
    · cases resolved

end Gasm.MemoryModel.BindingHistory.Controls

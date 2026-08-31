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
import Gasm.MemoryModel.EnvelopeOccurrencePath
import Gasm.MemoryModel.ObligationWorld
import Spikes.CheckedMemoryWindows.Program

/-!
Profile-local logical authority for the checked Windows byte-store demonstration. The nominal
envelope, binding history, latest-live path, and obligation world are deliberately instantiated
here rather than hidden behind a detached `AuthorizedAccess` proposition. This remains a
provisional M1 profile: only its later composition with the exact Windows entry grant, production
execution, and `VerifiedProgram` can admit the artifact.
-/

namespace Spikes.CheckedMemoryWindows.Authority

open Gasm.MemoryModel
open Gasm.MemoryModel.BindingHistory
open Gasm.MemoryModel.Envelope
open Gasm.MemoryModel.EnvelopeOccurrencePath
open Gasm.MemoryModel.ObligationWorld
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.StackStorePrefix

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Agent where | main
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Reference where | stackByteView
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Location where | stackFrame | selectedByte
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Event where | capture | store
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive EventPayload where
  | captureBinding (rip address : UInt64)
  | executeStore (rip address : UInt64) (value : UInt8)
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive RelationOccurrence where | captureToStore
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive RelationLabel where | programOrder
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ConsequenceOccurrence
  deriving DecidableEq
/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Consequence
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def envelopeDomains : Envelope.Domains where
  AgentId := Agent
  ReferenceId := Reference
  Location := Location
  EventId := Event
  EventPayload := EventPayload
  RelationOccurrenceId := RelationOccurrence
  RelationLabel := RelationLabel
  ConsequenceOccurrenceId := ConsequenceOccurrence
  Consequence := Consequence

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def storeAddress (entry : X86_64MachineState) : UInt64 :=
  entry.rsp - frameSize.toUInt64 + byteOffset.toUInt64

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def execution (entry : X86_64MachineState) : Envelope.Execution envelopeDomains where
  agents := [.main]
  references := [.stackByteView]
  locations := [.stackFrame, .selectedByte]
  events := [.capture, .store]
  event
    | .capture => some ⟨some .main,
        .captureBinding (afterAllocate entry).rip (storeAddress entry)⟩
    | .store => some ⟨some .main,
        .executeStore (afterAllocate entry).rip (storeAddress entry) storedValue⟩
  relationOccurrences := [.captureToStore]
  relationOccurrence
    | .captureToStore => some ⟨.capture, .programOrder, .store⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem execution_wellFormed (entry : X86_64MachineState) :
    (execution entry).WellFormed := by
  refine {
    agents_nodup := by change [Agent.main].Nodup; decide
    references_nodup := by change [Reference.stackByteView].Nodup; decide
    locations_nodup := by change [Location.stackFrame, Location.selectedByte].Nodup; decide
    events_nodup := by change [Event.capture, Event.store].Nodup; decide
    relation_occurrences_nodup := by
      change [RelationOccurrence.captureToStore].Nodup
      decide
    event_coverage := ?_
    event_agent_mem := ?_
    relation_coverage := ?_
    relation_endpoints := ?_ }
  · intro eventId
    cases eventId <;> constructor
    · intro _; exact ⟨_, rfl⟩
    · intro _; change Event.capture ∈ [Event.capture, Event.store]; decide
    · intro _; exact ⟨_, rfl⟩
    · intro _; change Event.store ∈ [Event.capture, Event.store]; decide
  · intro eventId record agent resolved attributed
    cases eventId <;> simp only [execution] at resolved
    all_goals
      cases resolved
      cases agent
      change Agent.main ∈ [Agent.main]
      decide
  · intro occurrence
    cases occurrence
    constructor
    · intro _; exact ⟨_, rfl⟩
    · intro _
      change RelationOccurrence.captureToStore ∈ [RelationOccurrence.captureToStore]
      decide
  · intro occurrence record resolved
    cases occurrence
    simp only [execution] at resolved
    cases resolved
    change Event.capture ∈ [Event.capture, Event.store] ∧
      Event.store ∈ [Event.capture, Event.store]
    decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
structure Footprint where
  start : UInt64
  length : Nat
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ObjectInstance where | entryStack
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive BindingKey where | stack
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
abbrev BindingGeneration := Nat

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive BindingInstance where | entryStack | otherStack
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Rights where | exclusiveWrite | sharedRead
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive RootOccurrence where | processEntry
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive TransitionOccurrence
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive CaptureOccurrence where | afterAllocation
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive UseOccurrence where | selectedStore
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def bindingDomains : BindingHistory.Domains where
  ObjectInstanceId := ObjectInstance
  BindingKey := BindingKey
  BindingGeneration := BindingGeneration
  BindingInstanceId := BindingInstance
  Rights := Rights
  LogicalFootprint := Footprint
  BackingFootprint := Footprint
  RootOccurrenceId := RootOccurrence
  TransitionOccurrenceId := TransitionOccurrence
  CaptureOccurrenceId := CaptureOccurrence
  UseOccurrenceId := UseOccurrence

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
def frameFootprint (entry : X86_64MachineState) : Footprint :=
  ⟨entry.rsp - frameSize.toUInt64, frameSize.toNat⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
def byteFootprint (entry : X86_64MachineState) : Footprint :=
  ⟨storeAddress entry, 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def history (entry : X86_64MachineState) :
    BindingHistory.History envelopeDomains bindingDomains where
  bindingInstances := [.entryStack]
  bindingRecord
    | .entryStack => some {
        key := .stack
        generation := (0 : BindingGeneration)
        object := .entryStack
        rights := .exclusiveWrite
        logicalFootprint := frameFootprint entry
        backingFootprint := frameFootprint entry }
    | .otherStack => none
  roots := [.processEntry]
  rootRecord
    | .processEntry => some { key := .stack, initial := some .entryStack }
  transitions := []
  transitionRecord occurrence := nomatch occurrence
  captures := [.afterAllocation]
  captureRecord
    | .afterAllocation => some {
        event := .capture
        reference := .stackByteView
        frontier := .root .processEntry }
  uses := [.selectedStore]
  useRecord
    | .selectedStore => some { event := .store, capture := .afterAllocation }

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem history_wellFormed (entry : X86_64MachineState) :
    (history entry).WellFormed (execution entry) := by
  refine {
    binding_instances_nodup := by change [BindingInstance.entryStack].Nodup; decide
    roots_nodup := by change [RootOccurrence.processEntry].Nodup; decide
    transitions_nodup := by exact List.nodup_nil
    captures_nodup := by change [CaptureOccurrence.afterAllocation].Nodup; decide
    uses_nodup := by change [UseOccurrence.selectedStore].Nodup; decide
    binding_coverage := ?_
    root_coverage := ?_
    transition_coverage := ?_
    capture_coverage := ?_
    use_coverage := ?_
    root_key_unique := ?_
    root_initial_resolves := ?_
    transition_event_mem := ?_
    transition_predecessor := ?_
    transition_rank_decreases := ?_
    transition_after_resolves := ?_
    successor_unique := ?_
    binding_key_generation_unique := ?_
    binding_introduction := ?_
    capture_event_mem := ?_
    capture_reference_mem := ?_
    capture_frontier_bound := ?_
    use_event_mem := ?_
    use_capture_resolves := ?_ }
  · intro binding
    cases binding with
    | entryStack =>
        constructor
        · intro _; exact ⟨_, rfl⟩
        · intro _
          change BindingInstance.entryStack ∈ [BindingInstance.entryStack]
          decide
    | otherStack =>
        constructor
        · intro member
          have equal : BindingInstance.otherStack = BindingInstance.entryStack :=
            List.mem_singleton.mp member
          cases equal
        · rintro ⟨record, resolved⟩
          simp [history] at resolved
  · intro root
    cases root
    constructor
    · intro _; exact ⟨_, rfl⟩
    · intro _
      change RootOccurrence.processEntry ∈ [RootOccurrence.processEntry]
      decide
  · intro transition
    exact nomatch transition
  · intro capture
    cases capture
    constructor
    · intro _; exact ⟨_, rfl⟩
    · intro _
      change CaptureOccurrence.afterAllocation ∈ [CaptureOccurrence.afterAllocation]
      decide
  · intro use
    cases use
    constructor
    · intro _; exact ⟨_, rfl⟩
    · intro _
      change UseOccurrence.selectedStore ∈ [UseOccurrence.selectedStore]
      decide
  · intro left right leftRecord rightRecord leftResolved rightResolved _
    cases left
    cases right
    rfl
  · intro root rootRecord binding rootResolved initialResolved
    cases root
    cases binding with
    | entryStack =>
        simp only [history] at rootResolved
        cases rootResolved
        exact ⟨_, rfl, rfl⟩
    | otherStack =>
        simp only [history] at rootResolved
        cases rootResolved
        cases initialResolved
  · intro transition
    exact nomatch transition
  · intro transition
    exact nomatch transition
  · intro transition
    exact nomatch transition
  · intro transition
    exact nomatch transition
  · intro left
    exact nomatch left
  · intro left right leftRecord rightRecord leftResolved rightResolved _ _
    cases left <;> cases right <;> simp [history] at leftResolved rightResolved
    rfl
  · intro binding _
    cases binding with
    | entryStack =>
        left
        constructor
        · refine ⟨.processEntry, ?_, ?_⟩
          · exact ⟨_, rfl, rfl⟩
          · intro other selected
            cases other
            rfl
        · intro introduced
          rcases introduced with ⟨site, _⟩
          exact nomatch site
    | otherStack => contradiction
  · intro capture record resolved
    cases capture
    simp only [history] at resolved
    cases resolved
    change Event.capture ∈ [Event.capture, Event.store]
    decide
  · intro capture record resolved
    cases capture
    simp only [history] at resolved
    cases resolved
    change Reference.stackByteView ∈ [Reference.stackByteView]
    decide
  · intro capture record resolved
    cases capture
    simp only [history] at resolved
    cases resolved
    exact ⟨.stack, .entryStack, _, rfl, rfl, rfl⟩
  · intro use record resolved
    cases use
    simp only [history] at resolved
    cases resolved
    change Event.store ∈ [Event.capture, Event.store]
    decide
  · intro use record resolved
    cases use
    simp only [history] at resolved
    cases resolved
    exact ⟨_, rfl⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem capture_to_store_path (entry : X86_64MachineState) :
    OccurrencePath (execution entry) .capture .store
      [.captureToStore] [.programOrder] := by
  exact .single ⟨by
    change RelationOccurrence.captureToStore ∈ [RelationOccurrence.captureToStore]
    decide, rfl⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ObligationKind where
  | exclusiveStore (binding : BindingInstance) (generation : BindingGeneration)
      (footprint : Footprint)
  | invalidateView (binding : BindingInstance) (generation : BindingGeneration)
      (capture : CaptureOccurrence)
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ObligationId where | access | invalidate
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def accessEntry (entry : X86_64MachineState) : Entry ObligationId ObligationKind :=
  ⟨.access, .exclusiveStore .entryStack 0 (byteFootprint entry)⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def invalidateEntry : Entry ObligationId ObligationKind :=
  ⟨.invalidate, .invalidateView .entryStack 0 .afterAllocation⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def entryWorld (entry : X86_64MachineState) : World ObligationId ObligationKind :=
  ⟨[accessEntry entry, invalidateEntry], by
    simp [accessEntry, invalidateEntry]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
/-- Exact logical proof carried by the checked store. The empty transition carrier establishes
    that the inherited root remains latest and live from capture through the exact use path. -/
structure TypedStoreView (entry : X86_64MachineState) : Prop where
  private mk ::
  envelopeWellFormed : (execution entry).WellFormed
  historyWellFormed : (history entry).WellFormed (execution entry)
  noRebindOrInvalidation : (history entry).transitions = []
  captureResolves : (history entry).Captures .afterAllocation .entryStack
  useResolves : (history entry).Uses .selectedStore .entryStack
  exactPath : OccurrencePath (execution entry) .capture .store
    [.captureToStore] [.programOrder]
  accessOwned : (entryWorld entry).Binds
    (accessEntry entry).id (accessEntry entry).payload
  invalidationOwned : (entryWorld entry).Binds
    invalidateEntry.id invalidateEntry.payload

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem typedStoreView : TypedStoreView entryState where
  envelopeWellFormed := execution_wellFormed entryState
  historyWellFormed := history_wellFormed entryState
  noRebindOrInvalidation := rfl
  captureResolves := by
    refine ⟨_, .stack, rfl, ?_⟩
    exact ⟨_, rfl, rfl, rfl⟩
  useResolves := by
    refine ⟨_, rfl, _, .stack, rfl, ?_⟩
    exact ⟨_, rfl, rfl, rfl⟩
  exactPath := capture_to_store_path entryState
  accessOwned := by simp [World.Binds, entryWorld]
  invalidationOwned := by simp [World.Binds, entryWorld]

end Spikes.CheckedMemoryWindows.Authority

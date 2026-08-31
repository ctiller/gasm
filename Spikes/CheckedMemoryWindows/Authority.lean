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
import Gasm.Targets.Windows.ProcessEntryMemory
import Spikes.CheckedMemoryWindows.Program

/-!
Invocation-scoped structural authority for the checked Windows byte-store demonstration.

The target-owned process-entry transition issues `invocation`; binding generations, captures,
uses, lifecycle occurrence, and obligation identities all carry that exact invocation. The entry
obligation world is constructed only through two explicit `ObligationWorld.Issuance` steps.

This module deliberately stops at structural correlation. `StructuralStoreAuthority` does not
claim that the capture is live/latest or that an x86 transition performed the store. The concrete
production-use refinement and target mapping grant are supplied in `Realization` and only their
composition may authorize checked instruction erasure.
-/

namespace Spikes.CheckedMemoryWindows.Authority

open Gasm.MemoryModel
open Gasm.MemoryModel.AddressRange
open Gasm.MemoryModel.BindingHistory
open Gasm.MemoryModel.Envelope
open Gasm.MemoryModel.EnvelopeOccurrencePath
open Gasm.MemoryModel.ObligationWorld
open Gasm.Targets.Windows.ProcessEntryMemory
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.StackStorePrefix
open Spikes.CheckedMemoryWindows

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def initialInvocationWorld : InvocationWorld := InvocationWorld.empty

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def processEntryLoad : ProcessEntryLoad executable initialInvocationWorld :=
  loadProcessEntry executable initialInvocationWorld

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def invocation : InvocationId := processEntryLoad.invocation

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
inductive Event where | capture | store | terminal
  deriving DecidableEq


/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive EventPayload where
  | captureBinding (invocation : InvocationId) (rip address : UInt64)
  | executeStore (invocation : InvocationId) (rip address : UInt64) (value : UInt8)
  | processExit (invocation : InvocationId) (code : UInt32)
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive RelationOccurrence where | captureToStore | storeToTerminal
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive RelationLabel where | programOrder | lifecycle
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ConsequenceOccurrence
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Consequence
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
abbrev envelopeDomains : Envelope.Domains where
  AgentId := Agent
  ReferenceId := Reference
  Location := Location
  EventId := Event
  EventPayload := EventPayload
  RelationOccurrenceId := RelationOccurrence
  RelationLabel := RelationLabel
  ConsequenceOccurrenceId := ConsequenceOccurrence
  Consequence := Consequence

/- Domain projections are intentionally abstract to generic envelope consumers.  This concrete
   spike nevertheless has finite, decidable identifiers; expose those instances explicitly so
   coverage proofs do not depend on reducibility of the `envelopeDomains` definition. -/
local instance : DecidableEq envelopeDomains.AgentId := by
  change DecidableEq Agent
  infer_instance

local instance : DecidableEq envelopeDomains.ReferenceId := by
  change DecidableEq Reference
  infer_instance

local instance : DecidableEq envelopeDomains.Location := by
  change DecidableEq Location
  infer_instance

local instance : DecidableEq envelopeDomains.EventId := by
  change DecidableEq Event
  infer_instance

local instance : DecidableEq envelopeDomains.RelationOccurrenceId := by
  change DecidableEq RelationOccurrence
  infer_instance

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def storeAddress (entry : X86_64MachineState) : UInt64 :=
  entry.rsp - frameSize.toUInt64 + byteOffset.toUInt64

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
def frameRange (entry : X86_64MachineState) : AddressRange :=
  ⟨entry.rsp - frameSize.toUInt64, frameSize.toNat⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
def byteRange (entry : X86_64MachineState) : AddressRange :=
  ⟨storeAddress entry, 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def execution (entry : X86_64MachineState) : Envelope.Execution envelopeDomains where
  agents := [.main]
  references := [.stackByteView]
  locations := [.stackFrame, .selectedByte]
  events := [.capture, .store, .terminal]
  event
    | .capture => some ⟨some .main,
        .captureBinding invocation (afterAllocate entry).rip (storeAddress entry)⟩
    | .store => some ⟨some .main,
        .executeStore invocation (afterAllocate entry).rip (storeAddress entry) storedValue⟩
    | .terminal => some ⟨some .main, .processExit invocation 0⟩
  relationOccurrences := [.captureToStore, .storeToTerminal]
  relationOccurrence
    | .captureToStore => some ⟨.capture, .programOrder, .store⟩
    | .storeToTerminal => some ⟨.store, .lifecycle, .terminal⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem execution_wellFormed (entry : X86_64MachineState) :
    (execution entry).WellFormed := by
  refine {
    agents_nodup := by change [Agent.main].Nodup; decide
    references_nodup := by change [Reference.stackByteView].Nodup; decide
    locations_nodup := by change [Location.stackFrame, Location.selectedByte].Nodup; decide
    events_nodup := by change [Event.capture, Event.store, Event.terminal].Nodup; decide
    relation_occurrences_nodup := by
      change [RelationOccurrence.captureToStore, RelationOccurrence.storeToTerminal].Nodup
      decide
    event_coverage := ?_
    event_agent_mem := ?_
    relation_coverage := ?_
    relation_endpoints := ?_ }
  · intro eventId
    cases eventId
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · intro eventId record agent resolved attributed
    cases eventId <;> simp only [execution] at resolved <;> cases resolved <;>
      cases attributed <;> cases agent <;> change Agent.main ∈ [Agent.main] <;> decide
  · intro occurrence
    cases occurrence
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro _; exact ⟨_, rfl⟩
      · intro _; exact List.Mem.tail _ (List.Mem.head _)
  · intro occurrence record resolved
    cases occurrence <;> simp only [execution] at resolved <;> cases resolved
    · constructor
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ObjectInstance where | entryStack
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive BindingKey where | stack
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure BindingGeneration where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure BindingInstance where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr


/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive Rights where | exclusiveWrite | sharedRead
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure RootOccurrence where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure TransitionOccurrence where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure CaptureOccurrence where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure UseOccurrence where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure LifecycleOccurrence where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def entryBinding (selected : InvocationId) : BindingInstance := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def entryGeneration (selected : InvocationId) : BindingGeneration := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def entryRoot (selected : InvocationId) : RootOccurrence := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def storeCapture (selected : InvocationId) : CaptureOccurrence := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def storeUse (selected : InvocationId) : UseOccurrence := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def rootTerminal (selected : InvocationId) : LifecycleOccurrence := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
abbrev bindingDomains : BindingHistory.Domains where
  ObjectInstanceId := ObjectInstance
  BindingKey := BindingKey
  BindingGeneration := BindingGeneration
  BindingInstanceId := BindingInstance
  Rights := Rights
  LogicalFootprint := AddressRange
  BackingFootprint := AddressRange
  RootOccurrenceId := RootOccurrence
  TransitionOccurrenceId := TransitionOccurrence
  CaptureOccurrenceId := CaptureOccurrence
  UseOccurrenceId := UseOccurrence

/- As above, make the concrete finite key equality visible through the generic history-domain
   projections.  These are computational derived instances, not classical equality or axioms. -/
local instance : DecidableEq bindingDomains.BindingInstanceId := by
  change DecidableEq BindingInstance
  infer_instance

local instance : DecidableEq bindingDomains.RootOccurrenceId := by
  change DecidableEq RootOccurrence
  infer_instance

local instance : DecidableEq bindingDomains.TransitionOccurrenceId := by
  change DecidableEq TransitionOccurrence
  infer_instance

local instance : DecidableEq bindingDomains.CaptureOccurrenceId := by
  change DecidableEq CaptureOccurrence
  infer_instance

local instance : DecidableEq bindingDomains.UseOccurrenceId := by
  change DecidableEq UseOccurrence
  infer_instance

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def entryBindingRecord (entry : X86_64MachineState) : BindingRecord bindingDomains := {
  key := .stack
  generation := entryGeneration invocation
  object := .entryStack
  rights := .exclusiveWrite
  logicalFootprint := frameRange entry
  backingFootprint := frameRange entry }

def entryRootRecord : RootRecord bindingDomains :=
  { key := .stack, initial := some (entryBinding invocation) }

def storeCaptureRecord : CaptureRecord envelopeDomains bindingDomains :=
  { event := .capture
    reference := .stackByteView
    frontier := .root (entryRoot invocation) }

def storeUseRecord : UseRecord envelopeDomains bindingDomains :=
  { event := .store, capture := storeCapture invocation }

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def history (entry : X86_64MachineState) :
    BindingHistory.History envelopeDomains bindingDomains where
  bindingInstances := [entryBinding invocation]
  bindingRecord binding :=
    letI : Decidable (binding = entryBinding invocation) :=
      instDecidableEqBindingInstance binding (entryBinding invocation)
    if binding = entryBinding invocation then some (entryBindingRecord entry) else none
  roots := [entryRoot invocation]
  rootRecord root :=
    letI : Decidable (root = entryRoot invocation) :=
      instDecidableEqRootOccurrence root (entryRoot invocation)
    if root = entryRoot invocation then some entryRootRecord else none
  transitions := []
  transitionRecord _ := none
  captures := [storeCapture invocation]
  captureRecord capture :=
    letI : Decidable (capture = storeCapture invocation) :=
      instDecidableEqCaptureOccurrence capture (storeCapture invocation)
    if capture = storeCapture invocation then some storeCaptureRecord else none
  uses := [storeUse invocation]
  useRecord use :=
    letI : Decidable (use = storeUse invocation) :=
      instDecidableEqUseOccurrence use (storeUse invocation)
    if use = storeUse invocation then some storeUseRecord else none

@[simp] theorem history_bindingRecord_entry (entry : X86_64MachineState) :
    (history entry).bindingRecord (entryBinding invocation) = some (entryBindingRecord entry) := by
  simp only [history]
  simp only [if_true]

theorem history_bindingRecord_ne (entry : X86_64MachineState) {binding : BindingInstance}
    (different : binding ≠ entryBinding invocation) :
    (history entry).bindingRecord binding = none := by
  simp only [history]
  rw [if_neg different]

@[simp] theorem history_rootRecord_entry (entry : X86_64MachineState) :
    (history entry).rootRecord (entryRoot invocation) = some entryRootRecord := by
  simp only [history]
  simp only [if_true]

theorem history_rootRecord_ne (entry : X86_64MachineState) {root : RootOccurrence}
    (different : root ≠ entryRoot invocation) :
    (history entry).rootRecord root = none := by
  simp only [history]
  rw [if_neg different]

@[simp] theorem history_captureRecord_store (entry : X86_64MachineState) :
    (history entry).captureRecord (storeCapture invocation) = some storeCaptureRecord := by
  simp only [history]
  simp only [if_true]

theorem history_captureRecord_ne (entry : X86_64MachineState) {capture : CaptureOccurrence}
    (different : capture ≠ storeCapture invocation) :
    (history entry).captureRecord capture = none := by
  simp only [history]
  rw [if_neg different]

@[simp] theorem history_useRecord_store (entry : X86_64MachineState) :
    (history entry).useRecord (storeUse invocation) = some storeUseRecord := by
  simp only [history]
  simp only [if_true]

theorem history_useRecord_ne (entry : X86_64MachineState) {use : UseOccurrence}
    (different : use ≠ storeUse invocation) :
    (history entry).useRecord use = none := by
  simp only [history]
  rw [if_neg different]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem history_wellFormed (entry : X86_64MachineState) :
    (history entry).WellFormed (execution entry) := by
  refine {
    binding_instances_nodup := by
      exact List.nodup_cons.mpr ⟨by intro impossible; contradiction, List.nodup_nil⟩
    roots_nodup := by
      exact List.nodup_cons.mpr ⟨by intro impossible; contradiction, List.nodup_nil⟩
    transitions_nodup := List.nodup_nil
    captures_nodup := by
      exact List.nodup_cons.mpr ⟨by intro impossible; contradiction, List.nodup_nil⟩
    uses_nodup := by
      exact List.nodup_cons.mpr ⟨by intro impossible; contradiction, List.nodup_nil⟩
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
    by_cases equal : binding = entryBinding invocation
    · subst binding
      constructor
      · intro _; exact ⟨_, history_bindingRecord_entry entry⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro member
        change binding ∈ [entryBinding invocation] at member
        exact (equal (List.mem_singleton.mp member)).elim
      · rintro ⟨record, resolved⟩
        rw [history_bindingRecord_ne entry equal] at resolved
        contradiction
  · intro root
    by_cases equal : root = entryRoot invocation
    · subst root
      constructor
      · intro _; exact ⟨_, history_rootRecord_entry entry⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro member
        change root ∈ [entryRoot invocation] at member
        exact (equal (List.mem_singleton.mp member)).elim
      · rintro ⟨record, resolved⟩
        rw [history_rootRecord_ne entry equal] at resolved
        contradiction
  · intro transition
    constructor
    · intro member; change transition ∈ [] at member; contradiction
    · rintro ⟨record, resolved⟩; change none = some record at resolved; contradiction
  · intro capture
    by_cases equal : capture = storeCapture invocation
    · subst capture
      constructor
      · intro _; exact ⟨_, history_captureRecord_store entry⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro member
        change capture ∈ [storeCapture invocation] at member
        exact (equal (List.mem_singleton.mp member)).elim
      · rintro ⟨record, resolved⟩
        rw [history_captureRecord_ne entry equal] at resolved
        contradiction
  · intro use
    by_cases equal : use = storeUse invocation
    · subst use
      constructor
      · intro _; exact ⟨_, history_useRecord_store entry⟩
      · intro _; exact List.Mem.head _
    · constructor
      · intro member
        change use ∈ [storeUse invocation] at member
        exact (equal (List.mem_singleton.mp member)).elim
      · rintro ⟨record, resolved⟩
        rw [history_useRecord_ne entry equal] at resolved
        contradiction
  · intro left right leftRecord rightRecord leftResolved rightResolved _
    have leftEq : left = entryRoot invocation := by
      by_cases equal : left = entryRoot invocation
      · exact equal
      · rw [history_rootRecord_ne entry equal] at leftResolved
        contradiction
    have rightEq : right = entryRoot invocation := by
      by_cases equal : right = entryRoot invocation
      · exact equal
      · rw [history_rootRecord_ne entry equal] at rightResolved
        contradiction
    exact leftEq.trans rightEq.symm
  · intro root rootRecord binding rootResolved initialResolved
    have rootEq : root = entryRoot invocation := by
      by_cases equal : root = entryRoot invocation
      · exact equal
      · rw [history_rootRecord_ne entry equal] at rootResolved
        contradiction
    subst root
    rw [history_rootRecord_entry entry] at rootResolved
    cases rootResolved
    change (some (entryBinding invocation) : Option BindingInstance) = some binding at initialResolved
    cases initialResolved
    exact ⟨entryBindingRecord entry, history_bindingRecord_entry entry, rfl⟩
  · intro transition record resolved
    change none = some record at resolved
    contradiction
  · intro transition record resolved
    change none = some record at resolved
    contradiction
  · intro transition record predecessor predecessorRecord resolved
    change none = some record at resolved
    contradiction
  · intro transition transitionRecord binding resolved
    change none = some transitionRecord at resolved
    contradiction
  · intro left right leftRecord rightRecord leftResolved
    change none = some leftRecord at leftResolved
    contradiction
  · intro left right leftRecord rightRecord leftResolved rightResolved _ _
    have leftEq : left = entryBinding invocation := by
      by_cases equal : left = entryBinding invocation
      · exact equal
      · rw [history_bindingRecord_ne entry equal] at leftResolved
        contradiction
    have rightEq : right = entryBinding invocation := by
      by_cases equal : right = entryBinding invocation
      · exact equal
      · rw [history_bindingRecord_ne entry equal] at rightResolved
        contradiction
    exact leftEq.trans rightEq.symm
  · intro binding member
    change binding ∈ [entryBinding invocation] at member
    have equal : binding = entryBinding invocation := List.mem_singleton.mp member
    subst binding
    left
    constructor
    · refine ⟨entryRoot invocation, ?_, ?_⟩
      · exact ⟨entryRootRecord, history_rootRecord_entry entry, rfl⟩
      · intro other introduced
        rcases introduced with ⟨record, resolved, _⟩
        by_cases equal : other = entryRoot invocation
        · exact equal
        · rw [history_rootRecord_ne entry equal] at resolved
          contradiction
    · intro introduced
      rcases introduced with ⟨site, selected, _⟩
      rcases selected with ⟨record, resolved, _⟩
      change none = some record at resolved
      contradiction
  · intro capture record resolved
    have captureEq : capture = storeCapture invocation := by
      by_cases equal : capture = storeCapture invocation
      · exact equal
      · rw [history_captureRecord_ne entry equal] at resolved
        contradiction
    subst capture
    rw [history_captureRecord_store entry] at resolved
    cases resolved
    exact List.Mem.head _
  · intro capture record resolved
    have captureEq : capture = storeCapture invocation := by
      by_cases equal : capture = storeCapture invocation
      · exact equal
      · rw [history_captureRecord_ne entry equal] at resolved
        contradiction
    subst capture
    rw [history_captureRecord_store entry] at resolved
    cases resolved
    exact List.Mem.head _
  · intro capture record resolved
    have captureEq : capture = storeCapture invocation := by
      by_cases equal : capture = storeCapture invocation
      · exact equal
      · rw [history_captureRecord_ne entry equal] at resolved
        contradiction
    subst capture
    rw [history_captureRecord_store entry] at resolved
    cases resolved
    exact ⟨.stack, entryBinding invocation, entryRootRecord,
      history_rootRecord_entry entry, rfl, rfl⟩
  · intro use record resolved
    have useEq : use = storeUse invocation := by
      by_cases equal : use = storeUse invocation
      · exact equal
      · rw [history_useRecord_ne entry equal] at resolved
        contradiction
    subst use
    rw [history_useRecord_store entry] at resolved
    cases resolved
    exact List.Mem.tail _ (List.Mem.head _)
  · intro use record resolved
    have useEq : use = storeUse invocation := by
      by_cases equal : use = storeUse invocation
      · exact equal
      · rw [history_useRecord_ne entry equal] at resolved
        contradiction
    subst use
    rw [history_useRecord_store entry] at resolved
    cases resolved
    exact ⟨storeCaptureRecord, history_captureRecord_store entry⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem capture_to_store_path (entry : X86_64MachineState) :
    OccurrencePath (execution entry) .capture .store
      [.captureToStore] [.programOrder] := by
  exact .single ⟨List.Mem.head _, rfl⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem store_to_terminal_path (entry : X86_64MachineState) :
    OccurrencePath (execution entry) .store .terminal
      [.storeToTerminal] [.lifecycle] := by
  exact .single ⟨List.Mem.tail _ (List.Mem.head _), rfl⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
inductive ObligationKind where
  | exclusiveStore (binding : BindingInstance) (generation : BindingGeneration)
      (footprint : AddressRange)
  | invalidateView (binding : BindingInstance) (generation : BindingGeneration)
      (capture : CaptureOccurrence)
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
structure ObligationId where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def accessId (selected : InvocationId) : ObligationId := ⟨selected, 0⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
def invalidateId (selected : InvocationId) : ObligationId := ⟨selected, 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def accessEntry (selected : InvocationId) (entry : X86_64MachineState) :
    Entry ObligationId ObligationKind :=
  ⟨accessId selected,
    .exclusiveStore (entryBinding selected) (entryGeneration selected) (byteRange entry)⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def invalidateEntry (selected : InvocationId) : Entry ObligationId ObligationKind :=
  ⟨invalidateId selected,
    .invalidateView (entryBinding selected) (entryGeneration selected) (storeCapture selected)⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def emptyWorld : World ObligationId ObligationKind := World.empty

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def accessWorld (selected : InvocationId) (entry : X86_64MachineState) :
    World ObligationId ObligationKind :=
  ⟨[accessEntry selected entry], by simp [accessEntry]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
def entryWorld (selected : InvocationId) (entry : X86_64MachineState) :
    World ObligationId ObligationKind :=
  ⟨[invalidateEntry selected, accessEntry selected entry], by
    simp [invalidateEntry, invalidateId, accessEntry, accessId]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem accessIssuance (selected : InvocationId) (entry : X86_64MachineState) :
    Issuance emptyWorld (accessWorld selected entry) (accessEntry selected entry) := by
  exact ⟨by simp [emptyWorld, accessWorld, World.empty]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem invalidationIssuance (selected : InvocationId) (entry : X86_64MachineState) :
    Issuance (accessWorld selected entry) (entryWorld selected entry)
      (invalidateEntry selected) := by
  exact ⟨by simp [accessWorld, entryWorld]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
theorem obligation_ids_disjoint_of_invocation_ne {left right : InvocationId}
    (different : left ≠ right) {leftOrdinal rightOrdinal : Nat} :
    (⟨left, leftOrdinal⟩ : ObligationId) ≠ ⟨right, rightOrdinal⟩ := by
  intro equal
  exact different (congrArg ObligationId.invocation equal)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
theorem entryWorld_disjoint_of_invocation_ne {left right : InvocationId}
    (different : left ≠ right) (leftState rightState : X86_64MachineState) :
    (entryWorld left leftState).Disjoint (entryWorld right rightState) := by
  intro leftId leftMember rightId rightMember
  simp only [entryWorld, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at leftMember rightMember
  rcases leftMember with rfl | rfl <;> rcases rightMember with rfl | rfl
  all_goals exact obligation_ids_disjoint_of_invocation_ne different

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
/-- Structural correlation and issuance only. This grants neither live/latest validity nor target
    execution admission. -/
structure StructuralStoreAuthority (selected : InvocationId)
    (entry : X86_64MachineState) : Prop where
  envelopeWellFormed : (execution entry).WellFormed
  historyWellFormed : (history entry).WellFormed (execution entry)
  captureResolves : (history entry).Captures (storeCapture selected) (entryBinding selected)
  useResolves : (history entry).Uses (storeUse selected) (entryBinding selected)
  exactPath : OccurrencePath (execution entry) .capture .store
    [.captureToStore] [.programOrder]
  accessIssued : Issuance emptyWorld (accessWorld selected entry) (accessEntry selected entry)
  invalidationIssued : Issuance (accessWorld selected entry) (entryWorld selected entry)
    (invalidateEntry selected)
  accessBound : (entryWorld selected entry).Binds
    (accessEntry selected entry).id (accessEntry selected entry).payload
  invalidationBound : (entryWorld selected entry).Binds
    (invalidateEntry selected).id (invalidateEntry selected).payload

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#principal-invariant -/
theorem structuralStoreAuthority : StructuralStoreAuthority invocation entryState where
  envelopeWellFormed := execution_wellFormed entryState
  historyWellFormed := history_wellFormed entryState
  captureResolves := by
    exact ⟨storeCaptureRecord, .stack, history_captureRecord_store entryState,
      entryRootRecord, history_rootRecord_entry entryState, rfl, rfl⟩
  useResolves := by
    exact ⟨storeUseRecord, history_useRecord_store entryState,
      storeCaptureRecord, .stack, history_captureRecord_store entryState,
      entryRootRecord, history_rootRecord_entry entryState, rfl, rfl⟩
  exactPath := capture_to_store_path entryState
  accessIssued := accessIssuance invocation entryState
  invalidationIssued := invalidationIssuance invocation entryState
  accessBound := by simp [World.Binds, entryWorld]
  invalidationBound := by simp [World.Binds, entryWorld]

end Spikes.CheckedMemoryWindows.Authority

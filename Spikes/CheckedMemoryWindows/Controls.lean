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

import Spikes.CheckedMemoryWindows.Equivalence

/-!
Adversarial controls for the checked-store demonstration. They reject the principal mismatches at
the public relational boundaries; private constructors separately prevent callers from directly
fabricating a `TypedStoreView`, Windows stack grant, store realization, or checked instruction.
-/

namespace Spikes.CheckedMemoryWindows.Controls

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.MemoryModel.BindingHistory
open Gasm.MemoryModel.ObligationWorld
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.StackStorePrefix
open Spikes.CheckedMemoryWindows.Authority
open Spikes.CheckedMemoryWindows.Realization

local instance : ExternalCallInterceptor X86_64 Spikes.CheckedMemoryWindows.Event :=
  standardWindowsRuntime Spikes.CheckedMemoryWindows.Event

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def staleAccess : Entry ObligationId ObligationKind :=
  ⟨.access, .exclusiveStore .entryStack 1 (byteFootprint entryState)⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem stale_generation_rejected :
    ¬ (entryWorld entryState).Binds staleAccess.id staleAccess.payload := by
  simp [World.Binds, entryWorld, staleAccess, accessEntry, invalidateEntry]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def wrongBindingAccess : Entry ObligationId ObligationKind :=
  ⟨.access, .exclusiveStore .otherStack 0 (byteFootprint entryState)⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem different_binding_same_address_rejected :
    ¬ (entryWorld entryState).Binds wrongBindingAccess.id wrongBindingAccess.payload := by
  simp [World.Binds, entryWorld, wrongBindingAccess, accessEntry, invalidateEntry]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem wrong_rights_rejected :
    (history entryState).bindingRecord .entryStack ≠ some {
      key := .stack
      generation := (0 : BindingGeneration)
      object := .entryStack
      rights := .sharedRead
      logicalFootprint := frameFootprint entryState
      backingFootprint := frameFootprint entryState } := by
  intro equal
  simp only [history] at equal
  have recordEqual := Option.some.inj equal
  have rightsEqual := congrArg (fun record => record.rights) recordEqual
  cases rightsEqual

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem wrong_footprint_rejected :
    (history entryState).bindingRecord .entryStack ≠ some {
      key := .stack
      generation := (0 : BindingGeneration)
      object := .entryStack
      rights := .exclusiveWrite
      logicalFootprint := ⟨(frameFootprint entryState).start, 39⟩
      backingFootprint := frameFootprint entryState } := by
  intro equal
  have lengths := congrArg (fun record => record.map
    (fun selected => selected.logicalFootprint.length)) equal
  change some frameSize.toNat = some 39 at lengths
  have lengthEqual := Option.some.inj lengths
  change 40 = 39 at lengthEqual
  omega

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem other_binding_not_captured :
    ¬ (history entryState).Captures .afterAllocation .otherStack := by
  intro captured
  rcases captured with ⟨capture, key, captureResolved, frontierResolved⟩
  simp only [history] at captureResolved
  cases captureResolved
  rcases frontierResolved with ⟨root, rootResolved, _, initialResolved⟩
  simp only [history] at rootResolved
  cases rootResolved
  cases initialResolved

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem wrong_use_event_rejected :
    (history entryState).useRecord .selectedStore ≠ some {
      event := Event.capture
      capture := .afterAllocation } := by
  intro equal
  simp only [history] at equal
  have recordEqual := Option.some.inj equal
  have eventsEqual := congrArg (fun record => record.event) recordEqual
  cases eventsEqual

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem checked_descriptor_mismatch_rejected :
    X86_64Instruction.encode checkedStore.erase ≠
      X86_64Instruction.encode (mov_rsp_byte 31 storedValue) := by
  rw [CheckedStore.erase_eq]
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def wrongRspState : X86_64MachineState :=
  entryState.setGpr64 .rsp 0

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem total_memory_does_not_supply_entry_grant :
    ¬ EntryStackCommittedWritable wrongRspState (frameFootprint wrongRspState) := by
  intro committed
  have statesEqual := committed.1
  have rspEqual := congrArg X86_64MachineState.rsp statesEqual
  change 0 = 0x7FFFFFFF0008 at rspEqual
  exact (by decide : (0 : UInt64) ≠ 0x7FFFFFFF0008) rspEqual

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def missingInvalidationWorld : World ObligationId ObligationKind :=
  ⟨[accessEntry entryState], by simp [accessEntry]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem omitted_invalidation_rejected :
    ¬ (entryWorld entryState).Equivalent missingInvalidationWorld := by
  intro equivalent
  have lengths := equivalent.length_eq
  simp [entryWorld, missingInvalidationWorld] at lengths

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def wrongArtifact : WindowsX86_64Artifact :=
  { artifact with instructions := [] }

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem wrong_artifact_not_established (environment : Environment)
    (loaded : X86_64MachineState) (context : CheckedMemoryContext) :
    ¬ CheckedMemoryEstablished wrongArtifact environment loaded context := by
  intro established
  have instructionsEqual := congrArg
    (fun selected : WindowsX86_64Artifact => selected.instructions) established.1
  change [] = instructions at instructionsEqual
  rw [instructions_shape] at instructionsEqual
  contradiction

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem wrong_terminal_cannot_authorize_lifecycle :
    (runProgramOutcomeLoop (Event := Spikes.CheckedMemoryWindows.Event)
      indexed 4 entryState []).observable ≠
      .processExited 1 [Inject.inject (ProcessEvent.exit 1)] := by
  rw [canonicalObservable]
  intro equal
  cases equal

end Spikes.CheckedMemoryWindows.Controls

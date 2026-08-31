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
Adversarial controls for the checked-store demonstration. They exercise invocation separation,
exact obligation payloads, mapped-range bounds, descriptor fidelity, lifecycle accounting, and
the all-legs admission boundary. Private constructors separately prevent fabrication of the
loader grant, logical refinement, physical realization, checked instruction, lifecycle, or final
admission bundle.
-/

namespace Spikes.CheckedMemoryWindows.Controls

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.MemoryModel
open Gasm.MemoryModel.ObligationWorld
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.StackStorePrefix
open Gasm.Targets.Windows
open Gasm.Targets.Windows.ProcessEntryMemory
open Spikes.CheckedMemoryWindows
open Spikes.CheckedMemoryWindows.Authority
open Spikes.CheckedMemoryWindows.Realization

variable [selectedHost : HostSelection]

local instance : ExternalCallInterceptor X86_64 Spikes.CheckedMemoryWindows.Event :=
  standardWindowsRuntime Spikes.CheckedMemoryWindows.Event

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def staleAccess : Entry ObligationId ObligationKind :=
  ⟨accessId invocation,
    .exclusiveStore (entryBinding invocation) ⟨invocation, 1⟩ (byteRange entryState)⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem stale_generation_rejected :
    ¬ (entryWorld invocation entryState).Binds staleAccess.id staleAccess.payload := by
  simp [World.Binds, entryWorld, staleAccess, accessEntry, invalidateEntry,
    entryGeneration]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem checked_descriptor_mismatch_rejected :
    X86_64Instruction.encode checkedStore.erase ≠
      X86_64Instruction.encode (mov_rsp_byte 31 storedValue) := by
  rw [CheckedStore.erase_eq]
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def outsideCommitted : AddressRange :=
  ⟨0x7FFFFFFEEFFF, 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem outside_committed_not_mapped :
    ¬ MappedWritable processEntryLoad processEntryLoad.afterHost outsideCommitted := by
  intro mapped
  have contained := mapped.withinCommitted
  change 0x7FFFFFFEF000 ≤ 0x7FFFFFFEEFFF ∧ _ at contained
  omega

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem authored_mapping_without_load_rejected (current : WindowsHostState)
    (notLoaded : current ≠ processEntryLoad.afterHost) :
    ¬ MappedWritable processEntryLoad current (byteRange entryState) := by
  intro mapped
  exact notLoaded mapped.currentIsLoaded

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def missingInvalidationWorld : World ObligationId ObligationKind :=
  accessWorld invocation entryState

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem omitted_invalidation_rejected :
    ¬ (entryWorld invocation entryState).Equivalent missingInvalidationWorld := by
  intro equivalent
  have lengths := equivalent.length_eq
  simp [entryWorld, missingInvalidationWorld, accessWorld] at lengths

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def secondProcessEntryLoad :
    ProcessEntryLoad executable processEntryLoad.afterHost :=
  loadProcessEntry executable processEntryLoad.afterHost

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem consecutive_invocation_ids_differ :
    secondProcessEntryLoad.invocation ≠ invocation := by
  exact sequential_invocations_ne selectedHost.beforeHost executable

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem consecutive_worlds_are_disjoint :
    (entryWorld invocation entryState).Disjoint
      (entryWorld secondProcessEntryLoad.invocation secondProcessEntryLoad.machine) := by
  exact entryWorld_disjoint_of_invocation_ne (Ne.symm consecutive_invocation_ids_differ)
    entryState secondProcessEntryLoad.machine

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- Any value that reaches the sole admission type necessarily contains every reviewed leg. These
    projections are deletion controls: dropping logical, physical, authoring, lifecycle, issuance,
    or termination evidence makes the admission constructor unavailable. -/
private theorem admission_has_all_legs {selected : InvocationId}
    {state : X86_64MachineState} {activeHost : WindowsHostState}
    (admission : MemoryAdmission selected state activeHost) :
    processEntryLoad = loadProcessEntry executable selectedHost.beforeHost ∧
      TypedStoreView selected state ∧
      X86StoreRealization selected state activeHost ∧
      AuthoringEstablished selected state activeHost ∧
      Nonempty (LifecycleCompletion selected state activeHost) := by
  exact ⟨admission.operationalLoad, admission.logical, admission.physical,
    admission.authored, ⟨admission.lifecycle⟩⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem replaying_same_host_replays_identity :
    (loadProcessEntry executable selectedHost.beforeHost).invocation =
      (loadProcessEntry executable selectedHost.beforeHost).invocation := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem replayed_worlds_cannot_be_disjoint :
    ¬ (entryWorld invocation entryState).Disjoint (entryWorld invocation entryState) := by
  intro disjoint
  exact disjoint (accessId invocation)
    (by simp [entryWorld, accessEntry]) (accessId invocation)
    (by simp [entryWorld, accessEntry]) rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def otherNamespaceHost : WindowsHostState :=
  WindowsHostState.root ⟨selectedHost.beforeHost.hostNamespace.key + 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem independent_namespace_ids_differ :
    (loadProcessEntry executable selectedHost.beforeHost).invocation ≠
      (loadProcessEntry executable otherNamespaceHost).invocation := by
  apply namespace_separates_invocations (executable := executable)
  intro equal
  have keys := congrArg HostNamespace.key equal
  change selectedHost.beforeHost.hostNamespace.key =
    selectedHost.beforeHost.hostNamespace.key + 1 at keys
  omega

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def invalidatedProductionExecution : ProcessExecution processEntryLoad :=
  productionBindingExecution.invalidate

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem inserted_invalidation_is_projected :
    bindingChanges invalidatedProductionExecution.events = [.invalidated invocation] := by
  simp [invalidatedProductionExecution, ProcessExecution.invalidate]
  rfl

private theorem inserted_invalidation_kills_binding :
    invalidatedProductionExecution.binding = none := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def reboundProductionExecution : ProcessExecution processEntryLoad :=
  productionBindingExecution.rebind ⟨invocation, invocation.generation + 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem inserted_rebind_is_projected :
    bindingChanges reboundProductionExecution.events =
      [.rebound invocation ⟨invocation, invocation.generation + 1⟩] := by
  simp [reboundProductionExecution, ProcessExecution.rebind]
  rfl

private theorem inserted_rebind_changes_binding :
    reboundProductionExecution.binding =
      some ⟨invocation, invocation.generation + 1⟩ := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem post_retirement_store_rejected :
    ¬ MappedWritable processEntryLoad
      (rootTeardownAfterExitProcess processEntryLoad 0).afterHost (byteRange entryState) := by
  intro mapped
  exact committedEntry_not_active_after_teardown processEntryLoad 0 mapped.committedPresent

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem recipient_free_return_not_claimed (recipient : InvocationId) :
    RootDisposition.returnExclusive recipient ∉ lifecycleCompletion.dispositions := by
  rw [lifecycleCompletion.dispositionsExact]
  simp

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

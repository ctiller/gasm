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
    ¬ MappedWritable processEntryLoad outsideCommitted := by
  intro mapped
  have contained := mapped.withinCommitted
  rw [processEntryLoad.stackExact] at contained
  change 0x7FFFFFFEF000 ≤ 0x7FFFFFFEEFFF ∧ _ at contained
  omega

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
    ProcessEntryLoad executable processEntryLoad.afterInvocations :=
  loadProcessEntry executable processEntryLoad.afterInvocations

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private theorem consecutive_invocation_ids_differ :
    secondProcessEntryLoad.invocation ≠ invocation := by
  exact consecutive_invocations_ne initialInvocationWorld

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
    {state : X86_64MachineState} (admission : MemoryAdmission selected state) :
    InvocationIssuance initialInvocationWorld processEntryLoad.afterInvocations selected ∧
      TypedStoreView selected state ∧
      X86StoreRealization selected state ∧
      AuthoringEstablished selected state ∧
      LifecycleCompletion selected state := by
  exact ⟨admission.invocationIssued, admission.logical, admission.physical,
    admission.authored, admission.lifecycle⟩

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

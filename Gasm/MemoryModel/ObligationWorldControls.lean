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

import Gasm.MemoryModel.ObligationWorld

/-!
Private controls for the structural obligation world. They exercise the actual finite-map,
issuance, removal, and disjoint-composition structures. Inhabitation proves structural consistency
only; it grants no target fidelity, lifecycle authority, or execution admission.
-/

namespace Gasm.MemoryModel.ObligationWorldControls

open Gasm.MemoryModel.ObligationWorld

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private inductive Kind where
  | exclusive (binding generation : Nat)
  | invalidateView (binding generation view : Nat)
  deriving DecidableEq

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private abbrev OccurrenceId := Nat

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def access : Entry OccurrenceId Kind := ⟨17, .exclusive 7 3⟩
/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def invalidation : Entry OccurrenceId Kind := ⟨18, .invalidateView 7 3 11⟩
/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def frameToken : Entry OccurrenceId Kind := ⟨29, .exclusive 20 1⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def empty : World OccurrenceId Kind := World.empty

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def accessWorld : World OccurrenceId Kind :=
  ⟨[access], by decide⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def lifecycleWorld : World OccurrenceId Kind :=
  ⟨[invalidation, access], by decide⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def completedWorld : World OccurrenceId Kind :=
  ⟨[], by decide⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def frameWorld : World OccurrenceId Kind :=
  ⟨[frameToken], by decide⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
private def mutatedAccessWorld : World OccurrenceId Kind :=
  ⟨[⟨access.id, .exclusive 99 1⟩], by decide⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
private theorem issue_access : Issuance empty accessWorld access := by
  exact ⟨by simp [empty, accessWorld, World.empty]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
private theorem remove_invalidation : Removal lifecycleWorld accessWorld invalidation := by
  exact ⟨by simp [lifecycleWorld, accessWorld]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
private theorem remove_access : Removal accessWorld completedWorld access := by
  exact ⟨by simp [accessWorld, completedWorld]⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
private theorem lifecycle_frame_disjoint : lifecycleWorld.Disjoint frameWorld := by
  simp [World.Disjoint, lifecycleWorld, frameWorld, invalidation, access, frameToken]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
private def framedLifecycle : World OccurrenceId Kind :=
  lifecycleWorld.compose frameWorld lifecycle_frame_disjoint

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- The finite-map invariant rejects two occurrences with the same nominal identity, even when
    their payloads differ. -/
private theorem duplicate_identity_rejected :
    ¬ (([access, { id := access.id, payload := .exclusive 99 1 }] :
      List (Entry OccurrenceId Kind)).map Entry.id).Nodup := by
  decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- Exact removal preserves the complete identity-and-payload entry of every survivor. -/
private theorem removal_preserves_access_payload : access ∈ lifecycleWorld.entries := by
  exact remove_invalidation.survivor_bound (by simp [accessWorld])

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- Removing another occurrence cannot preserve an identity while replacing its payload. -/
private theorem removal_rejects_payload_mutation :
    ¬ Removal lifecycleWorld mutatedAccessWorld invalidation := by
  intro removal
  have preserved : access ∈ mutatedAccessWorld.entries :=
    (removal.survivor_iff (by decide)).mpr (by simp [lifecycleWorld])
  simp [mutatedAccessWorld, access] at preserved

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- Exact removal cannot mint an obligation from the empty world. -/
private theorem no_mint_from_empty :
    ¬ Removal (empty : World OccurrenceId Kind) accessWorld access := by
  intro removal
  have lengthContradiction := removal.length_exact
  simp [empty, accessWorld, World.empty] at lengthContradiction

end Gasm.MemoryModel.ObligationWorldControls

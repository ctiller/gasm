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

/-!
The structural core of the canonical obligation world.

An obligation occurrence has a stable, generative identity and an immutable typed payload. A world
is a finite partial map represented by a duplicate-free list of identities; list order is
presentation only. `Removal` and `Issuance` describe exact one-entry deltas, so every surviving
identity keeps the same payload. Spatial composition additionally requires disjoint identities.

This module grants no discharge, issuance, target-fidelity, or execution authority. Lean values
and proofs are duplicable and therefore cannot by themselves be linear capabilities. A concrete
profile must govern identity generation and prove, in its full indexed authority state, that the
resource authorizing an `Issuance` or `Removal` is fresh, retained, transformed, or consumed as
its protocol requires. In particular, this generic layer deliberately has no `CanDischarge`
policy and no caller-selected cleanup/drop flag.
-/

namespace Gasm.MemoryModel.ObligationWorld

universe u v

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
/-- One nominal obligation occurrence. Equal payloads may occur repeatedly, but only at distinct
    occurrence identities. -/
structure Entry (Id : Type u) (Payload : Type v) where
  id : Id
  payload : Payload

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
/-- A finite partial map from obligation occurrence identities to immutable payloads. -/
structure World (Id : Type u) (Payload : Type v) where
  entries : List (Entry Id Payload)
  uniqueIds : (entries.map Entry.id).Nodup

namespace World

variable {Id : Type u} {Payload : Type v}

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
/-- Relational lookup in the finite obligation map. -/
def Binds (world : World Id Payload) (id : Id) (payload : Payload) : Prop :=
  ⟨id, payload⟩ ∈ world.entries

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Empty structural obligation fragment. -/
def empty : World Id Payload := ⟨[], List.nodup_nil⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Two worlds have no obligation occurrence identity in common. -/
def Disjoint (left right : World Id Payload) : Prop :=
  ∀ leftId ∈ left.entries.map Entry.id,
    ∀ rightId ∈ right.entries.map Entry.id, leftId ≠ rightId

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Spatial composition is defined only for identity-disjoint fragments. -/
def compose (left right : World Id Payload) (disjoint : Disjoint left right) :
    World Id Payload :=
  { entries := left.entries ++ right.entries
    uniqueIds := by
      rw [List.map_append, List.nodup_append]
      exact ⟨left.uniqueIds, right.uniqueIds, disjoint⟩ }

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- World equivalence forgets only list presentation order, never identity or payload. -/
def Equivalent (left right : World Id Payload) : Prop :=
  left.entries.Perm right.entries

@[simp] theorem binds_empty (id : Id) (payload : Payload) :
    ¬ (empty : World Id Payload).Binds id payload := by
  simp [Binds, empty]

@[simp] theorem compose_entries (left right : World Id Payload)
    (disjoint : Disjoint left right) :
    (compose left right disjoint).entries = left.entries ++ right.entries := rfl

@[simp] theorem compose_empty_right (world : World Id Payload)
    (disjoint : Disjoint world empty) :
    (compose world empty disjoint).entries = world.entries := by
  simp [compose, empty]

@[simp] theorem compose_empty_left (world : World Id Payload)
    (disjoint : Disjoint empty world) :
    (compose empty world disjoint).entries = world.entries := by
  simp [compose, empty]

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem equivalent_refl (world : World Id Payload) : world.Equivalent world :=
  List.Perm.refl _

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem equivalent_symm {left right : World Id Payload}
    (equivalent : left.Equivalent right) : right.Equivalent left :=
  equivalent.symm

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem equivalent_trans {first second third : World Id Payload}
    (firstSecond : first.Equivalent second) (secondThird : second.Equivalent third) :
    first.Equivalent third :=
  firstSecond.trans secondThird

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem compose_comm_equivalent (left right : World Id Payload)
    (leftRight : Disjoint left right) (rightLeft : Disjoint right left) :
    Equivalent (compose left right leftRight) (compose right left rightLeft) :=
  List.perm_append_comm

end World

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
/-- Exact removal of one named identity and payload. This is structural delta evidence, not
    evidence that any caller or profile was authorized to perform the discharge. -/
structure Removal {Id : Type u} {Payload : Type v}
    (before after : World Id Payload) (removed : Entry Id Payload) : Prop where
  exact : before.entries.Perm (removed :: after.entries)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#decomposition -/
/-- Exact fresh issuance of one named identity and payload. Freshness follows from the resulting
    world's unique-ID invariant; authority to allocate the identity is profile-owned. -/
structure Issuance {Id : Type u} {Payload : Type v}
    (before after : World Id Payload) (issued : Entry Id Payload) : Prop where
  exact : after.entries.Perm (issued :: before.entries)

namespace Removal

variable {Id : Type u} {Payload : Type v}
  {before after : World Id Payload} {removed : Entry Id Payload}

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
theorem length_exact (removal : Removal before after removed) :
    before.entries.length = after.entries.length + 1 := by
  rw [removal.exact.length_eq]
  simp

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
theorem was_bound (removal : Removal before after removed) :
    before.Binds removed.id removed.payload := by
  exact removal.exact.mem_iff.mpr (by simp)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
/-- Every exact surviving entry, including its immutable payload, remains bound. -/
theorem survivor_bound (removal : Removal before after removed)
    {survivor : Entry Id Payload} (member : survivor ∈ after.entries) :
    survivor ∈ before.entries := by
  exact removal.exact.mem_iff.mpr (by simp [member])

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
/-- Lookup conservation: every identity other than the removed one has exactly the same complete
    identity-and-payload entry before and after removal. -/
theorem survivor_iff (removal : Removal before after removed)
    {survivor : Entry Id Payload} (differentId : survivor.id ≠ removed.id) :
    survivor ∈ after.entries ↔ survivor ∈ before.entries := by
  constructor
  · exact removal.survivor_bound
  · intro member
    have member' := removal.exact.mem_iff.mp member
    simp only [List.mem_cons] at member'
    rcases member' with equal | member'
    · exact False.elim (differentId (congrArg Entry.id equal))
    · exact member'

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- The selected occurrence identity is absent after its exact removal. -/
theorem removed_id_absent (removal : Removal before after removed) :
    removed.id ∉ after.entries.map Entry.id := by
  have mapped := removal.exact.map Entry.id
  have afterConsNodup := mapped.nodup before.uniqueIds
  simpa using (List.nodup_cons.mp afterConsNodup).1

end Removal

namespace Issuance

variable {Id : Type u} {Payload : Type v}
  {before after : World Id Payload} {issued : Entry Id Payload}

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
theorem length_exact (issuance : Issuance before after issued) :
    after.entries.length = before.entries.length + 1 := by
  rw [issuance.exact.length_eq]
  simp

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
theorem is_bound (issuance : Issuance before after issued) :
    after.Binds issued.id issued.payload := by
  exact issuance.exact.mem_iff.mpr (by simp)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
/-- Every pre-existing entry, including its immutable payload, survives issuance exactly. -/
theorem prior_bound (issuance : Issuance before after issued)
    {prior : Entry Id Payload} (member : prior ∈ before.entries) :
    prior ∈ after.entries := by
  exact issuance.exact.mem_iff.mpr (by simp [member])

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#bounds-and-framing -/
/-- Lookup conservation: every identity other than the issued one has exactly the same complete
    identity-and-payload entry before and after issuance. -/
theorem prior_iff (issuance : Issuance before after issued)
    {prior : Entry Id Payload} (differentId : prior.id ≠ issued.id) :
    prior ∈ after.entries ↔ prior ∈ before.entries := by
  constructor
  · intro member
    have member' := issuance.exact.mem_iff.mp member
    simp only [List.mem_cons] at member'
    rcases member' with equal | member'
    · exact False.elim (differentId (congrArg Entry.id equal))
    · exact member'
  · exact issuance.prior_bound

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- An issued occurrence identity is genuinely fresh in the prior world. -/
theorem issued_id_fresh (issuance : Issuance before after issued) :
    issued.id ∉ before.entries.map Entry.id := by
  have mapped := issuance.exact.map Entry.id
  have beforeConsNodup := mapped.nodup after.uniqueIds
  simpa using (List.nodup_cons.mp beforeConsNodup).1

end Issuance

end Gasm.MemoryModel.ObligationWorld

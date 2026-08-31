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

import Gasm.MemoryModel.AccessAudit

/-!
Private controls for the access-audit semantics. They exercise the actual public structures and
composition operations. Inhabitation and `Safe` proofs establish only the internal consistency of
the proof-side audit. They grant no target fidelity, reachability, execution authority,
`VerifiedProgram` admission, or permission to erase an architectural fault.
-/

namespace Gasm.MemoryModel.AccessAuditControls

open Gasm.MemoryModel
open Gasm.MemoryModel.AccessAudit

private inductive Event where | instruction (id : Nat)
private inductive Agent where | cpu (id : Nat)
private inductive Origin where | point (index : Nat)
private inductive Kind where | load | store
private inductive Authority where | binding (id : Nat)
private inductive Generation where | generation (id : Nat)
private inductive Reason where
  | unmapped
  | staleGeneration
  | wrongAgent

private def domains : Domains where
  EventId := Event
  AgentId := Agent
  Origin := Origin
  AccessKind := Kind
  AuthorityId := Authority
  Generation := Generation
  Reason := Reason

private def attempt : Attempt domains := {
  event := .instruction 7
  agent := .cpu 2
  origin := .point 11
  kind := .store
  range := { start := 0x4000, length := 8 }
  authority := some (.binding 5)
  generation := some (.generation 3)
}

private abbrev Machine := Nat

private def initial : State domains Machine := State.initial 10

private def increment (machine : Machine) : Except Reason (Machine × Nat) :=
  .ok (machine + 1, machine)

private def refuse (_machine : Machine) : Except Reason (Machine × Nat) :=
  .error .staleGeneration

private def incrementOnlyAtTen (machine : Machine) : Except Reason (Machine × Nat) :=
  if machine = 10 then .ok (machine + 1, machine) else .error .wrongAgent

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Positive baseline: an allowed access changes the semantic machine, returns its value, and
    leaves the initially empty audit exactly empty. -/
private theorem allowed_baseline :
    execute attempt increment initial =
      .allowed { machine := 11, violations := [] } 10 := by
  rfl

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Refusal retains the complete attempted access and reason while preserving the pre-access
    machine. -/
private theorem denied_baseline :
    execute attempt refuse initial = .denied {
      machine := 10
      violations := [{ attempt := attempt, reason := .staleGeneration }]
    } := by
  rfl

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
private theorem denied_machine_unchanged :
    (execute attempt refuse initial).finalState.machine = 10 := by
  rfl

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
private theorem denied_is_not_clean : ¬ (execute attempt refuse initial).Clean := by
  simp [execute, refuse, initial, Outcome.Clean, Outcome.finalState, State.initial, State.Clean]

private def forbiddenContinuation (_ : Nat) : Checked domains Machine Nat :=
  fun state => .allowed { state with machine := 999 } 999

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A denied access is terminal: sequential composition cannot run a continuation that mutates the
    machine or fabricates a read value. -/
private theorem denied_stops_composition :
    bind (execute attempt refuse) forbiddenContinuation initial =
      execute attempt refuse initial := by
  rfl

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
private theorem increment_safe : Safe (execute attempt increment) := by
  apply Safe.execute
  intro machine
  exact ⟨machine + 1, machine, rfl⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Real accesses need not succeed from arbitrary raw states. A selected entry invariant supplies
    the capability/frame fact from which the ordinary checked decision is automatic. -/
private theorem conditional_increment_safe :
    SafeUnder (fun state : State domains Machine => state.machine = 10)
      (execute attempt incrementOnlyAtTen) := by
  apply SafeUnder.execute
  intro state _clean atTen
  refine ⟨11, 10, ?_⟩
  rw [incrementOnlyAtTen, if_pos atTen, atTen]
  rfl

private def twoIncrements : Checked domains Machine (Nat × Nat) :=
  bind (execute attempt increment) fun first =>
    bind (execute attempt increment) fun second =>
      pure (first, second)

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Common successful cases compose without explicit audit equalities at each instruction. -/
private theorem two_increments_safe : Safe twoIncrements := by
  apply Safe.bind increment_safe
  intro first
  apply Safe.bind increment_safe
  intro second
  exact Safe.pure (first, second)

private def dirty : State domains Machine := {
  machine := 10
  violations := [{ attempt := attempt, reason := .unmapped }]
}

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A later successful access cannot erase an earlier violation. -/
private theorem success_cannot_clean_dirty_prefix :
    (execute attempt increment dirty).finalState.violations = dirty.violations := by
  rfl

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A later refusal appends after rather than replacing an earlier diagnostic. -/
private theorem refusal_preserves_dirty_prefix :
    (execute attempt refuse dirty).finalState.violations =
      dirty.violations ++ [{ attempt := attempt, reason := .staleGeneration }] := by
  rfl

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- The refusal computation cannot satisfy the compositional safety certificate. This prevents a
    vacuous green baseline in which `Safe` silently accepts terminal denied outcomes. -/
private theorem refusal_not_safe : ¬ Safe (execute attempt refuse) := by
  intro safe
  obtain ⟨final, value, outcome, clean⟩ := safe initial (by rfl)
  simp [execute, refuse] at outcome

end Gasm.MemoryModel.AccessAuditControls

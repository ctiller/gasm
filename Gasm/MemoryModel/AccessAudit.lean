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

import Gasm.MemoryModel.AddressRange

/-!
Target-neutral audit semantics for checked memory accesses.

The audit is proof-side execution data, not architectural machine state and not a caller-visible
program observation. A target supplies the exact event, agent, origin, access, authority, and
reason vocabularies. This generic layer records those values without assigning them target
meaning.

`execute` is deliberately fail closed. A successful decision may update the underlying semantic
machine and preserves the audit exactly. A refused decision preserves the pre-access machine,
appends one structured violation, and returns a terminal `denied` outcome. `bind` cannot resume a
denied computation, so no invalid read receives a fabricated value and no denied write has a
memory effect.

`Safe` is the compositional proof shape intended for lowering automation: from every clean input,
the computation must produce a clean successful outcome. This module does not change
`VerifiedProgram`, grant target fidelity, decide authority, or admit an execution. A later
Trust-reviewed platform bridge must connect the real reachable execution relation to this audit
and make absence of violations a mandatory whole-program condition. That bridge must also prove
coverage: every memory access in the target semantics is represented by an `execute` node with
its exact origin and access metadata. Sealing prevents denial laundering, but cannot by itself
prove that a target lowering did not omit a semantic access.
-/

namespace Gasm.MemoryModel.AccessAudit

universe u v w x

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Profile-selected identities and diagnostic vocabularies for checked accesses. `Origin` may be
    an EventKey-derived CPU program point, a platform occurrence, or a device-domain origin. -/
structure Domains where
  EventId : Type u
  AgentId : Type u
  Origin : Type u
  AccessKind : Type u
  AuthorityId : Type u
  Generation : Type u
  Reason : Type u

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Complete request identity retained when an authority decision refuses an access. -/
structure Attempt (d : Domains) where
  event : d.EventId
  agent : d.AgentId
  origin : d.Origin
  kind : d.AccessKind
  range : AddressRange
  authority : Option d.AuthorityId
  generation : Option d.Generation

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- One exact refused access and the profile-supplied reason for refusal. -/
structure Violation (d : Domains) where
  attempt : Attempt d
  reason : d.Reason

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A semantic machine paired with its append-only proof audit. The audit is deliberately outside
    the target's architectural state so it erases before emission. -/
structure State (d : Domains) (Machine : Type v) where
  machine : Machine
  violations : List (Violation d)

namespace State

variable {d : Domains} {Machine : Type v}

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- No checked access has been refused on this execution prefix. -/
def Clean (state : State d Machine) : Prop := state.violations = []

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Installs an architectural/semantic machine with an empty proof audit. -/
def initial (machine : Machine) : State d Machine :=
  { machine := machine, violations := [] }

@[simp] theorem initial_clean (machine : Machine) : (initial (d := d) machine).Clean := rfl

end State

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Explicit checked-access outcome. `denied` is terminal for composition and retains the exact
    post-audit state; it never carries a fabricated access result. -/
inductive Outcome (d : Domains) (Machine : Type v) (Value : Type w) where
  | allowed (state : State d Machine) (value : Value)
  | denied (state : State d Machine)

namespace Outcome

variable {d : Domains} {Machine : Type v} {Value : Type w}

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- The complete semantic state is retained for either outcome. -/
def finalState : Outcome d Machine Value → State d Machine
  | .allowed state _ | .denied state => state

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Whole-prefix absence of refused accesses, independent of how a successful value is projected. -/
def Clean (outcome : Outcome d Machine Value) : Prop := outcome.finalState.Clean

end Outcome

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Constructor-controlled checked computation. Its evaluator and constructor are private;
    public clients compose only through `pure`, `execute`, and `bind`. Consequently clients cannot
    inspect an intermediate denial, truncate its audit, or manufacture a successful result. -/
structure Checked (d : Domains) (Machine : Type v) (Value : Type w) where
  private ofEvaluator ::
  private evaluator : State d Machine → Outcome d Machine Value

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- The sole evaluator for a constructor-controlled checked computation. -/
def run (computation : Checked d Machine Value) (state : State d Machine) :
    Outcome d Machine Value :=
  computation.evaluator state

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Lift one profile decision into fail-closed audit semantics. The decision returns the complete
    allowed machine/value pair or the exact refusal reason. -/
def execute (attempt : Attempt d)
    (decision : Machine → Except d.Reason (Machine × Value)) : Checked d Machine Value :=
  ⟨fun state =>
      match decision state.machine with
      | .ok (machine, value) =>
          .allowed { machine := machine, violations := state.violations } value
      | .error reason =>
          .denied {
            machine := state.machine
            violations := state.violations ++ [{ attempt := attempt, reason := reason }]
          }⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Successful checked computation with no machine effect or audit effect. -/
def pure (value : Value) : Checked d Machine Value :=
  ⟨fun state => .allowed state value⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Sequential composition stops at the first refusal. The sealed representation has no catch:
    the continuation cannot observe denial, manufacture a read value, or erase its audit. -/
def bind (first : Checked d Machine Value)
    (next : Value → Checked d Machine Result) : Checked d Machine Result :=
  ⟨fun state =>
    match run first state with
    | .allowed state value => run (next value) state
    | .denied state => .denied state⟩

namespace execute

variable {d : Domains} {Machine : Type v} {Value : Type w}
  {attempt : Attempt d} {decision : Machine → Except d.Reason (Machine × Value)}
  {state : State d Machine} {machine : Machine} {value : Value} {reason : d.Reason}

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem of_ok (allowed : decision state.machine = .ok (machine, value)) :
    run (execute attempt decision) state =
      .allowed { machine := machine, violations := state.violations } value := by
  simp [run, execute, allowed]

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem of_error (denied : decision state.machine = .error reason) :
    run (execute attempt decision) state = .denied {
      machine := state.machine
      violations := state.violations ++ [{ attempt := attempt, reason := reason }]
    } := by
  simp [run, execute, denied]

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Refusal leaves the underlying semantic/architectural machine exactly at its pre-access value. -/
theorem denied_preserves_machine (denied : decision state.machine = .error reason) :
    (run (execute attempt decision) state).finalState.machine = state.machine := by
  simp [run, execute, denied, Outcome.finalState]

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Refusal extends rather than replaces the prior diagnostic history. -/
theorem denied_appends_exactly (denied : decision state.machine = .error reason) :
    (run (execute attempt decision) state).finalState.violations =
      state.violations ++ [{ attempt := attempt, reason := reason }] := by
  simp [run, execute, denied, Outcome.finalState]

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A refused access is observably non-clean even when it was the first access in the prefix. -/
theorem denied_not_clean (denied : decision state.machine = .error reason) :
    ¬ (run (execute attempt decision) state).Clean := by
  simp [run, execute, denied, Outcome.Clean, Outcome.finalState, State.Clean]

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Success preserves the complete prior audit, including any earlier diagnostic prefix. -/
theorem allowed_preserves_violations (allowed : decision state.machine = .ok (machine, value)) :
    (run (execute attempt decision) state).finalState.violations = state.violations := by
  simp [run, execute, allowed, Outcome.finalState]

end execute

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- One computation succeeds and leaves an empty audit from this exact clean-prefix state. -/
def SafeFrom (computation : Checked d Machine Value) (state : State d Machine) : Prop :=
  ∃ final value, run computation state = .allowed final value ∧ final.Clean

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Capability/frame-indexed no-bad-access certificate. Real lowering normally proves this form:
    the supplied entry invariant describes the authority state from which the access is valid. -/
def SafeUnder (precondition : State d Machine → Prop)
    (computation : Checked d Machine Value) : Prop :=
  ∀ state, state.Clean → precondition state → SafeFrom computation state

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Unconditional compositional no-bad-access certificate. It is deliberately stronger than
    final-log emptiness: the computation must succeed from every clean input and remain clean. -/
def Safe (computation : Checked d Machine Value) : Prop :=
  ∀ state, state.Clean → SafeFrom computation state

namespace Safe

variable {d : Domains} {Machine : Type v} {Value : Type w} {Result : Type x}

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
theorem pure (value : Value) : Safe (pure (d := d) (Machine := Machine) value) := by
  intro state clean
  exact ⟨state, value, rfl, clean⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- The common lowering proof scales by composition: once each checked fragment is safe, their
    sequencing carries no per-instruction audit bookkeeping. -/
theorem bind {first : Checked d Machine Value} {next : Value → Checked d Machine Result}
    (firstSafe : Safe first) (nextSafe : ∀ value, Safe (next value)) :
    Safe (bind first next) := by
  intro state clean
  obtain ⟨middle, value, firstResult, middleClean⟩ := firstSafe state clean
  obtain ⟨final, result, nextResult, finalClean⟩ := nextSafe value middle middleClean
  exact ⟨final, result,
    by
      change (match run first state with
        | .allowed state value => run (next value) state
        | .denied state => .denied state) = .allowed final result
      rw [firstResult]
      simpa using nextResult,
    finalClean⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A profile decision that is constructively successful for every machine automatically yields
    a safe checked access; the audit plumbing itself creates no lowering burden. -/
theorem execute (attempt : Attempt d)
    (decision : Machine → Except d.Reason (Machine × Value))
    (succeeds : ∀ machine, ∃ next value, decision machine = .ok (next, value)) :
    Safe (AccessAudit.execute attempt decision) := by
  intro state clean
  obtain ⟨next, value, success⟩ := succeeds state.machine
  exact ⟨{ machine := next, violations := state.violations }, value,
    AccessAudit.execute.of_ok success, clean⟩

end Safe

namespace SafeUnder

variable {d : Domains} {Machine : Type v} {Value : Type w} {Result : Type x}
  {precondition middleCondition : State d Machine → Prop}

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- An unconditional certificate discharges any weaker entry-indexed obligation. -/
theorem of_safe {computation : Checked d Machine Value} (safe : Safe computation) :
    SafeUnder precondition computation := by
  intro state clean _precondition
  exact safe state clean

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- A profile decision needs to succeed only under the selected clean entry invariant. -/
theorem execute (attempt : Attempt d)
    (decision : Machine → Except d.Reason (Machine × Value))
    (succeeds : ∀ state, state.Clean → precondition state →
      ∃ next value, decision state.machine = .ok (next, value)) :
    SafeUnder precondition (AccessAudit.execute attempt decision) := by
  intro state clean precondition
  obtain ⟨next, value, success⟩ := succeeds state clean precondition
  exact ⟨{ machine := next, violations := state.violations }, value,
    AccessAudit.execute.of_ok success, clean⟩

/- REF: docs/MEMORY_MODEL.md#62-authority-states -/
/-- Indexed sequential composition. The handoff is the semantic instruction/frame theorem; audit
    preservation itself is discharged once here rather than repeated by every lowering. -/
theorem bind {first : Checked d Machine Value} {next : Value → Checked d Machine Result}
    (firstSafe : SafeUnder precondition first)
    (nextSafe : ∀ value, SafeUnder middleCondition (next value))
    (handoff : ∀ initial middle value,
      initial.Clean → precondition initial →
      run first initial = .allowed middle value → middleCondition middle) :
    SafeUnder precondition (AccessAudit.bind first next) := by
  intro initial clean precondition
  obtain ⟨middle, value, firstResult, middleClean⟩ :=
    firstSafe initial clean precondition
  have middleCondition := handoff initial middle value clean precondition firstResult
  obtain ⟨final, result, nextResult, finalClean⟩ :=
    nextSafe value middle middleClean middleCondition
  exact ⟨final, result,
    by
      change (match run first initial with
        | .allowed state value => run (next value) state
        | .denied state => .denied state) = .allowed final result
      rw [firstResult]
      simpa using nextResult,
    finalClean⟩

end SafeUnder

end Gasm.MemoryModel.AccessAudit

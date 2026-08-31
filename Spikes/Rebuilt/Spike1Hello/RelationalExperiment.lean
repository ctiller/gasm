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

import Spikes.Rebuilt.Spike1Hello.Spec

/-!
# Isolated relational lowering experiment for rebuilt Spike 1

This namespace is deliberately spike-local and non-public. It tests the accepted proof shape without
freezing a shared Lean interface or creating an emission authority.
-/

namespace Spikes.Rebuilt.Spike1Hello.RelationalExperiment

open Spikes.Rebuilt.Spike1Hello

/-- Selected abstract basic-block location. -/
inductive Block where
  | acquireStdout
  | writeRemaining
  | terminal (observation : TerminalObservation)
deriving DecidableEq, Repr

/-- Lowered logical state. Handles, addresses and ABI storage are introduced only by the Windows
realization; this rung retains the source split needed for proof. -/
structure State where
  block : Block
  committed : List UInt8
  remaining : List UInt8
deriving DecidableEq, Repr

namespace TerminalObservation

def emitted : TerminalObservation → List UInt8
  | .success bytes => bytes
  | .fatal _ committed => committed

end TerminalObservation

def initial : State :=
  { block := .acquireStdout, committed := [], remaining := message }

/-- Source relation carried as ghost state across the selected blocks. -/
def State.Safe (state : State) : Prop :=
  match state.block with
  | .acquireStdout | .writeRemaining => state.committed ++ state.remaining = message
  | .terminal observation =>
      state.remaining = [] ∧ state.committed = TerminalObservation.emitted observation ∧
        Accepts observation

/-- A provider acceptance cannot be constructed without proving its exact requested-range bound. -/
structure AcceptedPrefix (remaining : List UInt8) where
  count : Nat
  bounded : count ≤ remaining.length

/-- Exact accepted prefix carried by a bounded provider result. -/
def AcceptedPrefix.bytes {remaining : List UInt8} (accepted : AcceptedPrefix remaining) : List UInt8 :=
  remaining.take accepted.count

/-- Provider-owned occurrence labels. Program invariants do not occur in these results. -/
inductive ProviderResponse where
  | stdoutAcquired
  | noStdout
  | accepted (count : Nat)
  | writeFailed
deriving DecidableEq, Repr

/-- One selected abstract lowering step. Short/zero writes remain below `writeAll`; only the terminal
blocks connect back to the precious root. -/
inductive Step : State → ProviderResponse → State → Prop where
  | stdoutAcquired {committed remaining} :
      Step { block := .acquireStdout, committed, remaining } .stdoutAcquired
        { block := .writeRemaining, committed, remaining }
  | noStdout :
      Step initial .noStdout
        { block := .terminal (.fatal .noStdout []), committed := [], remaining := [] }
  | acceptedShort {committed remaining} (accepted : AcceptedPrefix remaining)
      (short : accepted.count < remaining.length) :
      Step { block := .writeRemaining, committed, remaining } (.accepted accepted.count)
        { block := .writeRemaining
          committed := committed ++ accepted.bytes
          remaining := remaining.drop accepted.count }
  | acceptedAll {committed remaining} (accepted : AcceptedPrefix remaining)
      (all : accepted.count = remaining.length) :
      Step { block := .writeRemaining, committed, remaining } (.accepted accepted.count)
        { block := .terminal (.success (committed ++ remaining))
          committed := committed ++ remaining
          remaining := [] }
  | writeFailed {committed remaining} :
      Step { block := .writeRemaining, committed, remaining } .writeFailed
        { block := .terminal (.fatal .writeFailure committed)
          committed
          remaining := [] }

/-- Reflexive-transitive exact prefix relation. -/
inductive Prefix : State → State → Prop where
  | refl (state) : Prefix state state
  | tail {before middle after response} :
      Step before response middle → Prefix middle after → Prefix before after

/-- A provider-labelled finite execution. Its response list cannot be silently reselected. -/
inductive Execution : State → List ProviderResponse → State → Prop where
  | refl (state) : Execution state [] state
  | tail {before middle after response responses} :
      Step before response middle → Execution middle responses after →
        Execution before (response :: responses) after

theorem Execution.toPrefix {before responses after}
    (execution : Execution before responses after) : Prefix before after := by
  induction execution with
  | refl => exact .refl _
  | tail step _ ih => exact .tail step ih

theorem initial_safe : initial.Safe := by
  rfl

private theorem append_take_drop (left right : List UInt8) (count : Nat) :
    (left ++ right.take count) ++ right.drop count = left ++ right := by
  simp only [List.append_assoc, List.take_append_drop]

/-- Machine-derived local rule: every selected lowering step preserves the source invariant or
enters a root-accepted terminal block. -/
theorem Step.preserves {before after : State} {response : ProviderResponse}
    (step : Step before response after)
    (safe : before.Safe) : after.Safe := by
  cases step with
  | stdoutAcquired => exact safe
  | noStdout =>
      exact ⟨rfl, rfl, accepts_failure {
        error := .noStdout
        committed := []
        valid := rfl }⟩
  | acceptedShort accepted short =>
      simpa [State.Safe, AcceptedPrefix.bytes, append_take_drop] using safe
  | acceptedAll accepted all =>
      have split := safe
      simp only [State.Safe] at split
      refine ⟨rfl, rfl, ?_⟩
      simpa [split] using accepts_success
  | writeFailed =>
      simp only [State.Safe] at safe
      exact ⟨rfl, rfl, accepts_failure {
        error := .writeFailure
        committed := _
        valid := ⟨_, safe⟩ }⟩

/-- Prefix preservation is structural and does not assume provider progress. -/
theorem Prefix.preserves {before after : State} (execution : Prefix before after)
    (safe : before.Safe) : after.Safe := by
  induction execution with
  | refl => exact safe
  | tail step _ ih => exact ih (step.preserves safe)

/-- Every prefix from the exact initial state is safe. -/
theorem Prefix.safe {after : State} (execution : Prefix initial after) : after.Safe :=
  execution.preserves initial_safe

def State.IsTerminal (state : State) : Prop :=
  ∃ observation, state.block = .terminal observation

/-- Terminal executions alone refine the precious terminal root. -/
theorem terminal_sound {after : State} (execution : Prefix initial after)
    (terminal : after.IsTerminal) : ∃ observation, after.block = .terminal observation ∧
      Accepts observation := by
  rcases terminal with ⟨observation, terminal_block⟩
  have safe := execution.safe
  rw [State.Safe, terminal_block] at safe
  exact ⟨observation, terminal_block, safe.2.2⟩

/-- Oversized acceptance is excluded before a provider result can become a lowering step. -/
theorem oversized_not_admitted (remaining : List UInt8) (count : Nat)
    (oversized : remaining.length < count) : ¬ count ≤ remaining.length := by
  omega

/-- A sound provider cannot launder an oversized successful count through the common machine fatal
label: there is no abstract lowering step for that occurrence. -/
theorem oversized_success_has_no_step {committed remaining after} (count : Nat)
    (oversized : remaining.length < count) :
    ¬ Step { block := .writeRemaining, committed, remaining } (.accepted count) after := by
  intro step
  cases step <;> omega

/-- Finite provider response traces that force a terminal write result. Positive short writes make
progress; failure terminates; an all-write terminates. Zero writes deliberately have no inhabitant. -/
inductive CompleteWritePlan : List UInt8 → List ProviderResponse → Prop where
  | fail {remaining} : remaining ≠ [] → CompleteWritePlan remaining [.writeFailed]
  | all {remaining count} : 0 < count → count = remaining.length →
      CompleteWritePlan remaining [.accepted count]
  | short {remaining count rest} : 0 < count → count < remaining.length →
      CompleteWritePlan (remaining.drop count) rest →
      CompleteWritePlan remaining (.accepted count :: rest)

/-- A complete eligible provider plan includes the acquisition result, so coverage cannot silently
choose a different acquisition branch. -/
inductive EligiblePlan : List ProviderResponse → Prop where
  | noStdout : EligiblePlan [.noStdout]
  | write {responses} : CompleteWritePlan message responses →
      EligiblePlan (.stdoutAcquired :: responses)

private theorem write_coverage {committed remaining responses}
    (split : committed ++ remaining = message) (plan : CompleteWritePlan remaining responses) :
    ∃ after,
      Execution { block := .writeRemaining, committed, remaining } responses after ∧
        after.IsTerminal := by
  cases plan with
  | fail remaining_nonempty =>
      let after : State :=
        { block := .terminal (.fatal .writeFailure committed), committed, remaining := [] }
      exact ⟨after, .tail .writeFailed (.refl after),
        ⟨.fatal .writeFailure committed, rfl⟩⟩
  | all positive all =>
      let accepted : AcceptedPrefix remaining := ⟨_, Nat.le_of_eq all⟩
      let after : State :=
        { block := .terminal (.success (committed ++ remaining))
          committed := committed ++ remaining
          remaining := [] }
      exact ⟨after, .tail (.acceptedAll accepted all) (.refl after),
        ⟨.success (committed ++ remaining), rfl⟩⟩
  | short positive short tail =>
      let accepted : AcceptedPrefix remaining := ⟨_, Nat.le_of_lt short⟩
      have next_split :
          (committed ++ accepted.bytes) ++ remaining.drop accepted.count = message := by
        simpa [AcceptedPrefix.bytes, append_take_drop] using split
      rcases write_coverage next_split tail with ⟨after, execution, terminal⟩
      exact ⟨after, .tail (.acceptedShort accepted short) execution, terminal⟩
termination_by responses.length

private theorem write_execution_terminal {committed remaining responses after}
    (plan : CompleteWritePlan remaining responses)
    (execution : Execution { block := .writeRemaining, committed, remaining } responses after) :
    after.IsTerminal := by
  induction plan generalizing committed after with
  | fail remaining_nonempty =>
      cases execution with
      | tail step rest =>
          cases step
          cases rest
          exact ⟨_, rfl⟩
  | all positive all =>
      cases execution with
      | tail step rest =>
          cases step <;> try omega
          cases rest
          exact ⟨_, rfl⟩
  | short positive short tail ih =>
      cases execution with
      | tail step rest =>
          cases step <;> try omega
          exact ih rest

/-- Negative control: supplying only the acquisition response cannot be reselected into a terminal
execution. In particular, coverage cannot ignore the caller's labelled response list. -/
theorem acquisition_only_is_not_terminal {after}
    (execution : Execution initial [.stdoutAcquired] after) : ¬ after.IsTerminal := by
  cases execution with
  | tail step rest =>
      cases step
      cases rest
      simp [State.IsTerminal]

/-- The experiment's private whole-program package. The fields deliberately separate universal
prefix safety, terminal refinement and conditional termination. -/
structure VerifiedExperiment where
  initialState : State
  initialExact : initialState = initial
  prefixSafety : ∀ {after}, Prefix initialState after → after.Safe
  terminalSoundness : ∀ {after}, Prefix initialState after → after.IsTerminal →
    ∃ observation, after.block = .terminal observation ∧ Accepts observation
  conditionalCoverage : ∀ responses, EligiblePlan responses →
    ∃ after, Execution initialState responses after ∧ after.IsTerminal
  conditionalTermination : ∀ {responses after}, EligiblePlan responses →
    Execution initialState responses after → after.IsTerminal

/-- The complete private package: universal safety/refinement plus conditional progress. -/
def spike1VerifiedExperiment : VerifiedExperiment where
  initialState := initial
  initialExact := rfl
  prefixSafety := fun execution => execution.safe
  terminalSoundness := terminal_sound
  conditionalCoverage := by
    intro responses plan
    cases plan with
    | noStdout =>
        let after : State :=
          { block := .terminal (.fatal .noStdout []), committed := [], remaining := [] }
        exact ⟨after, .tail .noStdout (.refl after), ⟨_, rfl⟩⟩
    | write writePlan =>
        rcases write_coverage (committed := []) (remaining := message) rfl writePlan with
          ⟨after, execution, terminal⟩
        exact ⟨after, .tail .stdoutAcquired execution, terminal⟩
  conditionalTermination := by
    intro responses after plan execution
    cases plan with
    | noStdout =>
        cases execution with
        | tail step rest =>
            cases step
            cases rest
            exact ⟨_, rfl⟩
    | write writePlan =>
        cases execution with
        | tail step rest =>
            cases step
            exact write_execution_terminal writePlan rest

end Spikes.Rebuilt.Spike1Hello.RelationalExperiment

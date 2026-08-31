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

/-- One selected abstract lowering step. Short/zero writes remain below `writeAll`; only the terminal
blocks connect back to the precious root. -/
inductive Step : State → State → Prop where
  | stdoutAcquired {committed remaining} :
      Step { block := .acquireStdout, committed, remaining }
        { block := .writeRemaining, committed, remaining }
  | writeComplete {committed} :
      Step { block := .writeRemaining, committed, remaining := [] }
        { block := .terminal (.success committed), committed, remaining := [] }
  | noStdout :
      Step initial
        { block := .terminal (.fatal .noStdout []), committed := [], remaining := [] }
  | acceptedShort {committed remaining} (accepted : AcceptedPrefix remaining)
      (short : accepted.count < remaining.length) :
      Step { block := .writeRemaining, committed, remaining }
        { block := .writeRemaining
          committed := committed ++ accepted.bytes
          remaining := remaining.drop accepted.count }
  | acceptedAll {committed remaining} (accepted : AcceptedPrefix remaining)
      (all : accepted.count = remaining.length) :
      Step { block := .writeRemaining, committed, remaining }
        { block := .terminal (.success (committed ++ remaining))
          committed := committed ++ remaining
          remaining := [] }
  | writeFailed {committed remaining} (committed_prefix : committed.IsPrefix message) :
      Step { block := .writeRemaining, committed, remaining }
        { block := .terminal (.fatal .writeFailure committed)
          committed
          remaining := [] }

/-- Reflexive-transitive exact prefix relation. -/
inductive Prefix : State → State → Prop where
  | refl (state) : Prefix state state
  | tail {before middle after} : Step before middle → Prefix middle after → Prefix before after

theorem initial_safe : initial.Safe := by
  rfl

private theorem append_take_drop (left right : List UInt8) (count : Nat) :
    (left ++ right.take count) ++ right.drop count = left ++ right := by
  simp only [List.append_assoc, List.take_append_drop]

/-- Machine-derived local rule: every selected lowering step preserves the source invariant or
enters a root-accepted terminal block. -/
theorem Step.preserves {before after : State} (step : Step before after)
    (safe : before.Safe) : after.Safe := by
  cases step with
  | stdoutAcquired => exact safe
  | writeComplete =>
      simp only [State.Safe, List.append_nil] at safe
      constructor
      · rfl
      constructor
      · rfl
      · rw [safe]
        exact accepts_success
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
  | writeFailed committed_prefix =>
      exact ⟨rfl, rfl, accepts_failure {
        error := .writeFailure
        committed := _
        valid := committed_prefix }⟩

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

/-- A finite response plan used only for the separate conditional-termination theorem. -/
inductive Response where
  | accepted (count : Nat)
  | failed
deriving DecidableEq, Repr

/-- Exact progress premise for a finite plan: each accepted response is positive and bounded by the
then-current remaining bytes, or the plan ends in fatal failure. -/
inductive ProgressPlan : List UInt8 → List Response → Prop where
  | complete : ProgressPlan [] []
  | fail {remaining} : remaining ≠ [] → ProgressPlan remaining [.failed]
  | accept {remaining count rest}
      (positive : 0 < count) (bounded : count ≤ remaining.length)
      (tail : ProgressPlan (remaining.drop count) rest) :
      ProgressPlan remaining (.accepted count :: rest)

private theorem write_progress {committed remaining plan}
    (split : committed ++ remaining = message) (progress : ProgressPlan remaining plan) :
    ∃ after,
      Prefix { block := .writeRemaining, committed, remaining } after ∧ after.IsTerminal := by
  cases progress with
  | complete =>
      let after : State :=
        { block := .terminal (.success committed), committed, remaining := [] }
      exact ⟨after, .tail .writeComplete (.refl after), ⟨.success committed, rfl⟩⟩
  | fail remaining_nonempty =>
      have committed_prefix : committed.IsPrefix message := ⟨remaining, split⟩
      let after : State :=
        { block := .terminal (.fatal .writeFailure committed), committed, remaining := [] }
      exact ⟨after, .tail (.writeFailed committed_prefix) (.refl after),
        ⟨.fatal .writeFailure committed, rfl⟩⟩
  | accept positive bounded tail =>
      let accepted : AcceptedPrefix remaining := ⟨_, bounded⟩
      by_cases all : accepted.count = remaining.length
      · let after : State :=
          { block := .terminal (.success (committed ++ remaining))
            committed := committed ++ remaining
            remaining := [] }
        exact ⟨after, .tail (.acceptedAll accepted all) (.refl after),
          ⟨.success (committed ++ remaining), rfl⟩⟩
      · have short : accepted.count < remaining.length := Nat.lt_of_le_of_ne bounded all
        have next_split :
            (committed ++ accepted.bytes) ++ remaining.drop accepted.count = message := by
          simpa [AcceptedPrefix.bytes, append_take_drop] using split
        rcases write_progress next_split tail with ⟨after, execution, terminal⟩
        exact ⟨after, .tail (.acceptedShort accepted short) execution, terminal⟩
termination_by plan.length

/-- The experiment's private whole-program package. The fields deliberately separate universal
prefix safety, terminal refinement and conditional termination. -/
structure VerifiedExperiment where
  initialState : State
  initialExact : initialState = initial
  prefixSafety : ∀ {after}, Prefix initialState after → after.Safe
  terminalSoundness : ∀ {after}, Prefix initialState after → after.IsTerminal →
    ∃ observation, after.block = .terminal observation ∧ Accepts observation
  progressClaim : ∀ plan, ProgressPlan message plan →
    ∃ after, Prefix initialState after ∧ after.IsTerminal

/-- The complete private package: universal safety/refinement plus conditional progress. -/
def spike1VerifiedExperiment : VerifiedExperiment where
  initialState := initial
  initialExact := rfl
  prefixSafety := fun execution => execution.safe
  terminalSoundness := terminal_sound
  progressClaim := by
    intro plan progress
    rcases write_progress (committed := []) (remaining := message) rfl progress with
      ⟨after, execution, terminal⟩
    exact ⟨after, .tail .stdoutAcquired execution, terminal⟩

end Spikes.Rebuilt.Spike1Hello.RelationalExperiment

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

import Init

/-!
A dependency-light fold which stops at the first refused input.

Refusal carries no successor state, so it is atomic at this abstraction boundary.
The result retains the accepted prefix, the first refused input, and the untouched
tail. Consumers can therefore state conservation and first-refusal laws without
reconstructing a prefix split around an `Option` result.
-/

namespace Stdlib

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- The result of attempting one fold step. A refused step cannot commit a successor state. -/
inductive FallibleStep (State : Type u) (Error : Type v) where
  | accepted (next : State)
  | refused (error : Error)

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- Exact boundary evidence returned by a finite fallible fold. -/
inductive FallibleFoldResult (State : Type u) (Input : Type v) (Error : Type w) where
  | completed (state : State) (accepted : List Input)
  | refused (state : State) (accepted : List Input)
      (first : Input) (untouchedTail : List Input) (error : Error)

namespace FallibleFoldResult

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- The state after every committed step and before any refused step. -/
def state : FallibleFoldResult State Input Error → State
  | .completed state _ => state
  | .refused state _ _ _ _ => state

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- Inputs whose steps committed, in original order. -/
def accepted : FallibleFoldResult State Input Error → List Input
  | .completed _ accepted => accepted
  | .refused _ accepted _ _ _ => accepted

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- Inputs not committed. On refusal this begins with the refused input. -/
def remainder : FallibleFoldResult State Input Error → List Input
  | .completed _ _ => []
  | .refused _ _ first untouchedTail _ => first :: untouchedTail

end FallibleFoldResult

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- Fold in list order until every step accepts or the first step refuses. -/
def fallibleFold (step : State → Input → FallibleStep State Error)
    (initial : State) : List Input → FallibleFoldResult State Input Error
  | [] => .completed initial []
  | first :: tail =>
      match step initial first with
      | .refused error => .refused initial [] first tail error
      | .accepted next =>
          match fallibleFold step next tail with
          | .completed final accepted => .completed final (first :: accepted)
          | .refused final accepted refused untouchedTail error =>
              .refused final (first :: accepted) refused untouchedTail error

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- Immediate refusal commits neither the input nor a successor state. -/
theorem fallibleFold_cons_refused
    (step : State → Input → FallibleStep State Error)
    (initial : State) (first : Input) (tail : List Input) (error : Error)
    (refuses : step initial first = .refused error) :
    fallibleFold step initial (first :: tail) =
      .refused initial [] first tail error := by
  simp [fallibleFold, refuses]

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- One accepted step is retained at the head of the committed prefix. -/
theorem fallibleFold_cons_accepted
    (step : State → Input → FallibleStep State Error)
    (initial next : State) (first : Input) (tail : List Input)
    (accepts : step initial first = .accepted next) :
    fallibleFold step initial (first :: tail) =
      match fallibleFold step next tail with
      | .completed final accepted => .completed final (first :: accepted)
      | .refused final accepted refused untouchedTail error =>
          .refused final (first :: accepted) refused untouchedTail error := by
  simp [fallibleFold, accepts]

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- The committed prefix followed by the exact remainder reconstructs the input. -/
theorem fallibleFold_conservation
    (step : State → Input → FallibleStep State Error)
    (initial : State) (input : List Input) :
    let result := fallibleFold step initial input
    result.accepted ++ result.remainder = input := by
  induction input generalizing initial with
  | nil => simp [fallibleFold, FallibleFoldResult.accepted, FallibleFoldResult.remainder]
  | cons first tail ih =>
      simp only [fallibleFold]
      cases hstep : step initial first with
      | refused error =>
          simp [FallibleFoldResult.accepted, FallibleFoldResult.remainder]
      | accepted next =>
          simp only
          cases hfold : fallibleFold step next tail with
          | completed final accepted =>
              have tailConservation := ih next
              rw [hfold] at tailConservation
              simpa [FallibleFoldResult.accepted, FallibleFoldResult.remainder] using
                congrArg (List.cons first) tailConservation
          | refused final accepted refused untouchedTail error =>
              have tailConservation := ih next
              rw [hfold] at tailConservation
              simpa [FallibleFoldResult.accepted, FallibleFoldResult.remainder,
                List.append_assoc] using congrArg (List.cons first) tailConservation

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- A relation recording exactly the state transitions committed by an accepted prefix. -/
inductive FallibleAcceptedPrefix
    (step : State → Input → FallibleStep State Error) : State → List Input → State → Prop where
  | nil (state : State) : FallibleAcceptedPrefix step state [] state
  | cons (accepts : step initial first = .accepted next)
      (tail : FallibleAcceptedPrefix step next rest final) :
      FallibleAcceptedPrefix step initial (first :: rest) final

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- The reported committed prefix is backed by the exact accepted state-transition chain. -/
theorem fallibleFold_acceptedPrefix
    (step : State → Input → FallibleStep State Error)
    (initial : State) (input : List Input) :
    let result := fallibleFold step initial input
    FallibleAcceptedPrefix step initial result.accepted result.state := by
  induction input generalizing initial with
  | nil =>
      simp only [fallibleFold, FallibleFoldResult.accepted, FallibleFoldResult.state]
      exact .nil initial
  | cons first tail ih =>
      simp only [fallibleFold]
      cases hstep : step initial first with
      | refused error =>
          simp only [FallibleFoldResult.accepted, FallibleFoldResult.state]
          exact .nil initial
      | accepted next =>
          simp only
          cases hfold : fallibleFold step next tail with
          | completed final accepted =>
              have acceptedTail := ih next
              rw [hfold] at acceptedTail
              exact .cons hstep acceptedTail
          | refused final accepted refused untouchedTail error =>
              have acceptedTail := ih next
              rw [hfold] at acceptedTail
              exact .cons hstep acceptedTail

/- REF: docs/STDLIB_FACILITIES_PLAN.md#6-fallible-streaming-and-base-io -/
/-- A refused result names the actual first refused step after its accepted prefix. -/
theorem fallibleFold_refused_boundary
    (step : State → Input → FallibleStep State Error)
    (initial final : State) (input accepted : List Input)
    (first : Input) (untouchedTail : List Input) (error : Error)
    (resultEq : fallibleFold step initial input =
      .refused final accepted first untouchedTail error) :
    FallibleAcceptedPrefix step initial accepted final ∧
      step final first = .refused error ∧
      accepted ++ first :: untouchedTail = input := by
  induction input generalizing initial accepted with
  | nil => simp [fallibleFold] at resultEq
  | cons head tail ih =>
      cases hstep : step initial head with
      | refused refusal =>
          simp only [fallibleFold, hstep] at resultEq
          cases resultEq
          exact ⟨.nil final, hstep, rfl⟩
      | accepted next =>
          simp only [fallibleFold, hstep] at resultEq
          cases hfold : fallibleFold step next tail with
          | completed completedState committed => simp [hfold] at resultEq
          | refused refusedState committed refused untouched refusal =>
              simp only [hfold] at resultEq
              cases resultEq
              obtain ⟨prefixProof, boundary, conservation⟩ :=
                ih next committed hfold
              exact ⟨.cons hstep prefixProof, boundary, by simp [conservation]⟩

end Stdlib

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

import Gasm.Targets.WASI.ABI

namespace Gasm.Targets.WASI

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
/-- Replace the payload of a successful exit while preserving every other observable outcome.

This total, proof-free normalizer is deliberately separated from evaluator-backed proofs that a
particular outcome is impossible.  Consumers can use the constructor equations below without
reducing the computation which produced the observation or transporting a proof through a
dependent match. -/
def WasiObservable.normalizeSuccessfulExit
    (successful : List Event → WasiObservable Event) :
    WasiObservable Event → WasiObservable Event
  | .exited 0 events => successful events
  | observation => observation

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
@[simp] theorem WasiObservable.normalizeSuccessfulExit_completed
    (successful : List Event → WasiObservable Event) (events : List Event) :
    (WasiObservable.completed events).normalizeSuccessfulExit successful = .completed events := rfl

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
@[simp] theorem WasiObservable.normalizeSuccessfulExit_exited_zero
    (successful : List Event → WasiObservable Event) (events : List Event) :
    (WasiObservable.exited 0 events).normalizeSuccessfulExit successful = successful events := rfl

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
@[simp] theorem WasiObservable.normalizeSuccessfulExit_exited_nonzero
    (successful : List Event → WasiObservable Event) (code : UInt32) (events : List Event)
    (nonzero : code ≠ 0) :
    (WasiObservable.exited code events).normalizeSuccessfulExit successful = .exited code events := by
  simp [WasiObservable.normalizeSuccessfulExit, nonzero]

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
@[simp] theorem WasiObservable.normalizeSuccessfulExit_trapped
    (successful : List Event → WasiObservable Event) (events : List Event) :
    (WasiObservable.trapped events).normalizeSuccessfulExit successful = .trapped events := rfl

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
@[simp] theorem WasiObservable.normalizeSuccessfulExit_fuelExhausted
    (successful : List Event → WasiObservable Event) :
    (WasiObservable.fuelExhausted : WasiObservable Event).normalizeSuccessfulExit successful =
      .fuelExhausted := rfl

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
@[simp] theorem WasiObservable.normalizeSuccessfulExit_memoryExhausted
    (successful : List Event → WasiObservable Event) (requested available : Nat) :
    (WasiObservable.memoryExhausted requested available).normalizeSuccessfulExit successful =
      .memoryExhausted requested available := rfl

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
/-- Relate an abstract observation to its successful-exit normalization without unfolding the
    computation which produced it.  Consumers supply only the impossible fuel case and the exact
    successful payload; every other outcome is preserved by the constructor equations above. -/
theorem WasiObservable.refines_normalizeSuccessfulExit
    (successful : List Event → WasiObservable Event) (observation : WasiObservable Event)
    (notFuel : observation ≠ .fuelExhausted)
    (successCase : ∀ events, observation = .exited 0 events →
      .exited 0 events = successful events) :
    observation = observation.normalizeSuccessfulExit successful := by
  cases observation with
  | completed events => rfl
  | exited code events =>
      by_cases zero : code = 0
      · subst code
        simpa using successCase events rfl
      · simp [WasiObservable.normalizeSuccessfulExit, zero]
  | trapped events => rfl
  | fuelExhausted => exact (notFuel rfl).elim
  | memoryExhausted requested available => rfl

/- REF: docs/PROOF_TACTICS.md#prove-layers-then-compose -/
/-- Exclude observable fuel exhaustion by classifying an abstract run outcome once, rather than
    unfolding or case-splitting an evaluator invocation in every consumer proof. -/
theorem WasiRunOutcome.observable_ne_fuelExhausted
    (outcome : WasiRunOutcome)
    (notFuel : ∀ partialState, outcome ≠ .fuelExhausted partialState) :
    outcome.observable ≠ .fuelExhausted := by
  cases outcome with
  | completed state signal => simp [WasiRunOutcome.observable]
  | exited state code => simp [WasiRunOutcome.observable]
  | trapped state => simp [WasiRunOutcome.observable]
  | fuelExhausted partialState => exact (notFuel partialState rfl).elim
  | memoryExhausted state requested available => simp [WasiRunOutcome.observable]

end Gasm.Targets.WASI

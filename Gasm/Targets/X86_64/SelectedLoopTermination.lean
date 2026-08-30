import Gasm.Targets.X86_64.EventfulSegment

/-!
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

namespace Gasm.Targets.X86_64

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A selected bounded-loop step with a uniform upper bound on the number of production-runner
    transitions consumed by each pass.  The certificate still retains each pass's exact fuel;
    `maxFuel` is used only to prove that their structural composition fits an artifact's fixed
    runner budget.

    This is proof-producing adapter evidence, not an evaluator or execution authority.  A caller
    must supply an exact `SelectedPrefix` for every reachable pass. -/
structure SelectedFuelBoundedInvariantLoopStep {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (bound : Nat)
    (invariant : Nat → X86_64MachineState → List Event → Prop) where
  maxFuel : Nat
  run : ∀ completed state eventsRev,
    completed < bound → invariant completed state eventsRev →
      ∃ fuel final finalEventsRev emitted,
        0 < fuel ∧ fuel ≤ maxFuel ∧
        ProductionPrefix.SelectedPrefix selected indexed fuel state eventsRev
          final finalEventsRev emitted ∧
        invariant (completed + 1) final finalEventsRev

namespace SelectedFuelBoundedInvariantLoopStep

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Forget only the quantitative fuel bound, retaining the existing selected-loop interface. -/
theorem toSelectedBoundedInvariantLoopStep {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {bound : Nat}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (step : SelectedFuelBoundedInvariantLoopStep selected indexed bound invariant) :
    SelectedBoundedInvariantLoopStep selected indexed bound invariant where
  run completed state eventsRev within holds := by
    rcases step.run completed state eventsRev within holds with
      ⟨fuel, final, finalEventsRev, emitted, positive, _withinFuel, certificate, next⟩
    exact ⟨fuel, final, finalEventsRev, emitted, positive, certificate, next⟩

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Structurally iterate selected passes while retaining both the exact composed prefix and the
    arithmetic fact that its fuel is bounded by `iterations * maxFuel`. -/
theorem iterateFrom {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {bound : Nat}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (step : SelectedFuelBoundedInvariantLoopStep selected indexed bound invariant) :
    ∀ start iterations state eventsRev, start + iterations ≤ bound → invariant start state eventsRev →
      ∃ final finalEventsRev emitted totalFuel,
        ProductionPrefix.SelectedPrefix selected indexed totalFuel state eventsRev
          final finalEventsRev emitted ∧
        totalFuel ≤ iterations * step.maxFuel ∧
        invariant (start + iterations) final finalEventsRev := by
  intro start iterations
  induction iterations generalizing start with
  | zero =>
      intro state eventsRev _ holds
      exact ⟨state, eventsRev, [], 0, .nil _ _, by simp, holds⟩
  | succ iterations ih =>
      intro state eventsRev hbound holds
      rcases step.run start state eventsRev (by omega) holds with
        ⟨firstFuel, middle, middleEventsRev, firstEvents, _positive, firstBound,
          first, middleHolds⟩
      rcases ih (start + 1) middle middleEventsRev (by omega) middleHolds with
        ⟨final, finalEventsRev, secondEvents, secondFuel, second, secondBound, finalHolds⟩
      refine ⟨final, finalEventsRev, firstEvents ++ secondEvents, firstFuel + secondFuel,
        first.append second, ?_, ?_⟩
      · calc
          firstFuel + secondFuel ≤ step.maxFuel + iterations * step.maxFuel :=
            Nat.add_le_add firstBound secondBound
          _ = (iterations + 1) * step.maxFuel := by simp [Nat.add_mul, Nat.add_comm]
      · rw [show start + (iterations + 1) = start + 1 + iterations by omega]
        exact finalHolds

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Zero-based bounded-fuel selected iteration. -/
theorem iterate {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {bound : Nat}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (step : SelectedFuelBoundedInvariantLoopStep selected indexed bound invariant)
    (state : X86_64MachineState) (eventsRev : List Event)
    (holds : invariant 0 state eventsRev) :
    ∃ final finalEventsRev emitted totalFuel,
      ProductionPrefix.SelectedPrefix selected indexed totalFuel state eventsRev
        final finalEventsRev emitted ∧
      totalFuel ≤ bound * step.maxFuel ∧
      invariant bound final finalEventsRev := by
  simpa using step.iterateFrom 0 bound state eventsRev (by omega) holds

end SelectedFuelBoundedInvariantLoopStep

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The dependent result of constructing an exact selected exit tail. -/
structure SelectedProcessExitTailResult {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (state : X86_64MachineState) (eventsRev : List Event) where
  fuel : Nat
  final : X86_64MachineState
  finalEventsRev : List Event
  emitted : List Event
  code : UInt32
  certificate : ProductionPrefix.SelectedPrefix selected indexed fuel state eventsRev
    final finalEventsRev emitted
  exitStep : ProductionPrefix.SelectedPrefix.SelectedProcessExitStep
    (Event := Event) selected indexed final code

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A bounded selected tail from a loop invariant to the exact instruction immediately before a
    typed process-exit transition.  Platform adapters own this evidence; the structure does not
    infer an exit from a logical terminator or from falling off an instruction list. -/
structure SelectedProcessExitTail {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (invariant : X86_64MachineState → List Event → Prop) where
  maxFuel : Nat
  run : ∀ state eventsRev, invariant state eventsRev →
    { result : SelectedProcessExitTailResult selected indexed state eventsRev //
      result.fuel ≤ maxFuel }

namespace SelectedFuelBoundedInvariantLoopStep

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Compose a quantitatively bounded selected loop, a bounded selected exit tail, and the exact
    typed process-exit step into the unchanged fixed-budget termination proposition.

    Unused budget is justified only after the typed exit has occurred.  No padding transitions,
    evaluator result, or alternate termination predicate are introduced. -/
theorem selectedExecutionTerminates {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {allowHalted : Bool}
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {bound totalBudget : Nat}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (step : SelectedFuelBoundedInvariantLoopStep selected indexed bound invariant)
    (tail : SelectedProcessExitTail selected indexed (invariant bound))
    (initial : X86_64MachineState) (initialEventsRev : List Event)
    (holds : invariant 0 initial initialEventsRev)
    (budget : bound * step.maxFuel + tail.maxFuel + 1 ≤ totalBudget) :
    selectedExecutionTerminates (Event := Event) allowHalted selected indexed totalBudget initial = true := by
  rcases step.iterate initial initialEventsRev holds with
    ⟨loopFinal, loopEventsRev, loopEmitted, loopFuel, loopPrefix, loopBound, loopInvariant⟩
  rcases tail.run loopFinal loopEventsRev loopInvariant with
    ⟨result, tailBound⟩
  have usedWithin : loopFuel + result.fuel + 1 ≤ totalBudget := by
    have parts : loopFuel + result.fuel + 1 ≤
        bound * step.maxFuel + tail.maxFuel + 1 :=
      Nat.add_le_add (Nat.add_le_add loopBound tailBound) (Nat.le_refl 1)
    omega
  let slack := totalBudget - (loopFuel + result.fuel + 1)
  have totalBudget_eq : loopFuel + result.fuel + 1 + slack = totalBudget := by
    dsimp [slack]
    omega
  rw [← totalBudget_eq]
  exact (loopPrefix.append result.certificate).selectedExecutionTerminates_of_processExit_with_slack
    result.exitStep slack

end SelectedFuelBoundedInvariantLoopStep

end Gasm.Targets.X86_64

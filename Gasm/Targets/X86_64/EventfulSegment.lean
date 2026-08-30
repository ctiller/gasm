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

import Gasm.Targets.X86_64.CFGLinker
import Gasm.Targets.X86_64.Instructions.Call

namespace Gasm.Targets.X86_64

open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The closed CALL/SYSCALL families which may be deliberately handed to a selected host
    interceptor.  This is a classifier, not an authority grant: every use still supplies the
    exact interceptor result at the concrete post-step address. -/
inductive HostInterceptEncoding : X86_64Instr → Prop where
  | callRip (disp : Int32) : HostInterceptEncoding (call_rip disp)
  | callRel32 (disp : Int32) : HostInterceptEncoding (call_rel32 disp)
  | syscall : HostInterceptEncoding syscall_op

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Event accumulation uses the same reverse accumulator as `runProgramOutcomeLoop`. -/
def accumulateEvent (eventsRev : List Event) : Option Event → List Event
  | none => eventsRev
  | some event => event :: eventsRev

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The chronological delta contributed by one interceptor transition. -/
def emittedBy : Option Event → List Event
  | none => []
  | some event => [event]

theorem accumulateEvent_reverse (eventsRev : List Event) (event : Option Event) :
    (accumulateEvent eventsRev event).reverse = eventsRev.reverse ++ emittedBy event := by
  cases event <;> simp [accumulateEvent, emittedBy]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A target-owned, safe prefix of the production x86 runner.  Each constructor supplies an
    exact indexed fetch and then follows `runProgramOutcomeLoop`'s actual transition.  It admits
    only the selected ordinary, direct/conditional-branch, and host-intercepted CALL/SYSCALL
    forms; it does not classify, replay, or grant authority for any other instruction family. -/
inductive ProductionPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) :
    (fuel : Nat) → (initial : X86_64MachineState) → (initialEventsRev : List Event) →
    (final : X86_64MachineState) → (finalEventsRev : List Event) → (emitted : List Event) → Prop where
  | nil (state : X86_64MachineState) (eventsRev : List Event) :
      ProductionPrefix indexed 0 state eventsRev state eventsRev []
  | ordinary {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      (encoding : SequentialInstruction instruction)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : ProductionPrefix indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      ProductionPrefix indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | directBranch {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      (encoding : DirectJumpEncoding instruction)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : ProductionPrefix indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      ProductionPrefix indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | conditionalTaken {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      {kind : X86BranchCondition}
      (encoding : ConditionalJumpEncoding instruction kind)
      (chosen : kind.holds state)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : ProductionPrefix indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      ProductionPrefix indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | conditionalFallthrough {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      {kind : X86BranchCondition}
      (encoding : ConditionalJumpEncoding instruction kind)
      (notChosen : ¬ kind.holds state)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : ProductionPrefix indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      ProductionPrefix indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | hostIntercept {fuel : Nat} {state hooked final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr} {event : Option Event}
      (encoding : HostInterceptEncoding instruction)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (intercept : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = some (hooked, event))
      (safe : hooked.fault = none)
      (tail : ProductionPrefix indexed fuel hooked (accumulateEvent eventsRev event)
        final finalEventsRev emitted) :
      ProductionPrefix indexed (fuel + 1) state eventsRev final finalEventsRev
        (emittedBy event ++ emitted)

namespace ProductionPrefix

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- One selected host transition is a literal production evaluator step. -/
theorem runProgramOutcomeLoop_step_intercept {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state hooked : X86_64MachineState) (eventsRev : List Event)
    (instruction : X86_64Instr) (event : Option Event)
    (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
    (intercept : interceptor.interceptCall
      (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = some (hooked, event))
    (safe : hooked.fault = none) :
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeLoop indexed fuel hooked (accumulateEvent eventsRev event) := by
  cases event <;> simp [runProgramOutcomeLoop, lookup, nativeOutcomeTransition, intercept, safe,
    accumulateEvent]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A prefix consumes exactly its certified fuel in the actual production loop, then delegates
    all stop behaviour (return, halt, fault, or fuel exhaustion) to the unchanged continuation. -/
theorem run {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {fuel : Nat}
    {initial final : X86_64MachineState} {initialEventsRev finalEventsRev emitted : List Event}
    (certificate : ProductionPrefix indexed fuel initial initialEventsRev final finalEventsRev emitted)
    (continuationFuel : Nat) :
    runProgramOutcomeLoop indexed (fuel + continuationFuel) initial initialEventsRev =
      runProgramOutcomeLoop indexed continuationFuel final finalEventsRev := by
  induction certificate generalizing continuationFuel with
  | nil => simp
  | @ordinary localFuel localState localFinal localEvents localFinalEvents localEmitted localInstruction
      encoding lookup silent safe tail ih =>
      rw [show (localFuel + 1) + continuationFuel =
        (localFuel + continuationFuel) + 1 by omega]
      rw [runProgramOutcomeLoop_step_none indexed (localFuel + continuationFuel) _ _ _ lookup silent safe]
      exact ih continuationFuel
  | @directBranch localFuel localState localFinal localEvents localFinalEvents localEmitted localInstruction
      encoding lookup silent safe tail ih =>
      rw [show (localFuel + 1) + continuationFuel =
        (localFuel + continuationFuel) + 1 by omega]
      rw [runProgramOutcomeLoop_step_none indexed (localFuel + continuationFuel) _ _ _ lookup silent safe]
      exact ih continuationFuel
  | @conditionalTaken localFuel localState localFinal localEvents localFinalEvents localEmitted localInstruction localKind
      encoding chosen lookup silent safe tail ih =>
      rw [show (localFuel + 1) + continuationFuel =
        (localFuel + continuationFuel) + 1 by omega]
      rw [runProgramOutcomeLoop_step_none indexed (localFuel + continuationFuel) _ _ _ lookup silent safe]
      exact ih continuationFuel
  | @conditionalFallthrough localFuel localState localFinal localEvents localFinalEvents localEmitted localInstruction localKind
      encoding notChosen lookup silent safe tail ih =>
      rw [show (localFuel + 1) + continuationFuel =
        (localFuel + continuationFuel) + 1 by omega]
      rw [runProgramOutcomeLoop_step_none indexed (localFuel + continuationFuel) _ _ _ lookup silent safe]
      exact ih continuationFuel
  | @hostIntercept localFuel localState localHooked localFinal localEvents localFinalEvents localEmitted localInstruction localEvent
      encoding lookup intercept safe tail ih =>
      rw [show (localFuel + 1) + continuationFuel =
        (localFuel + continuationFuel) + 1 by omega]
      rw [runProgramOutcomeLoop_step_intercept indexed (localFuel + continuationFuel) _ _ _ _ _
        lookup intercept safe]
      exact ih continuationFuel

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The reverse accumulator exposes the prefix's chronological event delta exactly. -/
theorem events_reverse_append {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {fuel : Nat}
    {initial final : X86_64MachineState} {initialEventsRev finalEventsRev emitted : List Event}
    (certificate : ProductionPrefix indexed fuel initial initialEventsRev final finalEventsRev emitted) :
    finalEventsRev.reverse = initialEventsRev.reverse ++ emitted := by
  induction certificate with
  | nil => simp
  | ordinary _ _ _ _ tail ih => exact ih
  | directBranch _ _ _ _ tail ih => exact ih
  | conditionalTaken _ _ _ _ _ tail ih => exact ih
  | conditionalFallthrough _ _ _ _ _ tail ih => exact ih
  | hostIntercept _ _ _ _ tail ih =>
      rw [ih, accumulateEvent_reverse]
      simp [List.append_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A production prefix augmented with the exact selected-call evidence consumed by
    `selectedExecutionTerminates`.  This is deliberately a separate certificate from
    `ProductionPrefix`: ordinary production prefixes are useful for artifacts that permit a
    wider host surface, while a universal closed-program proof must account for every reached
    call boundary.  Its constructors still fetch and execute the real indexed instructions. -/
inductive SelectedPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) :
    (fuel : Nat) → (initial : X86_64MachineState) → (initialEventsRev : List Event) →
    (final : X86_64MachineState) → (finalEventsRev : List Event) → (emitted : List Event) → Prop where
  | nil (state : X86_64MachineState) (eventsRev : List Event) :
      SelectedPrefix selected indexed 0 state eventsRev state eventsRev []
  | ordinary {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      (encoding : SequentialInstruction instruction)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (selectedAt : selected (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = true)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : SelectedPrefix selected indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      SelectedPrefix selected indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | directBranch {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      (encoding : DirectJumpEncoding instruction)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (selectedAt : selected (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = true)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : SelectedPrefix selected indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      SelectedPrefix selected indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | conditionalTaken {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      {kind : X86BranchCondition}
      (encoding : ConditionalJumpEncoding instruction kind)
      (chosen : kind.holds state)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (selectedAt : selected (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = true)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : SelectedPrefix selected indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      SelectedPrefix selected indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | conditionalFallthrough {fuel : Nat} {state final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr}
      {kind : X86BranchCondition}
      (encoding : ConditionalJumpEncoding instruction kind)
      (notChosen : ¬ kind.holds state)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (selectedAt : selected (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = true)
      (silent : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = none)
      (safe : (X86_64Instruction.step instruction state).fault = none)
      (tail : SelectedPrefix selected indexed fuel (X86_64Instruction.step instruction state) eventsRev
        final finalEventsRev emitted) :
      SelectedPrefix selected indexed (fuel + 1) state eventsRev final finalEventsRev emitted
  | hostIntercept {fuel : Nat} {state hooked final : X86_64MachineState}
      {eventsRev finalEventsRev emitted : List Event} {instruction : X86_64Instr} {event : Option Event}
      (encoding : HostInterceptEncoding instruction)
      (lookup : instructionAtRipIndexed indexed state.rip = some instruction)
      (selectedAt : selected (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = true)
      (intercept : interceptor.interceptCall
        (X86_64Instruction.step instruction state).rip
        (X86_64Instruction.step instruction state) = some (hooked, event))
      (safe : hooked.fault = none)
      (tail : SelectedPrefix selected indexed fuel hooked (accumulateEvent eventsRev event)
        final finalEventsRev emitted) :
      SelectedPrefix selected indexed (fuel + 1) state eventsRev final finalEventsRev
        (emittedBy event ++ emitted)

namespace SelectedPrefix

/-- Forgetting selected-call side conditions yields the ordinary production-prefix certificate. -/
theorem toProductionPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {fuel : Nat}
    {initial final : X86_64MachineState} {initialEventsRev finalEventsRev emitted : List Event}
    (certificate : SelectedPrefix selected indexed fuel initial initialEventsRev final finalEventsRev emitted) :
    ProductionPrefix indexed fuel initial initialEventsRev final finalEventsRev emitted := by
  induction certificate with
  | nil state eventsRev => exact .nil state eventsRev
  | ordinary encoding lookup _ silent safe tail ih =>
      exact .ordinary encoding lookup silent safe ih
  | directBranch encoding lookup _ silent safe tail ih =>
      exact .directBranch encoding lookup silent safe ih
  | conditionalTaken encoding chosen lookup _ silent safe tail ih =>
      exact .conditionalTaken encoding chosen lookup silent safe ih
  | conditionalFallthrough encoding notChosen lookup _ silent safe tail ih =>
      exact .conditionalFallthrough encoding notChosen lookup silent safe ih
  | hostIntercept encoding lookup _ intercept safe tail ih =>
      exact .hostIntercept encoding lookup intercept safe ih

/-- A selected prefix unfolds the executable selected-call checker one certified instruction at a
    time.  It relates the checker to the unchanged continuation rather than replaying a closed
    evaluator. -/
theorem selectedExecutionTerminates_run {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {allowHalted : Bool} {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {fuel : Nat}
    {initial final : X86_64MachineState} {initialEventsRev finalEventsRev emitted : List Event}
    (certificate : SelectedPrefix selected indexed fuel initial initialEventsRev final finalEventsRev emitted)
    (continuationFuel : Nat) :
    selectedExecutionTerminates (Event := Event) allowHalted selected indexed
      (fuel + continuationFuel) initial =
      selectedExecutionTerminates (Event := Event) allowHalted selected indexed
        continuationFuel final := by
  induction certificate generalizing continuationFuel with
  | nil => simp
  | ordinary encoding lookup selectedAt silent safe tail ih =>
      simp only [Nat.add_assoc, Nat.add_comm 1 continuationFuel]
      simp only [selectedExecutionTerminates, lookup, selectedAt, nativeOutcomeTransition, silent, safe]
      exact ih continuationFuel
  | directBranch encoding lookup selectedAt silent safe tail ih =>
      simp only [Nat.add_assoc, Nat.add_comm 1 continuationFuel]
      simp only [selectedExecutionTerminates, lookup, selectedAt, nativeOutcomeTransition, silent, safe]
      exact ih continuationFuel
  | conditionalTaken encoding chosen lookup selectedAt silent safe tail ih =>
      simp only [Nat.add_assoc, Nat.add_comm 1 continuationFuel]
      simp only [selectedExecutionTerminates, lookup, selectedAt, nativeOutcomeTransition, silent, safe]
      exact ih continuationFuel
  | conditionalFallthrough encoding notChosen lookup selectedAt silent safe tail ih =>
      simp only [Nat.add_assoc, Nat.add_comm 1 continuationFuel]
      simp only [selectedExecutionTerminates, lookup, selectedAt, nativeOutcomeTransition, silent, safe]
      exact ih continuationFuel
  | hostIntercept encoding lookup selectedAt intercept safe tail ih =>
      simp only [Nat.add_assoc, Nat.add_comm 1 continuationFuel]
      simp only [selectedExecutionTerminates, lookup, selectedAt, nativeOutcomeTransition, intercept, safe]
      exact ih continuationFuel

/-- Appending one selected typed process-exit transition turns a structural selected prefix into
    the executable termination certificate required by universal artifact verification. -/
theorem selectedExecutionTerminates_of_processExit {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {allowHalted : Bool} {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {fuel : Nat}
    {initial final : X86_64MachineState} {initialEventsRev finalEventsRev emitted : List Event}
    (certificate : SelectedPrefix selected indexed fuel initial initialEventsRev final finalEventsRev emitted)
    {instruction : X86_64Instr} {code : UInt32}
    (lookup : instructionAtRipIndexed indexed final.rip = some instruction)
    (selectedAt : selected (X86_64Instruction.step instruction final).rip
      (X86_64Instruction.step instruction final) = true)
    (exits : (nativeOutcomeTransition (Event := Event) instruction final []).1.fault =
      some (.processExit code)) :
    selectedExecutionTerminates (Event := Event) allowHalted selected indexed (fuel + 1) initial = true := by
  rw [certificate.selectedExecutionTerminates_run 1]
  simp [selectedExecutionTerminates, lookup, selectedAt, exits]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A selected typed process exit remains terminal when the caller supplies unused fuel after the
    exit transition.  This lets a structurally composed prefix discharge a production artifact's
    fixed fuel budget without padding the certified instruction stream. -/
theorem selectedExecutionTerminates_of_processExit_with_slack {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {allowHalted : Bool} {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {fuel : Nat}
    {initial final : X86_64MachineState} {initialEventsRev finalEventsRev emitted : List Event}
    (certificate : SelectedPrefix selected indexed fuel initial initialEventsRev final finalEventsRev emitted)
    {instruction : X86_64Instr} {code : UInt32}
    (lookup : instructionAtRipIndexed indexed final.rip = some instruction)
    (selectedAt : selected (X86_64Instruction.step instruction final).rip
      (X86_64Instruction.step instruction final) = true)
    (exits : (nativeOutcomeTransition (Event := Event) instruction final []).1.fault =
      some (.processExit code))
    (slack : Nat) :
    selectedExecutionTerminates (Event := Event) allowHalted selected indexed
      (fuel + 1 + slack) initial = true := by
  rw [show fuel + 1 + slack = fuel + (slack + 1) by omega]
  rw [certificate.selectedExecutionTerminates_run (slack + 1)]
  simp [selectedExecutionTerminates, lookup, selectedAt, exits]

end SelectedPrefix

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Composing certified prefixes preserves the exact final machine state, reverse accumulator,
    and every native stop reason supplied by the continuation. -/
theorem run_compose {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {firstFuel secondFuel continuationFuel : Nat}
    {initial middle final : X86_64MachineState}
    {initialEventsRev middleEventsRev finalEventsRev firstEvents secondEvents : List Event}
    (first : ProductionPrefix indexed firstFuel initial initialEventsRev middle middleEventsRev firstEvents)
    (second : ProductionPrefix indexed secondFuel middle middleEventsRev final finalEventsRev secondEvents) :
    runProgramOutcomeLoop indexed (firstFuel + secondFuel + continuationFuel) initial initialEventsRev =
      runProgramOutcomeLoop indexed continuationFuel final finalEventsRev := by
  rw [show firstFuel + secondFuel + continuationFuel =
    firstFuel + (secondFuel + continuationFuel) by omega]
  rw [first.run (secondFuel + continuationFuel), second.run continuationFuel]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The event delta of two composed production prefixes is chronological append. -/
theorem events_reverse_append_compose {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {firstFuel secondFuel : Nat}
    {initial middle final : X86_64MachineState}
    {initialEventsRev middleEventsRev finalEventsRev firstEvents secondEvents : List Event}
    (first : ProductionPrefix indexed firstFuel initial initialEventsRev middle middleEventsRev firstEvents)
    (second : ProductionPrefix indexed secondFuel middle middleEventsRev final finalEventsRev secondEvents) :
    finalEventsRev.reverse = initialEventsRev.reverse ++ (firstEvents ++ secondEvents) := by
  rw [second.events_reverse_append, first.events_reverse_append]
  simp [List.append_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A reusable invariant-preserving production loop step.  Spike adapters provide certificates
    only for their reachable selected forms; unrelated program paths need no setup or proof. -/
structure InvariantLoopStep {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (invariant : X86_64MachineState → List Event → Prop) where
  fuel : Nat
  run : ∀ state eventsRev, invariant state eventsRev →
    ∃ final finalEventsRev emitted,
      ProductionPrefix indexed fuel state eventsRev final finalEventsRev emitted ∧
      invariant final finalEventsRev

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Iterate an invariant loop step without inventing a graph evaluator: the conclusion is an
    exact equality to the production runner and records the total fuel and event delta. -/
theorem InvariantLoopStep.iterate {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)}
    {invariant : X86_64MachineState → List Event → Prop}
    (step : InvariantLoopStep indexed invariant) :
    ∀ (_iterations : Nat) state eventsRev, invariant state eventsRev →
      ∃ final finalEventsRev emitted totalFuel,
        invariant final finalEventsRev ∧
        finalEventsRev.reverse = eventsRev.reverse ++ emitted ∧
        ∀ continuationFuel,
          runProgramOutcomeLoop indexed (totalFuel + continuationFuel) state eventsRev =
            runProgramOutcomeLoop indexed continuationFuel final finalEventsRev := by
  intro iterations
  induction iterations with
  | zero =>
      intro state eventsRev holds
      exact ⟨state, eventsRev, [], 0, holds, by simp, by simp⟩
  | succ iterations ih =>
      intro state eventsRev holds
      rcases step.run state eventsRev holds with ⟨middle, middleEventsRev, firstEvents, first, middleHolds⟩
      rcases ih middle middleEventsRev middleHolds with
        ⟨final, finalEventsRev, secondEvents, secondFuel, finalHolds, events, runs⟩
      refine ⟨final, finalEventsRev, firstEvents ++ secondEvents, step.fuel + secondFuel,
        finalHolds, ?_, ?_⟩
      · rw [events, first.events_reverse_append]
        simp [List.append_assoc]
      · intro continuationFuel
        rw [show (step.fuel + secondFuel) + continuationFuel =
          step.fuel + (secondFuel + continuationFuel) by omega]
        rw [first.run (secondFuel + continuationFuel), runs continuationFuel]

end ProductionPrefix

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A bounded production loop whose selected pass may consume a different number of instructions
    on different iterations.  The bound is part of the contract: callers prove only reachable
    passes, while the conclusion is still an equality for the unmodified production runner.

    This is deliberately distinct from `InvariantLoopStep`: decimal codecs, streaming requests,
    and resource-recovery paths often have value-dependent work per pass.  Requiring a fake
    constant fuel for those paths would either overstate what an adapter proves or force it to
    pad the actual instruction stream. -/
structure BoundedInvariantLoopStep {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (bound : Nat)
    (invariant : Nat → X86_64MachineState → List Event → Prop) where
  run : ∀ completed state eventsRev,
    completed < bound → invariant completed state eventsRev →
      ∃ fuel final finalEventsRev emitted,
        ProductionPrefix indexed fuel state eventsRev final finalEventsRev emitted ∧
        invariant (completed + 1) final finalEventsRev

namespace BoundedInvariantLoopStep

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Compose a bounded, variable-fuel loop structurally.  Its event and outcome equations are
    inherited from `ProductionPrefix`; no parallel evaluator and no global fixed fuel bound are
    introduced. -/
theorem iterateFrom {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {bound : Nat}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (step : BoundedInvariantLoopStep indexed bound invariant) :
    ∀ start iterations state eventsRev, start + iterations ≤ bound → invariant start state eventsRev →
      ∃ final finalEventsRev emitted totalFuel,
        invariant (start + iterations) final finalEventsRev ∧
        finalEventsRev.reverse = eventsRev.reverse ++ emitted ∧
        ∀ continuationFuel,
          runProgramOutcomeLoop indexed (totalFuel + continuationFuel) state eventsRev =
            runProgramOutcomeLoop indexed continuationFuel final finalEventsRev := by
  intro start iterations
  induction iterations generalizing start with
  | zero =>
      intro state eventsRev _ holds
      exact ⟨state, eventsRev, [], 0, holds, by simp, by simp⟩
  | succ iterations ih =>
      intro state eventsRev hbound holds
      rcases step.run start state eventsRev (by omega) holds with
        ⟨firstFuel, middle, middleEventsRev, firstEvents, first, middleHolds⟩
      rcases ih (start + 1) middle middleEventsRev (by omega) middleHolds with
        ⟨final, finalEventsRev, secondEvents, secondFuel, finalHolds, events, runs⟩
      refine ⟨final, finalEventsRev, firstEvents ++ secondEvents, firstFuel + secondFuel,
        ?_, ?_, ?_⟩
      · rw [show start + (iterations + 1) = start + 1 + iterations by omega]
        exact finalHolds
      · rw [events, first.events_reverse_append]
        simp [List.append_assoc]
      · intro continuationFuel
        rw [show (firstFuel + secondFuel) + continuationFuel =
          firstFuel + (secondFuel + continuationFuel) by omega]
        rw [first.run (secondFuel + continuationFuel), runs continuationFuel]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The conventional zero-based view of `iterateFrom`, used by fixed-size native drivers. -/
theorem iterate {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {bound : Nat}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (step : BoundedInvariantLoopStep indexed bound invariant)
    (state : X86_64MachineState) (eventsRev : List Event)
    (holds : invariant 0 state eventsRev) :
    ∃ final finalEventsRev emitted totalFuel,
      invariant bound final finalEventsRev ∧
      finalEventsRev.reverse = eventsRev.reverse ++ emitted ∧
      ∀ continuationFuel,
          runProgramOutcomeLoop indexed (totalFuel + continuationFuel) state eventsRev =
          runProgramOutcomeLoop indexed continuationFuel final finalEventsRev := by
  simpa using step.iterateFrom 0 bound state eventsRev (by omega) holds

end BoundedInvariantLoopStep

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/- A small executable-proof fixture: a not-taken JE fetches the following SYSCALL, whose selected
    production interceptor emits one event.  It is intentionally a branch-plus-event example,
    not a synthetic relation with no production lookup or host transition. -/
namespace EventfulSegmentFixture

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
inductive Event where
  | syscall
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
def initial : X86_64MachineState :=
  { rip := 0, gprs := fun _ => 0, flags := 0, memory := X86_64Mem.zero }

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
def hooked (state : X86_64MachineState) : X86_64MachineState := { state with rip := 4 }

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
@[instance_reducible] def fixtureInterceptor : ExternalCallInterceptor X86_64 Event where
  interceptCall address state :=
    if address == linuxSyscallEntry then some (hooked state, some .syscall) else none

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
local instance : ExternalCallInterceptor X86_64 Event := fixtureInterceptor

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
def indexed : List (UInt64 × X86_64Instr) :=
  indexInstructions 0 [je_rel8 0, syscall_op]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
def afterBranch : X86_64MachineState := { initial with rip := 2 }

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem je_step : X86_64Instruction.step (je_rel8 0) initial = afterBranch := by
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem je_lookup : instructionAtRipIndexed indexed initial.rip = some (je_rel8 0) := by
  unfold indexed indexInstructions indexInstructions.loop instructionAtRipIndexed initial
  simp

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem je_silent : @ExternalCallInterceptor.interceptCall X86_64 Event fixtureInterceptor
    (X86_64Instruction.step (je_rel8 0) initial).rip
    (X86_64Instruction.step (je_rel8 0) initial) = none := by
  rw [je_step]
  change @ExternalCallInterceptor.interceptCall X86_64 Event fixtureInterceptor 2 afterBranch = none
  unfold fixtureInterceptor
  simp [linuxSyscallEntry]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
def fixtureFinal : X86_64MachineState :=
  hooked (X86_64Instruction.step syscall_op
    (X86_64Instruction.step (je_rel8 0) initial))

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem syscall_lookup : instructionAtRipIndexed indexed afterBranch.rip = some syscall_op := by
  change instructionAtRipIndexed [(0, je_rel8 0), (2, syscall_op)] 2 = some syscall_op
  simp [instructionAtRipIndexed]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem syscall_intercept : @ExternalCallInterceptor.interceptCall X86_64 Event fixtureInterceptor
    (X86_64Instruction.step syscall_op afterBranch).rip
    (X86_64Instruction.step syscall_op afterBranch) = some (fixtureFinal, some Event.syscall) := by
  rw [show fixtureFinal = hooked (X86_64Instruction.step syscall_op afterBranch) by
    unfold fixtureFinal
    rw [je_step]]
  unfold fixtureInterceptor
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem eventful_branch_prefix :
    ProductionPrefix indexed 2 initial [] fixtureFinal [Event.syscall] [Event.syscall] := by
  apply ProductionPrefix.conditionalFallthrough
    (encoding := ConditionalJumpEncoding.je8 0)
  · simp [X86BranchCondition.holds, initial, X86_64MachineState.zf]
  · exact je_lookup
  · exact je_silent
  · rw [je_step]
    rfl
  · refine ProductionPrefix.hostIntercept (encoding := HostInterceptEncoding.syscall)
      (hooked := fixtureFinal) (event := some Event.syscall) ?_ ?_ ?_ ?_
    · rw [je_step]
      exact syscall_lookup
    · rw [je_step]
      exact syscall_intercept
    · rfl
    · exact .nil _ _

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem eventful_branch_prefix_events :
    [Event.syscall].reverse = ([] : List Event).reverse ++ [Event.syscall] := by
  exact eventful_branch_prefix.events_reverse_append

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
theorem eventful_branch_runs_to_fuel_boundary :
    runProgramOutcomeLoop indexed 2 initial [] = .fuelExhausted fixtureFinal [Event.syscall] := by
  simpa [runProgramOutcomeLoop] using eventful_branch_prefix.run 0

end EventfulSegmentFixture

end Gasm.Targets.X86_64

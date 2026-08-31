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

import Gasm.Targets.X86_64.LocalBlockDischarge

/-!
# Closed production execution

This module closes an exact selected production prefix with one typed terminal transition.  It is
the reusable boundary between instruction/block proofs and platform program certificates: clients
retain the production instruction index, exact initial and final states, event accumulator, fuel,
and terminal outcome without peeling `runProgramOutcomeLoop` themselves.
-/

namespace Gasm.Targets.X86_64

open ProductionPrefix
open ProductionPrefix.SelectedPrefix

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- An exact selected body followed by one selected process-exit transition in the same production
instruction index.  `slack` records an artifact budget larger than the shortest certified run;
the production evaluator still stops at the terminal transition. -/
structure ClosedExecution {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (initial : X86_64MachineState) (initialEventsRev : List Event) where
  bodyFuel : Nat
  final : X86_64MachineState
  finalEventsRev : List Event
  emitted : List Event
  body : SelectedPrefix selected indexed bodyFuel initial initialEventsRev
    final finalEventsRev emitted
  exitCode : UInt32
  terminal : @SelectedProcessExitStep Event _ selected indexed final exitCode
  slack : Nat := 0

namespace ClosedExecution

variable {Event : Type} [ExternalCallInterceptor X86_64 Event]
  {selected : Gasm.Core.Address → X86_64MachineState → Bool}
  {indexed : List (UInt64 × X86_64Instr)}
  {initial : X86_64MachineState} {initialEventsRev : List Event}

/-- Exact artifact evaluator fuel certified by the body, terminal transition, and optional slack. -/
def fuel (execution : ClosedExecution selected indexed initial initialEventsRev) : Nat :=
  execution.bodyFuel + 1 + execution.slack

/-- The exact terminal production outcome, including final state and chronological events. -/
def outcome (execution : ClosedExecution selected indexed initial initialEventsRev) :
    NativeRunOutcome Event :=
  .terminated (.processExit execution.exitCode) execution.terminal.hooked
    (accumulateEvent execution.finalEventsRev execution.terminal.event).reverse

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Run the actual indexed production evaluator through the closed execution. -/
theorem run (execution : ClosedExecution selected indexed initial initialEventsRev) :
    runProgramOutcomeLoop indexed execution.fuel initial initialEventsRev = execution.outcome := by
  exact execution.body.runProgramOutcomeLoop_of_processExit_with_slack
    execution.terminal execution.slack

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- The same closed evidence discharges the selected-call termination checker. -/
theorem terminates (execution : ClosedExecution selected indexed initial initialEventsRev)
    (allowHalted : Bool) :
    selectedExecutionTerminates (Event := Event) allowHalted selected indexed
      execution.fuel initial = true := by
  exact execution.body.selectedExecutionTerminates_of_processExit_with_slack
    execution.terminal execution.slack

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- A typed process exit is admissible for every x86 platform halt policy. -/
theorem admissible (execution : ClosedExecution selected indexed initial initialEventsRev)
    (allowHalted : Bool) : execution.outcome.isAdmissible allowHalted := by
  simp [outcome, NativeRunOutcome.isAdmissible]

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Closed executions expose their observation without erasing the exact outcome certificate. -/
theorem observable (execution : ClosedExecution selected indexed initial initialEventsRev) :
    execution.outcome.observable =
      NativeObservable.processExited execution.exitCode
        (accumulateEvent execution.finalEventsRev execution.terminal.event).reverse := by
  rfl

/-- Convert closed execution evidence to the standard termination certificate consumed by
platform external-input framing.  The exact index is definitionally the artifact index built from
`baseRip` and `instructions`; no detached instruction list can be substituted. -/
def terminationCertificate
    (execution : ClosedExecution selected indexed initial initialEventsRev)
    (allowHalted : Bool) (baseRip : UInt64) (instructions : List X86_64Instr)
    (indexExact : indexed = indexInstructions baseRip instructions) :
    SelectedTerminationCertificate (Event := Event) allowHalted selected
      baseRip instructions initial := by
  subst indexed
  exact {
    fuel := execution.fuel
    verifies := execution.terminates allowHalted
  }

end ClosedExecution

end Gasm.Targets.X86_64

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

import Gasm.Targets.X86_64.DecimalSchedule
import Spikes.Spike2Fibonacci.Linux.DecimalRuntime

/-!
# Production-state decimal phase invariants for Linux Spike 2

The schedule invariant is intentionally an exact recursively-defined production state, rather
than a free decimal result assertion.  At every reachable pass it requires the actual stack or
output frame, fault-free execution, selected dispatcher authority, and the non-IAT ordinary-code
facts proved by `DecimalRuntime`.  Thus this adapter cannot synthesize a decimal transition: a
caller must establish every physical pass witness for the real `spike2Indexed` stream.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- Exact state after `completed` actual seven-instruction extraction passes. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
def spike2ExtractionIter (initial : X86_64MachineState) : Nat → X86_64MachineState
  | 0 => initial
  | completed + 1 => extractionFinal 236 (spike2ExtractionIter initial completed)

/-- Exact state after `completed` actual five-instruction reverse-write passes. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
def spike2WriteIter (initial : X86_64MachineState) : Nat → X86_64MachineState
  | 0 => initial
  | completed + 1 => writeFinal 243 (spike2WriteIter initial completed)

/-- A closed, stateful extraction witness for one production decimal formatting invocation.
`ordinary` is the explicitly stateful Linux/Win32 dispatcher frame; it cannot be replaced by a
RIP-only claim. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
structure Spike2ExtractionLoopWitness (value : UInt64) (stackLower : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent) : Prop where
  entry : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    (spike2ExtractionIter initial completed).rip = spike2ExtractionLinkedLayout.address .clearHigh
  safety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    ExtractionSafety stackLower (spike2ExtractionIter initial completed)
  executionSafety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    ExtractionExecutionSafety 236 (spike2ExtractionIter initial completed)
  ordinary : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    Spike2ExtractionOrdinary 236 (spike2ExtractionIter initial completed)
  branch : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    X86BranchCondition.notEqual.holds
        (extractionStates (spike2ExtractionIter initial completed)).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds
        (extractionStates (spike2ExtractionIter initial completed)).2.2.2.2.2

/-- Extraction invariant: the state and event accumulator are exactly the concrete production
prefix after the stated number of passes.  Physical safety and dispatcher facts remain in the
associated witness and are consumed at each `run` use. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
def spike2ExtractionInvariant (initial : X86_64MachineState) (initialEventsRev : List AnyEvent) :
    Nat → X86_64MachineState → List AnyEvent → Prop :=
  fun completed state eventsRev =>
    state = spike2ExtractionIter initial completed ∧ eventsRev = initialEventsRev

/-- Instantiate the existing bounded decimal extraction phase with exact Linux execution states.
No generic control-chain abstraction is introduced: every iteration is one `spike2Indexed`
selected pass supplied by the concrete layout/runtime bridge. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem spike2ExtractionPhase (value : UInt64) (stackLower : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent)
    (witness : Spike2ExtractionLoopWitness value stackLower initial initialEventsRev) :
    DecimalExtractionPhase selectedNonInputPlatformCall spike2Indexed value
      (spike2ExtractionInvariant initial initialEventsRev) where
  run completed state eventsRev within invariant := by
    rcases invariant with ⟨rfl, rfl⟩
    refine ⟨236, stackLower, ?_, ?_⟩
    · exact spike2ExtractionLinkedLayout_selectedPass
        (spike2ExtractionIter initial completed) (witness.entry completed within)
        (witness.safety completed within) (witness.executionSafety completed within)
        (witness.ordinary completed within) (witness.branch completed within)
    · exact ⟨rfl, rfl⟩

/-- A closed, stateful reverse-write witness for one production decimal formatting invocation. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
structure Spike2WriteLoopWitness (value : UInt64) (stackUpper outputLimit : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent) : Prop where
  entry : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    (spike2WriteIter initial completed).rip = spike2WriteLinkedLayout.address .pop
  safety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    WriteSafety stackUpper outputLimit (spike2WriteIter initial completed)
  executionSafety : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    WriteExecutionSafety 243 (spike2WriteIter initial completed)
  ordinary : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    Spike2WriteOrdinary 243 (spike2WriteIter initial completed)
  branch : ∀ completed, completed < Stdlib.Fmt.decimalDigitCount value →
    X86BranchCondition.notEqual.holds (writeStates (spike2WriteIter initial completed)).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates (spike2WriteIter initial completed)).2.2.2

/-- Exact reverse-write production-state invariant. -/
/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
def spike2WriteInvariant (initial : X86_64MachineState) (initialEventsRev : List AnyEvent) :
    Nat → X86_64MachineState → List AnyEvent → Prop :=
  fun completed state eventsRev =>
    state = spike2WriteIter initial completed ∧ eventsRev = initialEventsRev

/-- Instantiate the existing bounded decimal write phase with exact Linux execution states. -/
/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
theorem spike2WritePhase (value : UInt64) (stackUpper outputLimit : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List AnyEvent)
    (witness : Spike2WriteLoopWitness value stackUpper outputLimit initial initialEventsRev) :
    DecimalWritePhase selectedNonInputPlatformCall spike2Indexed value
      (spike2WriteInvariant initial initialEventsRev) where
  run completed state eventsRev within invariant := by
    rcases invariant with ⟨rfl, rfl⟩
    refine ⟨243, stackUpper, outputLimit, ?_, ?_⟩
    · exact spike2WriteLinkedLayout_selectedPass
        (spike2WriteIter initial completed) (witness.entry completed within)
        (witness.safety completed within) (witness.executionSafety completed within)
        (witness.ordinary completed within) (witness.branch completed within)
    · exact ⟨rfl, rfl⟩

end Spikes.Spike2Fibonacci.Linux

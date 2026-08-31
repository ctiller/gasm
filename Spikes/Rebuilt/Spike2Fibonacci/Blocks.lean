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

import Spikes.Rebuilt.Spike2Fibonacci.Spec

/-!
# Abstract source blocks for rebuilt Spike 2

These pure blocks describe the source operations, Fibonacci state transition, bounded iteration,
and exact observable events without mentioning a target, linker, or execution engine.
-/

namespace Spikes.Rebuilt.Spike2Fibonacci

open Gasm.Effects

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Abstract source effects used by the Fibonacci blocks. -/
structure Operations (Event : Type) where
  format : Nat → List UInt8
  format_correct : ∀ value, format value = Stdlib.Fmt.formatDecimal value
  output : List UInt8 → Event
  exit : UInt32 → Event

/- REF: docs/PROOF_TACTICS.md#design-relational-ghost-state -/
/-- Source loop state immediately before one row. -/
structure BlockState where
  index : Nat
  current : Nat
  next : Nat
deriving Repr, DecidableEq

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- One source row emits the current pair and advances the Fibonacci recurrence. -/
def rowBlock {Event : Type} (operations : Operations Event) (state : BlockState) :
    BlockState × Event :=
  (⟨state.index + 1, state.next, state.current + state.next⟩,
    operations.output
      ([0x46, 0x69, 0x62, 0x28] ++ operations.format state.index ++
        [0x29, 0x20, 0x3d, 0x20] ++ operations.format state.current ++ [0x0d, 0x0a]))

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Pure structural iteration of the source row block. -/
def loopBlock {Event : Type} (operations : Operations Event) :
    Nat → BlockState → BlockState × List Event
  | 0, state => (state, [])
  | remaining + 1, state =>
      let first := rowBlock operations state
      let rest := loopBlock operations remaining first.1
      (rest.1, first.2 :: rest.2)

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Complete abstract program: ninety source rows followed by typed exit. -/
def programBlock {Event : Type} (operations : Operations Event) : BlockState × List Event :=
  let rows := loopBlock operations 90 ⟨1, 1, 1⟩
  (rows.1, rows.2 ++ [operations.exit 0])

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- The concrete source interpretation uses canonical formatting and typed observable events. -/
def sourceOperations : Operations AnyEvent where
  format := Stdlib.Fmt.formatDecimal
  format_correct := by intro; rfl
  output bytes := Inject.inject (ConsoleEvent.out (decodeRow bytes))
  exit code := Inject.inject (ProcessEvent.exit code)

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- The row transition is exactly the source recurrence. -/
theorem rowBlock_state {Event : Type} (operations : Operations Event) (state : BlockState) :
    (rowBlock operations state).1 =
      ⟨state.index + 1, state.next, state.current + state.next⟩ := by
  rfl

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Correct formatting makes a row consume exactly the canonical row bytes. -/
theorem rowBlock_event {Event : Type} (operations : Operations Event) (state : BlockState) :
    (rowBlock operations state).2 = operations.output (rowBytes state.index state.current) := by
  simp [rowBlock, rowBytes, operations.format_correct]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Under the source interpretation, one row emits exactly its canonical console event. -/
theorem rowBlock_source (state : BlockState) :
    rowBlock sourceOperations state =
      (⟨state.index + 1, state.next, state.current + state.next⟩,
        rowEvent state.index state.current) := by
  simp [rowBlock, sourceOperations, rowEvent, rowBytes]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Source iteration emits exactly the recurrence-indexed chronological event list. -/
theorem loopBlock_source (remaining : Nat) (state : BlockState) :
    (loopBlock sourceOperations remaining state).2 =
      rowEvents state.index state.current state.next remaining := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
      rw [show loopBlock sourceOperations (remaining + 1) state =
        let first := rowBlock sourceOperations state
        let rest := loopBlock sourceOperations remaining first.1
        (rest.1, first.2 :: rest.2) from rfl]
      rw [rowBlock_source]
      simp only
      rw [ih]
      rfl

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Starting from a mathematical Fibonacci pair, iteration preserves the exact pair and index. -/
theorem loopBlock_fibonacci_state {Event : Type} (operations : Operations Event)
    (remaining index : Nat) :
    (loopBlock operations remaining ⟨index, fib index, fib (index + 1)⟩).1 =
      ⟨index + remaining, fib (index + remaining), fib (index + remaining + 1)⟩ := by
  induction remaining generalizing index with
  | zero => simp [loopBlock]
  | succ remaining ih =>
      change
        (loopBlock operations remaining
          ⟨index + 1, fib (index + 1), fib index + fib (index + 1)⟩).1 = _
      have next : fib index + fib (index + 1) = fib (index + 2) := by
        rw [show fib (index + 2) = fib (index + 1) + fib index from rfl, Nat.add_comm]
      rw [next]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (ih (index := index + 1))

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- The complete source program finishes immediately after row ninety with the next pair ready. -/
theorem programBlock_state :
    (programBlock sourceOperations).1 = ⟨91, fib 91, fib 92⟩ := by
  unfold programBlock
  change (loopBlock sourceOperations 90 ⟨1, 1, 1⟩).1 = _
  rw [show (⟨1, 1, 1⟩ : BlockState) = ⟨1, fib 1, fib (1 + 1)⟩ from rfl]
  simpa using (loopBlock_fibonacci_state sourceOperations 90 1)

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- The abstract source program exposes exactly the same event trace as the monadic spec. -/
theorem programBlock_events :
    (programBlock sourceOperations).2 = runModelTrace (spec : TraceM AnyEvent Unit) := by
  rw [runModelTrace_spec]
  unfold programBlock
  change
    (loopBlock sourceOperations 90 ⟨1, 1, 1⟩).2 ++ [sourceOperations.exit 0] =
      rowEvents 1 1 1 90 ++ [Inject.inject (ProcessEvent.exit 0)]
  rw [loopBlock_source]
  rfl

end Spikes.Rebuilt.Spike2Fibonacci

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

import Spikes.Spike2Fibonacci.Spec
import Stdlib.Fmt.Basic

/-!
# Structural native-driver loop contract for Spike 2

This module deliberately does not execute an x86 interpreter or assert an artifact-level
equivalence.  It is the compositional prerequisite for those proofs: a concrete Linux or Windows
adapter supplies a proof for one already-decomposed native loop block, while the induction here
accounts for all ninety passes and records the exact bytes and recurrence state at each boundary.

`NativeDriverBlocks` has no semantic authority by itself.  In particular, `advance` is merely the
adapter's selected native block transition and must be connected by that adapter to the real
lowered instruction segment and platform boundary.  Keeping this boundary explicit prevents a
logical model from being accidentally presented as an emitted-program certificate.
-/

namespace Spikes.Spike2Fibonacci

open Stdlib.Fmt

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- ASCII bytes which precede the decimal index in every native Spike 2 row. -/
def fibPrefixBytes : List UInt8 := [0x46, 0x69, 0x62, 0x28] -- "Fib("

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- ASCII bytes separating a row index from its Fibonacci value. -/
def fibMiddleBytes : List UInt8 := [0x29, 0x20, 0x3D, 0x20] -- ") = "

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- The CRLF terminator emitted by both native Spike 2 drivers. -/
def nativeLineEnding : List UInt8 := [0x0D, 0x0A]

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Exact native bytes for one Fibonacci row.  Decimal fields use the independently proved,
    total `Stdlib.Fmt.formatDecimal` codec rather than Lean string interpolation. -/
def fibonacciLineBytes (index : Nat) : List UInt8 :=
  fibPrefixBytes ++ formatDecimal index ++ fibMiddleBytes ++
    formatDecimal (fibIter index) ++ nativeLineEnding

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Exact concatenated native bytes after `completed` rows, numbered from one. -/
def fibonacciOutputBytes (completed : Nat) : List UInt8 :=
  (List.range completed).flatMap fun offset => fibonacciLineBytes (offset + 1)

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- One-row extension of the byte model.  This is the byte-level counterpart of an observable
    write boundary: it does not hide the row behind a formatted `String`. -/
theorem fibonacciOutputBytes_succ (completed : Nat) :
    fibonacciOutputBytes (completed + 1) =
      fibonacciOutputBytes completed ++ fibonacciLineBytes (completed + 1) := by
  simp [fibonacciOutputBytes, List.range_succ, List.flatMap_append]

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- The ninety-row native output has precisely the structurally accumulated byte form. -/
theorem fibonacciOutputBytes_90 :
    fibonacciOutputBytes 90 =
      (List.range 90).flatMap (fun offset => fibonacciLineBytes (offset + 1)) := rfl

/-- Observable part of a native-driver state at its main-loop boundary.  An adapter may retain
    arbitrary additional facts in `frame`; these fields are the values that the generic induction
    needs to preserve and expose to Linux/Windows trace adapters. -/
structure FibonacciBoundary where
  counter : UInt64
  current : UInt64
  next : UInt64
  output : List UInt8

/-- A platform adapter observes this boundary from its actual machine state. -/
abbrev FibonacciObserver (State : Type) := State → FibonacciBoundary

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The common recurrence/output invariant at a native main-loop header after `completed` rows.
    `frame` is deliberately supplied by the adapter, so this theorem layer does not weaken a
    concrete stack, code, IAT, syscall, or fault-freedom invariant. -/
def fibonacciBoundaryInvariant {State : Type} (observe : FibonacciObserver State)
    (frame : State → Prop) (completed : Nat) (state : State) : Prop :=
  frame state ∧
    (observe state).counter = (completed + 1).toUInt64 ∧
    (observe state).current = (fibIter (completed + 1)).toUInt64 ∧
    (observe state).next = (fibIter (completed + 2)).toUInt64 ∧
    (observe state).output = fibonacciOutputBytes completed

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Contract for one *already selected and decomposed* native driver iteration.  It carries the
    exact byte append obligation, not merely an abstract "one output event" claim.  The adapter
    proves `step` from its concrete instruction/block lemmas; this structure does not claim that
    a caller-provided transition is executable native code. -/
structure NativeDriverBlocks (State : Type) where
  observe : FibonacciObserver State
  frame : State → Prop
  initial : State
  advance : State → State
  initialInvariant : fibonacciBoundaryInvariant observe frame 0 initial
  step : ∀ completed state,
    completed < 90 →
    fibonacciBoundaryInvariant observe frame completed state →
      fibonacciBoundaryInvariant observe frame (completed + 1) (advance state)

namespace NativeDriverBlocks

/-- Iterating the adapter's native block transition.  It is structural recursion over the number
    of completed rows, never a replay of a whole-program evaluator. -/
def run (blocks : NativeDriverBlocks State) : Nat → State
  | 0 => blocks.initial
  | count + 1 => blocks.advance (run blocks count)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Universal loop induction over the driver's actual finite domain.  A concrete driver only
    proves a base boundary and an iteration step for rows `0..89`; this theorem supplies every
    boundary through the exact ninety-row exit and deliberately makes no claim about a 91st pass. -/
theorem run_invariant (blocks : NativeDriverBlocks State) (completed : Nat) (hcompleted : completed ≤ 90) :
    fibonacciBoundaryInvariant blocks.observe blocks.frame completed (run blocks completed) := by
  induction completed with
  | zero => exact blocks.initialInvariant
  | succ completed ih =>
    apply blocks.step completed (run blocks completed)
    · omega
    · exact ih (by omega)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The exact ninety-pass checkpoint consumed by the Linux and Windows drivers. -/
theorem run_90 (blocks : NativeDriverBlocks State) :
    fibonacciBoundaryInvariant blocks.observe blocks.frame 90 (run blocks 90) :=
  run_invariant blocks 90 (by omega)

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Byte-exact consequence of the ninety-pass checkpoint. -/
theorem run_90_output (blocks : NativeDriverBlocks State) :
    (blocks.observe (run blocks 90)).output = fibonacciOutputBytes 90 := by
  exact (run_90 blocks).2.2.2.2

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Recurrence-state consequence of the ninety-pass checkpoint. -/
theorem run_90_registers (blocks : NativeDriverBlocks State) :
    (blocks.observe (run blocks 90)).counter = (91 : Nat).toUInt64 ∧
    (blocks.observe (run blocks 90)).current = (fibIter 91).toUInt64 ∧
    (blocks.observe (run blocks 90)).next = (fibIter 92).toUInt64 := by
  exact ⟨(run_90 blocks).2.1, (run_90 blocks).2.2.1, (run_90 blocks).2.2.2.1⟩

end NativeDriverBlocks

end Spikes.Spike2Fibonacci

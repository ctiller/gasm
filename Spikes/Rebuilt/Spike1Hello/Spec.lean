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

import Gasm.Core.Types

/-!
# Rebuilt Spike 1 source contract

This file owns only the target-independent output contract selected by Craig on 2026-08-31.
It contains no instruction, address, ABI, provider, artifact, or `VerifiedProgram` definition.
-/

namespace Spikes.Rebuilt.Spike1Hello

/-- The logical text required before an ordinary successful exit. -/
def message : List UInt8 :=
  "Hello, World!\n".toUTF8.toList

/-- Fatal outcomes admitted by the Spike 1 root. A short write is deliberately absent. -/
inductive FatalOutputError where
  | noStdout
  | writeFailure
deriving DecidableEq, Repr

/-- Result of one abstract write attempt. Positive or zero partial acceptance is nonfatal. -/
inductive WriteResult where
  | accepted (count : Nat)
  | fatal (error : FatalOutputError)
deriving DecidableEq, Repr

/-- Logical state threaded through repeated writes. -/
structure OutputState where
  emitted : List UInt8
  remaining : List UInt8
deriving DecidableEq, Repr

/-- The state is an exact split of the required message. -/
def OutputState.Valid (state : OutputState) : Prop :=
  state.emitted ++ state.remaining = message

/-- Initial state before stdout acquisition and the first write. -/
def initial : OutputState :=
  { emitted := [], remaining := message }

theorem initial_valid : initial.Valid := by
  simp [initial, OutputState.Valid]

/-- Apply a nonfatal provider acceptance. The provider must not claim more bytes than remain. -/
def accept (state : OutputState) (count : Nat) : OutputState :=
  { emitted := state.emitted ++ state.remaining.take count
    remaining := state.remaining.drop count }

/-- Short and zero-length writes preserve the exact output split and therefore require retry. -/
theorem accept_valid (state : OutputState) (valid : state.Valid) (count : Nat) :
    (accept state count).Valid := by
  simp only [accept, OutputState.Valid]
  rw [List.append_assoc, List.take_append_drop, valid]

/-- Root-visible process outcome. Fatal exit codes are required to be nonzero. -/
inductive Outcome where
  | exited (code : UInt32) (emitted : List UInt8)
  | fatal (error : FatalOutputError) (code : UInt32) (emitted : List UInt8)
deriving DecidableEq, Repr

/-- Selected Spike 1 root: normal exit requires the complete text; fatal output failure permits
only the exact committed prefix, and absence of stdout commits nothing. -/
def Accepts : Outcome → Prop
  | .exited code emitted => code = 0 ∧ emitted = message
  | .fatal .noStdout code emitted => code ≠ 0 ∧ emitted = []
  | .fatal .writeFailure code emitted => code ≠ 0 ∧ emitted.IsPrefix message

/-- Finishing from a valid state is legal exactly when no bytes remain. -/
theorem accepts_success (state : OutputState) (valid : state.Valid)
    (done : state.remaining = []) : Accepts (.exited 0 state.emitted) := by
  rw [OutputState.Valid, done, List.append_nil] at valid
  exact ⟨rfl, valid⟩

/-- A fatal write after any sequence of accepted prefixes preserves an exact committed prefix. -/
theorem accepts_write_failure (state : OutputState) (valid : state.Valid) (code : UInt32)
    (failed : code ≠ 0) : Accepts (.fatal .writeFailure code state.emitted) := by
  refine ⟨failed, ?_⟩
  exact ⟨state.remaining, valid⟩

/-- Missing stdout is fatal before output begins. -/
theorem accepts_no_stdout (code : UInt32) (failed : code ≠ 0) :
    Accepts (.fatal .noStdout code []) := by
  exact ⟨failed, rfl⟩

end Spikes.Rebuilt.Spike1Hello

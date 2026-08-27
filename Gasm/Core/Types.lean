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

import Lean

namespace Gasm.Core

/- REF: docs/API_STATE_MODELS.md#1-the-composed-state-model-zero-cost-proof-erasure -/
/-- 64-bit virtual memory address. -/
@[reducible] def Address := UInt64

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- 64-bit quadword. -/
@[reducible] def QWord := UInt64

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- 32-bit doubleword. -/
@[reducible] def DWord := UInt32

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- 16-bit word. -/
@[reducible] def Word := UInt16

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- 8-bit byte. -/
@[reducible] def Byte := UInt8

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality-vector-clocks -/
/-- Unique identifier for an execution thread. -/
def ThreadId := Nat
deriving DecidableEq, Repr, Inhabited

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality-vector-clocks -/
/-- Monotonic vector clock mapping thread IDs to logical event timestamps. -/
structure VectorClock where
  clock : ThreadId → Nat

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality-vector-clocks -/
/-- Strict happens-before relation on vector clocks. -/
def VectorClock.happensBefore (vc₁ vc₂ : VectorClock) : Prop :=
  (∀ t, vc₁.clock t ≤ vc₂.clock t) ∧ (∃ t, vc₁.clock t < vc₂.clock t)

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality-vector-clocks -/
/-- Component-wise join of two vector clocks. -/
def VectorClock.join (vc₁ vc₂ : VectorClock) : VectorClock :=
  { clock := fun t => max (vc₁.clock t) (vc₂.clock t) }

/- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality-vector-clocks -/
/-- Advances the logical clock for a specified thread. -/
def VectorClock.tick (vc : VectorClock) (t : ThreadId) : VectorClock :=
  { clock := fun tid => if tid = t then vc.clock tid + 1 else vc.clock tid }

/- REF: docs/API_STATE_MODELS.md#1-the-composed-state-model-zero-cost-proof-erasure -/
/-- Identifier tag for causal synchronization events. -/
def EventTag := Nat
deriving DecidableEq, Repr, Inhabited

end Gasm.Core

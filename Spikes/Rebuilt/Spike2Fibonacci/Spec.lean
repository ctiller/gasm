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

import Gasm.Effects.Console
import Gasm.Effects.Inject
import Gasm.Effects.Process
import Gasm.Effects.Trace
import Stdlib.Fmt.UInt64Decimal

/-!
# Rebuilt Spike 2 specification

This source-level specification fixes the Fibonacci recurrence, the exact bytes and console event
for each row, the bounded ninety-row trace, and the final typed process exit.  It contains no
target program or execution machinery.
-/

namespace Spikes.Rebuilt.Spike2Fibonacci

open Gasm.Effects
open Stdlib.Fmt

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Mathematical Fibonacci recurrence used by the rebuilt specification. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Machine-shaped tail-recursive Fibonacci recurrence. -/
def fibLoop : Nat → Nat → Nat → Nat
  | 0, current, _ => current
  | remaining + 1, current, next => fibLoop remaining next (current + next)

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Tail recursion agrees with the mathematical recurrence at every index. -/
theorem fibLoop_eq (remaining index : Nat) :
    fibLoop remaining (fib index) (fib (index + 1)) = fib (index + remaining) := by
  induction remaining generalizing index with
  | zero => rfl
  | succ remaining ih =>
      rw [show fibLoop (remaining + 1) (fib index) (fib (index + 1)) =
        fibLoop remaining (fib (index + 1)) (fib index + fib (index + 1)) from rfl]
      have next : fib index + fib (index + 1) = fib (index + 2) := by
        rw [show fib (index + 2) = fib (index + 1) + fib index from rfl, Nat.add_comm]
      rw [next, ih]
      congr 1
      omega

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Exact native bytes for one one-based Fibonacci row. -/
def rowBytes (index value : Nat) : List UInt8 :=
  [0x46, 0x69, 0x62, 0x28] ++ formatDecimal index ++
    [0x29, 0x20, 0x3d, 0x20] ++ formatDecimal value ++ [0x0d, 0x0a]

/- REF: docs/SYSTEM_EFFECTS.md#21-monadconsole-standard-io -/
/-- Total text boundary for the ASCII row bytes. -/
def decodeRow (bytes : List UInt8) : String :=
  match String.fromUTF8? (ByteArray.mk bytes.toArray) with
  | some text => text
  | none => String.ofList (bytes.map (fun byte => Char.ofNat byte.toNat))

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- The exact observable event for one source row. -/
def rowEvent (index current : Nat) : AnyEvent :=
  Inject.inject (ConsoleEvent.out (decodeRow (rowBytes index current)))

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Chronological source events for a bounded Fibonacci recurrence. -/
def rowEvents : Nat → Nat → Nat → Nat → List AnyEvent
  | _, _, _, 0 => []
  | index, current, next, remaining + 1 =>
      rowEvent index current :: rowEvents (index + 1) next (current + next) remaining

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Structurally bounded specification-side row producer. -/
def emitRows : Nat → Nat → Nat → Nat → TraceM AnyEvent Unit
  | _, _, _, 0 => pure ()
  | index, current, next, remaining + 1 => do
      MonadConsole.printStr (decodeRow (rowBytes index current))
      emitRows (index + 1) next (current + next) remaining

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- The bounded source producer appends exactly its chronological row events. -/
theorem emitRows_run (index current next remaining : Nat) (state : TraceState AnyEvent) :
    emitRows index current next remaining state =
      (some (), { state with
        events := state.events ++ rowEvents index current next remaining }) := by
  induction remaining generalizing index current next state with
  | zero =>
      change (some (), state) = (some (), { state with events := state.events ++ [] })
      cases state
      simp
  | succ remaining ih =>
      let event := rowEvent index current
      let nextState : TraceState AnyEvent := { state with events := state.events ++ [event] }
      change emitRows (index + 1) next (current + next) remaining nextState = _
      rw [ih]
      cases state
      simp [nextState, event, rowEvent, rowEvents, List.append_assoc]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Sequential source composition of bounded rows and typed process exit. -/
def program (index current next remaining : Nat) (code : UInt32) : TraceM AnyEvent Unit :=
  fun state =>
    match emitRows index current next remaining state with
    | (some _, nextState) =>
        (none, { nextState with events := nextState.events ++
          [Inject.inject (ProcessEvent.exit code)] })
    | (none, nextState) => (none, nextState)

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Source composition adds exactly one final typed exit event. -/
theorem program_events (index current next remaining : Nat) (code : UInt32)
    (state : TraceState AnyEvent) :
    (program index current next remaining code state).2.events =
      state.events ++ rowEvents index current next remaining ++
        [Inject.inject (ProcessEvent.exit code)] := by
  unfold program
  rw [emitRows_run]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Rebuilt Spike 2 contract: ninety rows followed by typed process exit. -/
def spec : TraceM AnyEvent Unit := program 1 1 1 90 0

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Exact effect trace of the rebuilt source specification. -/
theorem runModelTrace_spec :
    runModelTrace (spec : TraceM AnyEvent Unit) =
      rowEvents 1 1 1 90 ++ [Inject.inject (ProcessEvent.exit 0)] := by
  rw [show spec = program 1 1 1 90 0 from rfl]
  exact program_events 1 1 1 90 0 ({} : TraceState AnyEvent)

end Spikes.Rebuilt.Spike2Fibonacci

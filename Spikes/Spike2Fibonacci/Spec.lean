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
import Gasm.Core.Types
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.Trace
import Stdlib.Fmt.UInt64Decimal

namespace Spikes.Spike2Fibonacci

open Gasm.Core
open Gasm.Effects
open Stdlib.Fmt

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Pure functional canonical definition of Fibonacci numbers in Lean. -/
def fibNat : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibNat (n + 1) + fibNat n

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Tail-recursive iterative Fibonacci loop accumulator. -/
def fibIterLoop (i a b : Nat) : Nat :=
  match i with
  | 0 => a
  | i + 1 => fibIterLoop i b (a + b)

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Tail-recursive iterative Fibonacci calculation matching machine loop state. -/
def fibIter (n : Nat) : Nat :=
  fibIterLoop n 0 1

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Inductive accumulator invariant relating the tail-recursive loop to fibNat. -/
theorem fibIterLoop_invariant (k m : Nat) :
    fibIterLoop k (fibNat m) (fibNat (m + 1)) = fibNat (m + k) := by
  induction k generalizing m with
  | zero =>
    rfl
  | succ k ih =>
    show fibIterLoop k (fibNat (m + 1)) (fibNat m + fibNat (m + 1)) = fibNat (m + (k + 1))
    have hSum : fibNat m + fibNat (m + 1) = fibNat (m + 2) := by
      show fibNat m + fibNat (m + 1) = fibNat (m + 1 + 1)
      have hDef : fibNat (m + 1 + 1) = fibNat (m + 1) + fibNat m := rfl
      rw [hDef, Nat.add_comm]
    rw [hSum]
    have ih' := ih (m + 1)
    have hAssoc : m + 1 + k = m + (k + 1) := by omega
    rw [hAssoc] at ih'
    exact ih'

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Full formal theorem proving equivalence between tail-recursive and mathematical Fibonacci. -/
theorem fibIter_eq_fibNat (n : Nat) : fibIter n = fibNat n := by
  have hInv := fibIterLoop_invariant n 0
  have h0 : fibNat 0 = 0 := rfl
  have h1 : fibNat (0 + 1) = 1 := rfl
  have hN : 0 + n = n := by omega
  rw [h0, h1, hN] at hInv
  exact hInv

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- ASCII bytes which precede the decimal index in every Spike 2 row. -/
def fibPrefixBytes : List UInt8 := [0x46, 0x69, 0x62, 0x28] -- "Fib("

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- ASCII bytes separating a row index from its Fibonacci value. -/
def fibMiddleBytes : List UInt8 := [0x29, 0x20, 0x3D, 0x20] -- ") = "

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- The CRLF terminator emitted by both native Spike 2 drivers. -/
def nativeLineEnding : List UInt8 := [0x0D, 0x0A]

/- REF: docs/STDLIB_FMT.md#6-spike-2-migration-status -/
/-- Exact reference bytes for one Fibonacci row.  Decimal fields use the independently proved,
    total standard-library formatter. -/
def fibonacciLineBytes (index : Nat) : List UInt8 :=
  fibPrefixBytes ++ formatDecimal index ++ fibMiddleBytes ++
    formatDecimal (fibIter index) ++ nativeLineEnding

/-- Total decoding boundary for reference output bytes. -/
def decodeNativeBytes (bytes : List UInt8) : String :=
  let byteArr := ByteArray.mk bytes.toArray
  match String.fromUTF8? byteArr with
  | some str => str
  | none => String.ofList (bytes.map (fun byte => Char.ofNat byte.toNat))

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Formats all 90 Fibonacci lines into a single complete output buffer using verified fibIter (CRLF). -/
def formattedFibonacciWindowsOutput : String :=
  (List.range 90).foldl (fun acc i =>
    let n := i + 1
    acc ++ s!"Fib({n}) = {fibIter n}\r\n"
  ) ""

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Formats all 90 Fibonacci lines into a single complete output buffer using verified fibIter (LF). -/
def formattedFibonacciWasmOutput : String :=
  (List.range 90).foldl (fun acc i =>
    let n := i + 1
    acc ++ s!"Fib({n}) = {fibIter n}\n"
  ) ""

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Chronological reference events for a bounded run of Fibonacci rows. -/
def fibonacciEventsFrom : Nat → Nat → List AnyEvent
  | _, 0 => []
  | index, remaining + 1 =>
      Inject.inject (ConsoleEvent.out (decodeNativeBytes (fibonacciLineBytes index))) ::
        fibonacciEventsFrom (index + 1) remaining

/-- High-level bounded row producer.  Its structural recursion is the specification-side
    counterpart of the native loop invariant, not an evaluator replay. -/
def emitFibonacciRows : Nat → Nat → TraceM AnyEvent Unit
  | _, 0 => pure ()
  | index, remaining + 1 => do
      MonadConsole.printStr (decodeNativeBytes (fibonacciLineBytes index))
      emitFibonacciRows (index + 1) remaining

/-- The bounded row producer changes only the event trace and appends precisely its
    chronological reference events. -/
theorem emitFibonacciRows_run (index remaining : Nat) (state : TraceState AnyEvent) :
    emitFibonacciRows index remaining state =
      (some (), { state with
        events := state.events ++ fibonacciEventsFrom index remaining }) := by
  induction remaining generalizing index state with
  | zero =>
      change (some (), state) =
        (some (), { state with events := state.events ++ [] })
      cases state
      simp
  | succ remaining ih =>
      let event : AnyEvent :=
        Inject.inject (ConsoleEvent.out (decodeNativeBytes (fibonacciLineBytes index)))
      let nextState : TraceState AnyEvent := { state with events := state.events ++ [event] }
      change emitFibonacciRows (index + 1) remaining nextState = _
      rw [ih]
      cases state
      simp [nextState, event, fibonacciEventsFrom, List.append_assoc]

/-- Event projection of `emitFibonacciRows_run`. -/
theorem emitFibonacciRows_events (index remaining : Nat) (state : TraceState AnyEvent) :
    ((emitFibonacciRows index remaining state).2.events) =
      state.events ++ fibonacciEventsFrom index remaining := by
  rw [emitFibonacciRows_run]

/-- Sequential composition of the bounded row producer and typed process exit. -/
def fibonacciProgram (index remaining : Nat) (code : UInt32) : TraceM AnyEvent Unit :=
  fun state =>
    match emitFibonacciRows index remaining state with
    | (some _, next) =>
        (none, { next with events := next.events ++
          [Inject.inject (ProcessEvent.exit code)] })
    | (none, next) => (none, next)

/-- Sequential composition with process exit adds exactly the final typed exit event. -/
theorem fibonacciProgram_events (index remaining : Nat) (code : UInt32)
    (state : TraceState AnyEvent) :
    (fibonacciProgram index remaining code state).2.events =
      state.events ++ fibonacciEventsFrom index remaining ++
        [Inject.inject (ProcessEvent.exit code)] := by
  unfold fibonacciProgram
  change
    (match emitFibonacciRows index remaining state with
      | (some _, next) =>
          (none, { next with events := next.events ++
            [Inject.inject (ProcessEvent.exit code)] })
      | (none, next) => (none, next)).2.events = _
  rw [emitFibonacciRows_run]

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- High-level software specification: prints the first 90 Fibonacci numbers to standard output
    and exits with code 0. -/
def fibonacciSpec : TraceM AnyEvent Unit := fibonacciProgram 1 90 0

/-- Exact effect trace of the high-level specification. -/
theorem runModelTrace_fibonacciSpec :
    runModelTrace (fibonacciSpec : TraceM AnyEvent Unit) =
      fibonacciEventsFrom 1 90 ++ [Inject.inject (ProcessEvent.exit 0)] := by
  rw [show fibonacciSpec = fibonacciProgram 1 90 0 from rfl]
  exact fibonacciProgram_events 1 90 0 ({} : TraceState AnyEvent)

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- High-level software specification for Wasm: prints all 90 formatted lines and exits with code 0. -/
def fibonacciWasmSpec : TraceM AnyEvent Unit := do
  MonadConsole.printStr formattedFibonacciWasmOutput
  MonadProcess.exitProcess 0

end Spikes.Spike2Fibonacci

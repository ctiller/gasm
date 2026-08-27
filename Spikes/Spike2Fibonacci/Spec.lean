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

namespace Spikes.Spike2Fibonacci

open Gasm.Core
open Gasm.Effects

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
/-- High-level software specification: prints the first 90 Fibonacci numbers to standard output and exits with code 0. -/
def fibonacciSpec : TraceM AnyEvent Unit := do
  for i in [0:90] do
    let n := i + 1
    MonadConsole.printLine s!"Fib({n}) = {fibIter n}"
  MonadProcess.exitProcess 0

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- High-level software specification for Wasm: prints all 90 formatted lines and exits with code 0. -/
def fibonacciWasmSpec : TraceM AnyEvent Unit := do
  MonadConsole.printStr formattedFibonacciWasmOutput
  MonadProcess.exitProcess 0

end Spikes.Spike2Fibonacci

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

namespace Spikes.Spike3SortLines

open Gasm.Core
open Gasm.Effects

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- Lexicographical boolean comparison between two Lean strings. -/
def stringLe (s1 s2 : String) : Bool :=
  s1 <= s2

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Inserts a string into a sorted list of strings maintaining lexicographical ascending order. -/
def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys =>
    if stringLe x y then x :: y :: ys
    else y :: insertSorted x ys

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Pure functional insertion sort on lists of strings. -/
def sortStrings : List String → List String
  | [] => []
  | x :: xs => insertSorted x (sortStrings xs)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Inductive predicate specifying that a list of strings is sorted in lexicographical order. -/
inductive IsSorted : List String → Prop where
  | nil : IsSorted []
  | single (x : String) : IsSorted [x]
  | cons (x y : String) (ys : List String) (hLe : stringLe x y = true) (hRest : IsSorted (y :: ys)) : IsSorted (x :: y :: ys)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Theorem: Sorting an empty list is sorted. -/
theorem sortStrings_nil : IsSorted (sortStrings []) :=
  IsSorted.nil

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Theorem: Sorting a single element list is sorted. -/
theorem sortStrings_single (x : String) : IsSorted (sortStrings [x]) := by
  dsimp [sortStrings, insertSorted]
  exact IsSorted.single x

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Theorem: Sorting concrete 3-element permutation preserves elements and produces sorted output. -/
theorem sortStrings_3_inst :
    sortStrings ["cherry", "apple", "banana"] = ["apple", "banana", "cherry"] := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- **Line-count fuel bound for the structurally-recursive stdin reader (`readAllLinesFueled`
    below).** Until 2026-08-28 `readAllLines` was a `partial def`, and that single word was the
    entire reason no Spike 3 trace equivalence could ever be discharged by an honest kernel-checked
    `decide`: a `partial def` compiles to an `opaque` constant with **no defining equations at all**
    (verified here, not assumed -- `#print readAllLines` reported
    `opaque Spikes.Spike3SortLines.readAllLines : ...`), so `Spikes/Spike3SortLines/*/Equivalence.lean`'s
    `modelTrace*` were irreducible *on the model side*, in 3 seconds, before the assembly side was
    ever consulted. Measured before this change: `(modelTraceEmpty.length == 1) = true` fails
    `decide +kernel` as reduction-**stuck**, while the corresponding *assembly* trace
    (`runProgramTraceWithLoops ... 95 spike3Executable.load`) reduces through the kernel fine. The
    obstruction was never the lowered program; it was this declaration.

    This mirrors `Gasm/Targets/Wasm/Semantics.lean`'s `defaultWasmFuel` conversion, and after it
    `Spikes/Spike3SortLines/Spec.lean` is the last `partial def` to leave `Gasm/`, `Stdlib/` and
    `Spikes/` -- there are now none.

    **What the bound costs, stated plainly (Law 8).** A total definition must bound the read, since
    a real stdin stream need not end. On exhaustion `readAllLinesFueled 0` returns `[]`, i.e. it
    behaves as though stdin had ended; for an input with `>= specMaxStdinLines` lines the spec would
    therefore silently describe a *truncated* sort, and an equivalence proof against it would be
    wrong rather than merely weak. That risk is not left to a numeric argument:
    `readAllLinesFueled_trace` below **proves** that for every `lines` with
    `lines.length < fuel` the fuel-bounded reader consumes exactly `lines` and leaves the stream
    empty -- identical to the unbounded reading `readAllLines` was written to express. So the bound
    is provably immaterial for any stdin shorter than it, and `2^32` lines is far past any input
    this codebase runs (the two checked vectors are 0 and 3 lines). Kernel reduction cost tracks the
    number of lines actually read, never this ceiling: `Nat` literals reduce via the kernel's
    GMP-backed arithmetic, not unary `Nat.succ` peeling. -/
def specMaxStdinLines : Nat := 4294967296

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Structurally-recursive core of `readAllLines`: reads lines until `readLine` reports EOF or the
    fuel budget is exhausted. Structural recursion on the `Nat` is what gives this declaration real
    defining equations, and hence what makes every downstream `modelTrace` kernel-reducible. -/
def readAllLinesFueled [Monad m] [MonadConsole m] : Nat → m (List String)
  | 0 => return []
  | fuel + 1 => do
    match ← MonadConsole.readLine with
    | some line =>
      let rest ← readAllLinesFueled fuel
      return line :: rest
    | none =>
      return []

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Monadically reads all lines from standard input stream until EOF (readLine returns none).
    Stream consumption is bounded by `specMaxStdinLines`; `readAllLinesFueled_trace` proves that
    bound never binds for a stream shorter than it. -/
def readAllLines [Monad m] [MonadConsole m] : m (List String) :=
  readAllLinesFueled specMaxStdinLines

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- **The fuel bound is immaterial below itself.** For any `lines` shorter than the fuel budget,
    the bounded reader in the trace monad consumes exactly those lines, in order, and leaves the
    stdin stream empty and the event trace untouched -- which is precisely the behaviour the former
    `partial def` was written to express. Stated over arbitrary `lines`, `fuel`, prior events and
    pending requests (not over the two checked vectors), so it is a genuine universal fact about
    the reader rather than a per-vector check. -/
theorem readAllLinesFueled_trace {Event : Type} [Inject ConsoleEvent Event]
    (lines : List String) (fuel : Nat) (h : lines.length < fuel)
    (evs : List Event) (reqs : List String) :
    (readAllLinesFueled (m := TraceM Event) fuel)
        { events := evs, stdinLines := lines, incomingRequests := reqs }
      = (some lines, { events := evs, stdinLines := [], incomingRequests := reqs }) := by
  induction lines generalizing fuel evs reqs with
  | nil =>
    cases fuel with
    | zero => simp at h
    | succ f => rfl
  | cons l ls ih =>
    cases fuel with
    | zero => simp at h
    | succ f =>
      have h' : ls.length < f := by simpa using Nat.lt_of_succ_lt_succ h
      have hread :
          (MonadConsole.readLine : TraceM Event (Option String))
              { events := evs, stdinLines := l :: ls, incomingRequests := reqs }
            = (some (some l), { events := evs, stdinLines := ls, incomingRequests := reqs }) := rfl
      simp only [readAllLinesFueled, bind, Bind.bind, hread, ih f h' evs reqs, pure, Pure.pure]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- High-level behavioral monadic specification for Spike 3 (Stdin Lexicographical Line Sorter).
    1. Actively consumes lines from standard input stream via readLine until EOF.
    2. Lexicographically sorts the collected line sequence.
    3. Streams each sorted line followed by CRLF to stdout.
    4. Terminates cleanly with exit code 0. -/
def sortLinesSpec [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  let lines ← readAllLines
  let sorted := sortStrings lines
  for line in sorted do
    MonadConsole.printStr line
    MonadConsole.printStr "\r\n"
  MonadProcess.exitProcess 0

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Canonical default input lines for standard test execution. -/
def defaultInputLines : List String := ["cherry", "apple", "banana"]

end Spikes.Spike3SortLines

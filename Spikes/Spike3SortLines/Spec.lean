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
/-- Monadically reads all lines from standard input stream until EOF (readLine returns none).
    Unbounded stream consumption up to available process memory. -/
partial def readAllLines [Monad m] [MonadConsole m] : m (List String) := do
  match ← MonadConsole.readLine with
  | some line =>
    let rest ← readAllLines
    return line :: rest
  | none =>
    return []

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

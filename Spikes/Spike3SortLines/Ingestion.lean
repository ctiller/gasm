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

import Spikes.Spike3SortLines.Input

/-!
Pure line-ingestion laws shared by the native sorter bridges.

This is deliberately stated over Lean's existing `List` model, not a second
storage implementation.  The pending Stdlib Vec/LineStore adapter will prove
that its bounded append operation realizes `appendLines`; these lemmas then
transfer its first-refusal behavior without redoing the induction.
-/

namespace Spikes.Spike3SortLines

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Append one already-decoded line when the abstract line-store capacity remains. -/
def appendLine {α : Type} (capacity : Nat) (stored : List α) (line : α) : Option (List α) :=
  if stored.length < capacity then some (stored ++ [line]) else none

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Sequentially append decoded lines, stopping exactly at the first refused append. -/
def appendLines {α : Type} (capacity : Nat) (stored : List α) : List α → Option (List α)
  | [] => some stored
  | line :: tail =>
    match appendLine capacity stored line with
    | some next => appendLines capacity next tail
    | none => none

theorem appendLines_append {α : Type} (capacity : Nat) (stored prior suffix : List α) :
    appendLines capacity stored (prior ++ suffix) =
      (appendLines capacity stored prior).bind (fun next => appendLines capacity next suffix) := by
  induction prior generalizing stored with
  | nil => rfl
  | cons line prior ih =>
    simp only [List.cons_append, appendLines]
    cases h : appendLine capacity stored line with
    | none => simp [h]
    | some next => simp [h, ih]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A prefix whose aggregate length fits is appended exactly, in arrival order. -/
theorem appendLines_of_fits {α : Type} (capacity : Nat) (stored lines : List α)
    (fits : stored.length + lines.length ≤ capacity) :
    appendLines capacity stored lines = some (stored ++ lines) := by
  induction lines generalizing stored with
  | nil => simp [appendLines]
  | cons line tail ih =>
    have headFits : stored.length < capacity := by
      exact Nat.lt_of_lt_of_le
        (Nat.lt_add_of_pos_right (by simp)) fits
    simp only [appendLines, appendLine, if_pos headFits]
    rw [ih (stored ++ [line])]
    · simp [List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil] at fits ⊢
      omega

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- After a successful capacity-filling prefix, the first following line is refused and the
remaining tail is not inspected.  This is the pure form of the preparation-abort boundary used
by Linux and Windows; it does not claim anything about target execution. -/
theorem appendLines_first_failure_untouched_tail {α : Type}
    (capacity : Nat) (stored prior : List α) (first : α) (tail : List α)
    (fills : stored.length + prior.length = capacity) :
    appendLines capacity stored (prior ++ first :: tail) = none := by
  rw [appendLines_append, appendLines_of_fits]
  · change appendLines capacity (stored ++ prior) (first :: tail) = none
    have full : (stored ++ prior).length = capacity := by
      simpa [List.length_append] using fills
    simp [appendLines, appendLine, full]
  · omega

end Spikes.Spike3SortLines

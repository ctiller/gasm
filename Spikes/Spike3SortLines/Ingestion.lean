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
storage implementation.  The Stdlib Vec/LineStore adapter will prove that its
bounded append operation realizes `appendLinesResult`; these lemmas then
transfer its first-refusal behavior without redoing the induction.
-/

namespace Spikes.Spike3SortLines

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The exact result of bounded decoded-line ingestion.  A refusal records the successfully
prepared store, the first refused line, and the suffix which was not inspected.  This is the
pure evidence needed by target bridges to establish that a preparation abort cannot have
consumed or emitted a fabricated tail. -/
inductive AppendLinesResult (α : Type) where
  | completed (stored : List α)
  | refused (prepared : List α) (first : α) (untouchedTail : List α)
  deriving Repr

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Append one already-decoded line when the abstract line-store capacity remains. -/
def appendLine {α : Type} (capacity : Nat) (stored : List α) (line : α) : Option (List α) :=
  if stored.length < capacity then some (stored ++ [line]) else none

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Sequentially append decoded lines, stopping exactly at the first refused append and
retaining its complete boundary evidence. -/
def appendLinesResult {α : Type} (capacity : Nat) (stored : List α) : List α → AppendLinesResult α
  | [] => .completed stored
  | line :: tail =>
    match appendLine capacity stored line with
    | some next => appendLinesResult capacity next tail
    | none => .refused stored line tail

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Forget the refusal boundary only for a local option-shaped corollary.  Program behavior
certificates consume `AppendLinesResult` directly. -/
def AppendLinesResult.toOption {α : Type} : AppendLinesResult α → Option (List α)
  | .completed stored => some stored
  | .refused _ _ _ => none

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A prefix whose aggregate length fits is appended exactly, in arrival order. -/
theorem appendLinesResult_of_fits {α : Type} (capacity : Nat) (stored lines : List α)
    (fits : stored.length + lines.length ≤ capacity) :
    appendLinesResult capacity stored lines = .completed (stored ++ lines) := by
  induction lines generalizing stored with
  | nil => simp [appendLinesResult]
  | cons line tail ih =>
    have headFits : stored.length < capacity := by
      exact Nat.lt_of_lt_of_le
        (Nat.lt_add_of_pos_right (by simp)) fits
    simp only [appendLinesResult, appendLine, if_pos headFits]
    rw [ih (stored ++ [line])]
    · simp [List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil] at fits ⊢
      omega

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- After a successful capacity-filling prefix, the first following line is refused and the
remaining tail is not inspected.  This is the pure form of the preparation-abort boundary used
by Linux and Windows; it does not claim anything about target execution. -/
theorem appendLinesResult_first_refusal {α : Type}
    (capacity : Nat) (stored prior : List α) (first : α) (tail : List α)
    (fills : stored.length + prior.length = capacity) :
    appendLinesResult capacity stored (prior ++ first :: tail) =
      .refused (stored ++ prior) first tail := by
  induction prior generalizing stored with
  | nil =>
    simp only [List.nil_append, appendLinesResult]
    have full : stored.length = capacity := by omega
    simp [appendLine, full]
  | cons line prior ih =>
    simp only [List.cons_append, appendLinesResult]
    have headFits : stored.length < capacity := by
      simp only [List.length_cons] at fills
      omega
    rw [show appendLine capacity stored line = some (stored ++ [line]) by
      simp [appendLine, headFits]]
    simpa [List.append_assoc] using ih (stored ++ [line]) (by
      simp only [List.length_append, List.length_cons, List.length_nil] at fills ⊢
      omega)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The option projection of an explicit first refusal is `none`; this is a corollary, not the
semantic interface used by the sorter proofs. -/
theorem appendLinesResult_first_refusal_toOption {α : Type}
    (capacity : Nat) (stored prior : List α) (first : α) (tail : List α)
    (fills : stored.length + prior.length = capacity) :
    (appendLinesResult capacity stored (prior ++ first :: tail)).toOption = none := by
  rw [appendLinesResult_first_refusal capacity stored prior first tail fills]
  rfl

end Spikes.Spike3SortLines

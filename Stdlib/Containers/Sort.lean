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

import Stdlib.Containers.Vec

/-! Reference insertion sorting and reusable correctness certificates. -/

namespace Stdlib.Sort

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
def SortedBy (before : α → α → Bool) (values : List α) : Prop :=
  List.Pairwise (fun left right => before left right = true) values

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
/-- The exact laws required by insertion-sort orderedness: transitivity and totality. -/
structure LawfulTotalRelation (before : α → α → Bool) : Prop where
  trans : ∀ {a b c}, before a b = true → before b c = true → before a c = true
  total : ∀ a b, before a b = true ∨ before b a = true

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
/-- Optional stronger laws for consumers that need equality reasoning in addition to sorting. -/
structure LawfulOrder (before : α → α → Bool) : Prop extends LawfulTotalRelation before where
  refl : ∀ value, before value value = true
  antisymm : ∀ {a b}, before a b = true → before b a = true → a = b

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
def insert (before : α → α → Bool) (value : α) : List α → List α
  | [] => [value]
  | current :: rest =>
      if before value current then value :: current :: rest
      else current :: insert before value rest

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
def insertionSort (before : α → α → Bool) : List α → List α
  | [] => []
  | value :: rest => insert before value (insertionSort before rest)

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem insert_perm (before : α → α → Bool) (value : α) (values : List α) :
    (insert before value values).Perm (value :: values) := by
  induction values with
  | nil => simp [insert]
  | cons current rest ih =>
      unfold insert
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons current ih).trans (List.Perm.swap value current rest)

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem insert_sorted (before : α → α → Bool) (laws : LawfulTotalRelation before)
    (value : α) {values : List α} (ordered : SortedBy before values) :
    SortedBy before (insert before value values) := by
  induction values with
  | nil => simp [SortedBy, insert]
  | cons current rest ih =>
      rw [SortedBy, List.pairwise_cons] at ordered
      unfold insert
      by_cases valueBefore : before value current = true
      · simp only [valueBefore, ↓reduceIte]
        apply List.Pairwise.cons
        · intro next nextMember
          have nextCases : next = current ∨ next ∈ rest := by simpa using nextMember
          rcases nextCases with equal | member
          · cases equal
            exact valueBefore
          · exact laws.trans valueBefore (ordered.1 next member)
        · exact List.Pairwise.cons ordered.1 ordered.2
      · simp only [valueBefore, Bool.false_eq_true, ↓reduceIte]
        apply List.Pairwise.cons
        · intro next nextMember
          have currentBeforeValue : before current value = true := by
            rcases laws.total value current with first | second
            · exact False.elim (valueBefore first)
            · exact second
          have nextCases : next = value ∨ next ∈ rest := by
            simpa using (List.Perm.mem_iff (insert_perm before value rest)).mp nextMember
          rcases nextCases with equal | member
          · cases equal
            exact currentBeforeValue
          · exact ordered.1 next member
        · exact ih ordered.2

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem insertionSort_sorted (before : α → α → Bool) (laws : LawfulTotalRelation before)
    (values : List α) : SortedBy before (insertionSort before values) := by
  induction values with
  | nil => simp [SortedBy, insertionSort]
  | cons value rest ih => exact insert_sorted before laws value ih

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem insertionSort_perm (before : α → α → Bool) (values : List α) :
    (insertionSort before values).Perm values := by
  induction values with
  | nil => exact List.Perm.refl _
  | cons value rest ih =>
      exact (insert_perm before value _).trans (List.Perm.cons value ih)

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
@[simp] theorem insertionSort_length (before : α → α → Bool) (values : List α) :
    (insertionSort before values).length = values.length :=
  (insertionSort_perm before values).length_eq

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem mem_insertionSort (before : α → α → Bool) (value : α) (values : List α) :
    value ∈ insertionSort before values ↔ value ∈ values :=
  List.Perm.mem_iff (insertionSort_perm before values)

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
/-- A sorted result packages both semantic obligations used by downstream clients. -/
structure Result (before : α → α → Bool) (input : List α) where
  output : List α
  sorted : SortedBy before output
  permutation : output.Perm input

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
/-- A sorting result stated entirely over representation-free vector semantics. -/
structure ModelResult (before : α → α → Bool) (input : VecSpec.Model α n) where
  output : List α
  sorted : SortedBy before output
  permutation : output.Perm (VecSpec.toList input)

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
def certifiedInsertionSort (before : α → α → Bool) (laws : LawfulTotalRelation before)
    (input : List α) : Result before input :=
  ⟨insertionSort before input, insertionSort_sorted before laws input,
    insertionSort_perm before input⟩

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
def certifiedModelInsertionSort (before : α → α → Bool) (laws : LawfulTotalRelation before)
    (input : VecSpec.Model α n) : ModelResult before input :=
  ⟨insertionSort before (VecSpec.toList input),
    insertionSort_sorted before laws (VecSpec.toList input),
    insertionSort_perm before (VecSpec.toList input)⟩

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
/-- Executable Array-backed realization of the semantic insertion sort. -/
def insertionSortVec (before : α → α → Bool) (input : Vec α n) : Vec α n :=
  Vec.ofListSized (insertionSort before input.toList) (by simp)

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
@[simp] theorem insertionSortVec_toList (before : α → α → Bool) (input : Vec α n) :
    (insertionSortVec before input).toList = insertionSort before input.toList := by
  simp [insertionSortVec]

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem insertionSortVec_sorted (before : α → α → Bool) (laws : LawfulTotalRelation before)
    (input : Vec α n) : SortedBy before (insertionSortVec before input).toList := by
  rw [insertionSortVec_toList]
  exact insertionSort_sorted before laws input.toList

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
theorem insertionSortVec_perm (before : α → α → Bool) (input : Vec α n) :
    (insertionSortVec before input).toList.Perm input.toList := by
  rw [insertionSortVec_toList]
  exact insertionSort_perm before input.toList

/- REF: docs/STDLIB_CONTAINERS.md#2-generic-sorting -/
@[simp] theorem ModelResult.output_length {n : Nat} {input : VecSpec.Model α n}
    (result : ModelResult before input) :
    result.output.length = n := by
  rw [result.permutation.length_eq, VecSpec.toList_length]

end Stdlib.Sort

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

import Stdlib.Containers.VecSpec

/-! A certified Array-backed realization of representation-free vector semantics. -/

namespace Stdlib

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- A finite sequence whose length is present in its type and checked against its array storage. -/
structure Vec (α : Type u) (n : Nat) where
  private data : Array α
  private size_eq : data.size = n

namespace Vec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def empty : Vec α 0 := ⟨#[], rfl⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def singleton (value : α) : Vec α 1 := ⟨#[value], rfl⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def ofList (values : List α) : Vec α values.length :=
  ⟨values.toArray, by simp⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Construct a vector at a caller-selected length after proving the list has that length. -/
def ofListSized (values : List α) (length_eq : values.length = n) : Vec α n :=
  length_eq ▸ ofList values

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Construct a vector at the exact length carried by an existing array. -/
def ofArray (values : Array α) : Vec α values.size := ⟨values, rfl⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The contiguous realization seam; proofs should normally prefer `toList`. -/
def toArray (values : Vec α n) : Array α := values.data

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def toList (values : Vec α n) : List α := values.data.toList

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def size (_values : Vec α n) : Nat := n

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def get? (values : Vec α n) (index : Nat) : Option α := values.data[index]?

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def get (values : Vec α n) (index : Fin n) : α :=
  values.data[index.val]'(by simp [values.size_eq])

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def set (values : Vec α n) (index : Fin n) (value : α) : Vec α n :=
  ⟨values.data.set index.val value (by simp [values.size_eq]), by
    simp [values.size_eq]⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Exchange two valid positions without changing the vector length. -/
def swap (values : Vec α n) (left right : Fin n) : Vec α n :=
  ⟨values.data.swap left.val right.val (by simp [values.size_eq]) (by simp [values.size_eq]),
    by simp [values.size_eq]⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def push (values : Vec α n) (value : α) : Vec α (n + 1) :=
  ⟨values.data.push value, by simp [values.size_eq]⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def append (left : Vec α n) (right : Vec α m) : Vec α (n + m) :=
  ⟨left.data ++ right.data, by simp [left.size_eq, right.size_eq]⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def map (f : α → β) (values : Vec α n) : Vec β n :=
  ⟨values.data.map f, by simp [values.size_eq]⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def foldl (f : σ → α → σ) (initial : σ) (values : Vec α n) : σ :=
  values.data.foldl f initial

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def toModel (values : Vec α n) : VecSpec.Model α n := values.get

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_empty : (empty : Vec α 0).toList = [] := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_singleton (value : α) : (singleton value).toList = [value] := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_ofList (values : List α) : (ofList values).toList = values := by
  simp [ofList, toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_ofListSized (values : List α) (length_eq : values.length = n) :
    (ofListSized values length_eq).toList = values := by
  cases length_eq
  exact toList_ofList values

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toArray_ofArray (values : Array α) : (ofArray values).toArray = values := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toArray_size (values : Vec α n) : values.toArray.size = n := values.size_eq

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toArray_toList (values : Vec α n) : values.toArray.toList = values.toList := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_length (values : Vec α n) : values.toList.length = n := by
  simpa [toList] using values.size_eq

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem size_index (values : Vec α n) : values.size = n := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_push (values : Vec α n) (value : α) :
    (values.push value).toList = values.toList ++ [value] := by
  simp [push, toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_append (left : Vec α n) (right : Vec α m) :
    (left.append right).toList = left.toList ++ right.toList := by
  simp [append, toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_map (f : α → β) (values : Vec α n) :
    (values.map f).toList = values.toList.map f := by
  simp [map, toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get?_ofList (values : List α) (index : Nat) :
    (ofList values).get? index = values[index]? := by
  simp [ofList, get?]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get?_eq_toList_get? (values : Vec α n) (index : Nat) :
    values.get? index = values.toList[index]? := by
  simp [get?, toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get?_fin (values : Vec α n) (index : Fin n) :
    values.get? index = some (values.get index) := by
  simp [get?, get, values.size_eq]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get?_eq_none_of_le (values : Vec α n) {index : Nat} (outOfBounds : n ≤ index) :
    values.get? index = none := by
  simp [get?, values.size_eq, Nat.not_lt.mpr outOfBounds]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get?_eq_none_iff (values : Vec α n) (index : Nat) :
    values.get? index = none ↔ n ≤ index := by
  simp [get?, values.size_eq, Nat.not_lt]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem foldl_eq_list_foldl (f : σ → α → σ) (initial : σ) (values : Vec α n) :
    values.foldl f initial = values.toList.foldl f initial := by
  simp [foldl, toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toModel_get (values : Vec α n) (index : Fin n) :
    values.toModel index = values.get index := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Central refinement bridge: semantic observation and executable list projection agree. -/
@[simp] theorem toModel_toList (values : Vec α n) :
    VecSpec.toList values.toModel = values.toList := by
  cases values with
  | mk data size_eq =>
    cases size_eq
    change List.ofFn (fun index : Fin data.size => data[index.val]) = data.toList
    rw [← Array.toList_ofFn]
    simp

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_set_self (values : Vec α n) (index : Fin n) (value : α) :
    (values.set index value).get index = value := by
  simp [set, get]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get_set_of_ne (values : Vec α n) {left right : Fin n} (different : left ≠ right)
    (value : α) : (values.set right value).get left = values.get left := by
  unfold set get
  apply Array.getElem_set_ne
  · simp [values.size_eq]
  · intro equal
    exact different (Fin.ext (Eq.symm equal))

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_swap_left (values : Vec α n) (left right : Fin n) :
    (values.swap left right).get left = values.get right := by
  simp [swap, get]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_swap_right (values : Vec α n) (left right : Fin n) :
    (values.swap left right).get right = values.get left := by
  simp [swap, get]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get_swap_of_ne (values : Vec α n) {left right index : Fin n}
    (notLeft : index ≠ left) (notRight : index ≠ right) :
    (values.swap left right).get index = values.get index := by
  unfold swap get
  apply Array.getElem_swap_of_ne
  · intro equal
    exact notLeft (Fin.ext equal)
  · intro equal
    exact notRight (Fin.ext equal)

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem size_swap (values : Vec α n) (left right : Fin n) :
    (values.swap left right).size = values.size := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem swap_swap (values : Vec α n) (left right : Fin n) :
    (values.swap left right).swap left right = values := by
  cases values with
  | mk data size_eq =>
    cases size_eq
    simp [swap]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem toList_swap_perm (values : Vec α n) (left right : Fin n) :
    (values.swap left right).toList.Perm values.toList := by
  exact Array.perm_iff_toList_perm.mp
    (Array.swap_perm (xs := values.data) (by simp [values.size_eq]) (by simp [values.size_eq]))

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_map (f : α → β) (values : Vec α n) (index : Fin n) :
    (values.map f).get index = f (values.get index) := by
  simp [map, get]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_push_prefix (values : Vec α n) (value : α) (index : Fin n) :
    (values.push value).get index.castSucc = values.get index := by
  unfold push get
  exact Array.getElem_push_lt (by simp [values.size_eq])

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_push_last (values : Vec α n) (value : α) :
    (values.push value).get ⟨n, by omega⟩ = value := by
  cases values with
  | mk data size_eq =>
    cases size_eq
    exact Array.getElem_push_eq

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_append_left (left : Vec α n) (right : Vec α m) (index : Fin n) :
    (left.append right).get (Fin.castAdd m index) = left.get index := by
  unfold append get
  exact Array.getElem_append_left (by simp [left.size_eq])

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_append_right (left : Vec α n) (right : Vec α m) (index : Fin m) :
    (left.append right).get (Fin.natAdd n index) = right.get index := by
  cases left with
  | mk leftData leftSize =>
    cases right with
    | mk rightData rightSize =>
      cases leftSize
      cases rightSize
      simp [append, get, Array.getElem_append_right]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get?_append_left (left : Vec α n) (right : Vec α m) {index : Nat}
    (inLeft : index < n) : (left.append right).get? index = left.get? index := by
  unfold append get?
  apply Array.getElem?_append_left
  simpa [left.size_eq] using inLeft

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get?_append_right (left : Vec α n) (right : Vec α m) {index : Nat}
    (inRight : n ≤ index) :
    (left.append right).get? index = right.get? (index - n) := by
  unfold append get?
  simpa [left.size_eq] using
    (Array.getElem?_append_right (xs := left.data) (ys := right.data)
      (i := index) (by simpa [left.size_eq] using inRight))

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Array-backed mapping implements the representation-free mapping operation. -/
@[simp] theorem toModel_map (f : α → β) (values : Vec α n) :
    (values.map f).toModel = VecSpec.map f values.toModel := by
  apply VecSpec.Model.ext
  intro index
  simp only [toModel]
  change (values.map f).get index = f (values.get index)
  exact get_map f values index

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Array-backed replacement implements representation-free replacement. -/
@[simp] theorem toModel_set (values : Vec α n) (index : Fin n) (value : α) :
    (values.set index value).toModel = VecSpec.set values.toModel index value := by
  apply VecSpec.Model.ext
  intro current
  simp only [toModel]
  by_cases equal : current = index
  · subst current
    simp [VecSpec.set]
  · rw [get_set_of_ne values equal]
    simp [VecSpec.set, equal]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Array-backed exchange implements representation-free exchange. -/
@[simp] theorem toModel_swap (values : Vec α n) (left right : Fin n) :
    (values.swap left right).toModel = VecSpec.swap values.toModel left right := by
  apply VecSpec.Model.ext
  intro current
  simp only [toModel]
  by_cases atLeft : current = left
  · subst current
    simp [VecSpec.swap]
  · by_cases atRight : current = right
    · subst current
      simp [VecSpec.swap, atLeft]
    · rw [get_swap_of_ne values atLeft atRight]
      simp [VecSpec.swap, atLeft, atRight]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Array concatenation implements representation-free vector concatenation. -/
@[simp] theorem toModel_append (left : Vec α n) (right : Vec α m) :
    (left.append right).toModel = VecSpec.append left.toModel right.toModel := by
  apply VecSpec.Model.ext
  intro index
  simp only [toModel]
  refine Fin.addCases ?_ ?_ index
  · intro leftIndex
    simp [VecSpec.append]
  · intro rightIndex
    simp [VecSpec.append]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Array push implements representation-free extension by one final value. -/
@[simp] theorem toModel_push (values : Vec α n) (value : α) :
    (values.push value).toModel = VecSpec.push values.toModel value := by
  apply VecSpec.Model.ext
  intro index
  simp only [toModel]
  simp only [VecSpec.push, VecSpec.append]
  refine Fin.addCases ?_ ?_ index
  · intro prefixIndex
    rw [Fin.addCases_left]
    change (values.push value).get (Fin.castAdd 1 prefixIndex) = values.get prefixIndex
    exact get_push_prefix values value prefixIndex
  · intro finalIndex
    rw [Fin.addCases_right]
    have finalIndex_eq : finalIndex = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst finalIndex
    change (values.push value).get ⟨n, by omega⟩ = value
    exact get_push_last values value

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem toModel_complete {left right : Vec α n}
    (equal : ∀ index, left.toModel index = right.toModel index) : left = right := by
  cases left with
  | mk leftData leftSize =>
    cases right with
    | mk rightData rightSize =>
      have dataEqual : leftData = rightData := by
        apply Array.ext
        · simp [leftSize, rightSize]
        · intro index hleft hright
          have index_lt : index < n := by rw [← leftSize]; exact hleft
          exact equal ⟨index, index_lt⟩
      subst rightData
      rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def arrayRepresentation (α : Type u) : VecSpec.Representation (Vec α) α where
  observe := toModel
  complete := toModel_complete

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The list model is complete: equal models imply equal vectors. -/
@[ext] theorem ext {left right : Vec α n} (equal : left.toList = right.toList) : left = right := by
  cases left with
  | mk leftData leftSize =>
    cases right with
    | mk rightData rightSize =>
      simp only [toList] at equal
      have dataEqual : leftData = rightData := Array.toList_inj.mp equal
      subst dataEqual
      rfl

end Vec
end Stdlib

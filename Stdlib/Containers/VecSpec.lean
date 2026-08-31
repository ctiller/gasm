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

/-! Representation-free semantics for finite indexed sequences. -/

namespace Stdlib.VecSpec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- A vector's semantic content: one value for every valid index. -/
abbrev Model (α : Type u) (n : Nat) := Fin n → α

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def get (model : Model α n) (index : Fin n) : α := model index

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def map (f : α → β) (model : Model α n) : Model β n := fun index => f (model index)

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Replace one semantic position without choosing a storage representation. -/
def set (model : Model α n) (index : Fin n) (value : α) : Model α n :=
  fun current => if current = index then value else model current

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Exchange two semantic positions without choosing a storage representation. -/
def swap (model : Model α n) (left right : Fin n) : Model α n :=
  fun current =>
    if current = left then model right
    else if current = right then model left
    else model current

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Concatenate two semantic vectors by splitting the combined finite index. -/
def append (left : Model α n) (right : Model α m) : Model α (n + m) :=
  Fin.addCases left right

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- Extend a semantic vector with one final value. -/
def push (model : Model α n) (value : α) : Model α (n + 1) :=
  append model (fun _ => value)

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def toList (model : Model α n) : List α := List.ofFn model

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_map (f : α → β) (model : Model α n) (index : Fin n) :
    get (map f model) index = f (get model index) := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_set_self (model : Model α n) (index : Fin n) (value : α) :
    get (set model index value) index = value := by
  simp [get, set]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get_set_of_ne (model : Model α n) {left right : Fin n} (different : left ≠ right)
    (value : α) : get (set model right value) left = get model left := by
  simp [get, set, different]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_swap_left (model : Model α n) (left right : Fin n) :
    get (swap model left right) left = get model right := by
  simp [get, swap]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_swap_right (model : Model α n) (left right : Fin n) :
    get (swap model left right) right = get model left := by
  by_cases equal : left = right
  · subst right
    simp [get, swap]
  · simp [get, swap, Ne.symm equal]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
theorem get_swap_of_ne (model : Model α n) {left right index : Fin n}
    (notLeft : index ≠ left) (notRight : index ≠ right) :
    get (swap model left right) index = get model index := by
  simp [get, swap, notLeft, notRight]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_append_left (left : Model α n) (right : Model α m) (index : Fin n) :
    get (append left right) (Fin.castAdd m index) = get left index := by
  simp [get, append]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_append_right (left : Model α n) (right : Model α m) (index : Fin m) :
    get (append left right) (Fin.natAdd n index) = get right index := by
  simp [get, append]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_push_prefix (model : Model α n) (value : α) (index : Fin n) :
    get (push model value) (Fin.castAdd 1 index) = get model index := by
  simp [push]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem get_push_last (model : Model α n) (value : α) :
    get (push model value) ⟨n, by omega⟩ = value := by
  change get (push model value) (Fin.natAdd n (0 : Fin 1)) = value
  change get (append model (fun _ : Fin 1 => value)) (Fin.natAdd n 0) = value
  rw [get_append_right]
  rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[ext] theorem Model.ext {left right : Model α n} (equal : ∀ index, left index = right index) :
    left = right := funext equal

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_length (model : Model α n) : (toList model).length = n := by
  simp [toList]

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- A certified representation is completely characterized by its semantic observation. -/
structure Representation (Rep : Nat → Type u) (α : Type v) where
  observe : {n : Nat} → Rep n → Model α n
  complete : ∀ {n : Nat} {left right : Rep n},
    (∀ index, observe left index = observe right index) → left = right

end Stdlib.VecSpec

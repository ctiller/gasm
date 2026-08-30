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
def toList (model : Model α n) : List α := List.ofFn model

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

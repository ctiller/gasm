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

/-! A lossless boundary between specialized `ByteArray` execution and indexed byte vectors. -/

namespace ByteArray

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def toVec (bytes : ByteArray) : Stdlib.Vec UInt8 bytes.size :=
  Stdlib.Vec.ofArray bytes.data

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def toModel (bytes : ByteArray) : Stdlib.VecSpec.Model UInt8 bytes.size :=
  bytes.toVec.toModel

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toVec_get? (bytes : ByteArray) (index : Nat) :
    bytes.toVec.get? index = bytes[index]? := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toVec_get (bytes : ByteArray) (index : Fin bytes.size) :
    bytes.toVec.get index = bytes[index.val]'index.isLt := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toVec_toModel (bytes : ByteArray) : bytes.toVec.toModel = bytes.toModel := rfl

end ByteArray

namespace Stdlib.Vec

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
def toByteArray (bytes : Vec UInt8 n) : ByteArray :=
  ⟨bytes.toArray⟩

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toByteArray_size (bytes : Vec UInt8 n) : bytes.toByteArray.size = n :=
  bytes.toArray_size

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toByteArray_get? (bytes : Vec UInt8 n) (index : Nat) :
    bytes.toByteArray[index]? = bytes.get? index := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toByteArray_get (bytes : Vec UInt8 n) (index : Fin n) :
    bytes.toByteArray[index.val]'(by simp) = bytes.get index := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toByteArray_toVec (bytes : ByteArray) : bytes.toVec.toByteArray = bytes := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
/-- The reverse roundtrip is heterogeneous only because the vector length is type-indexed. -/
theorem toVec_toByteArray (bytes : Vec UInt8 n) : HEq bytes.toByteArray.toVec bytes := by
  cases bytes with
  | mk data size_eq =>
    cases size_eq
    rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toList_toVec (bytes : ByteArray) :
    bytes.toVec.toList = bytes.data.toList := rfl

/- REF: docs/STDLIB_CONTAINERS.md#3-vector-model -/
@[simp] theorem toByteArray_data_toList (bytes : Vec UInt8 n) :
    bytes.toByteArray.data.toList = bytes.toList := rfl

end Stdlib.Vec

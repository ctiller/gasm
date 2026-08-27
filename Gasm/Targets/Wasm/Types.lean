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

namespace Gasm.Targets.Wasm

open Gasm.Core

/- REF: wasm-syntax-types#value-types -/
/-- WebAssembly primitive numeric and reference value types. -/
inductive ValType where
  | i32 : ValType
  | i64 : ValType
  | f32 : ValType
  | f64 : ValType
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-types#block-types -/
/-- WebAssembly block return type descriptor. -/
inductive BlockType where
  | empty : BlockType
  | val   : ValType → BlockType
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-types#composite-types -/
/-- Function type signature classifying parameter types and return types. -/
structure FuncType where
  params  : List ValType
  results : List ValType
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-types#limits -/
/-- Memory limits specified in 64 KiB pages. -/
structure Limits where
  min : UInt32
  max : Option UInt32 := none
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-types#memory-types -/
/-- Memory type classifying linear memory allocations. -/
structure MemType where
  limits : Limits
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-modules#imports -/
/-- Import descriptor kind. -/
inductive ImportDesc where
  | func (typeIdx : Nat) : ImportDesc
  | mem  (type : MemType) : ImportDesc
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-modules#imports -/
/-- Imported entity declaration from a foreign module namespace. -/
structure Import where
  module : String
  name   : String
  desc   : ImportDesc
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-modules#exports -/
/-- Export descriptor kind. -/
inductive ExportDesc where
  | func (funcIdx : Nat) : ExportDesc
  | mem  (memIdx : Nat)  : ExportDesc
  deriving Repr, DecidableEq, BEq, Inhabited

/- REF: wasm-syntax-modules#exports -/
/-- Exported entity declaration available to host embedder. -/
structure Export where
  name : String
  desc : ExportDesc
  deriving Repr, DecidableEq, BEq, Inhabited

end Gasm.Targets.Wasm

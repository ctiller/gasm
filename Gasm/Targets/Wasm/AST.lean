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
import Gasm.Targets.Wasm.Types

namespace Gasm.Targets.Wasm

open Gasm.Core

/- REF: wasm-syntax-instructions#instructions -/
/-- Structured WebAssembly instructions. -/
inductive WasmInstr where
  -- Control flow
  | unreachable : WasmInstr
  | nop         : WasmInstr
  | block       : BlockType → List WasmInstr → WasmInstr
  | loop        : BlockType → List WasmInstr → WasmInstr
  | if_else     : BlockType → List WasmInstr → List WasmInstr → WasmInstr
  | br          : Nat → WasmInstr
  | br_if       : Nat → WasmInstr
  | return_op   : WasmInstr
  | call        : Nat → WasmInstr

  -- Parametric & Variable
  | drop        : WasmInstr
  | select_op   : WasmInstr
  | local_get   : Nat → WasmInstr
  | local_set   : Nat → WasmInstr
  | local_tee   : Nat → WasmInstr
  | global_get  : Nat → WasmInstr
  | global_set  : Nat → WasmInstr

  -- Memory
  | i32_load    : Nat → Nat → WasmInstr  -- align, offset
  | i32_load8_u : Nat → Nat → WasmInstr
  | i64_load    : Nat → Nat → WasmInstr
  | i32_store   : Nat → Nat → WasmInstr
  | i64_store   : Nat → Nat → WasmInstr
  | i32_store8  : Nat → Nat → WasmInstr
  | memory_size : WasmInstr
  | memory_grow : WasmInstr

  -- Numeric Constants
  | i32_const   : UInt32 → WasmInstr
  | i64_const   : UInt64 → WasmInstr

  -- 32-bit Integer Comparisons & Arithmetic
  | i32_eqz     : WasmInstr
  | i32_eq      : WasmInstr
  | i32_ne      : WasmInstr
  | i32_lt_u    : WasmInstr
  | i32_gt_u    : WasmInstr
  | i32_le_u    : WasmInstr
  | i32_ge_u    : WasmInstr
  | i32_add     : WasmInstr
  | i32_sub     : WasmInstr
  | i32_mul     : WasmInstr
  | i32_div_u   : WasmInstr
  | i32_rem_u   : WasmInstr
  | i32_and     : WasmInstr
  | i32_or      : WasmInstr
  | i32_xor     : WasmInstr
  | i32_shl     : WasmInstr
  | i32_shr_u   : WasmInstr

  -- 64-bit Integer Comparisons & Arithmetic
  | i64_eqz     : WasmInstr
  | i64_eq      : WasmInstr
  | i64_ne      : WasmInstr
  | i64_lt_u    : WasmInstr
  | i64_gt_u    : WasmInstr
  | i64_le_u    : WasmInstr
  | i64_ge_u    : WasmInstr
  | i64_add     : WasmInstr
  | i64_sub     : WasmInstr
  | i64_mul     : WasmInstr
  | i64_div_u   : WasmInstr
  | i64_rem_u   : WasmInstr
  | i64_and     : WasmInstr
  | i64_or      : WasmInstr
  | i64_xor     : WasmInstr
  | i64_shl     : WasmInstr
  | i64_shr_u   : WasmInstr

  -- Conversions
  | i32_wrap_i64    : WasmInstr
  | i64_extend_i32_u: WasmInstr
  deriving Repr, Inhabited

end Gasm.Targets.Wasm

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
import Gasm.Core.Rng
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Semantics

namespace Gasm.Targets.Wasm.Fuzzable

open Gasm.Core
open Gasm.Targets.Wasm

/- REF: wasm-syntax-instructions#instructions -/
/-- Curated 32-bit edge case values for WebAssembly numeric fuzzing. -/
def curated32BitValues : List UInt32 := [
  0, 1, 2, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000,
  0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555
]

/- REF: wasm-syntax-instructions#instructions -/
/-- Curated 64-bit edge case values for WebAssembly numeric fuzzing. -/
def curated64BitValues : List UInt64 := [
  0, 1, 2, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0x7FFFFFFF, 0x80000000,
  0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF,
  0xAAAAAAAAAAAAAAAA, 0x5555555555555555
]

/- REF: wasm-syntax-instructions#instructions -/
/-- Small bounded iteration counts for structured control-flow fuzzing. Loop-bearing test cases
    must provably terminate on both the Lean model and the host oracle, so loop trip counts are
    drawn from this curated small range rather than the full 32-bit edge-case set. -/
def curatedLoopBoundValues : List UInt32 := [0, 1, 2, 3, 5, 8, 13, 20]

/- REF: wasm-syntax-instructions#instructions -/
/-- Declares whether an instruction can be directly tested in isolation on host runtimes. -/
def canFuzzWasmRuntime (instr : WasmInstr) : Bool :=
  match instr with
  | .unreachable => false
  | .call _      => false
  | _            => true

/- REF: wasm-syntax-instructions#instructions -/
/-- Generates initial test machine states (curated edge cases + pseudo-random) for any Wasm instruction. -/
def generateWasmFuzzStates (instr : WasmInstr) (rng : FuzzerRng) (randCount : Nat := 8) : Prod (List WasmMachineState) FuzzerRng := Id.run do
  let mut states : List WasmMachineState := []
  let mut curRng := rng

  match instr with
  -- Binary 32-bit Arithmetic & Bitwise
  | .i32_add | .i32_sub | .i32_mul | .i32_and | .i32_or | .i32_xor
  | .i32_eq | .i32_ne | .i32_lt_u | .i32_gt_u | .i32_le_u | .i32_ge_u =>
    for v1 in curated32BitValues.take 5 do
      for v2 in curated32BitValues.take 5 do
        states := states ++ [{ stack := [WasmVal.i32 v2, WasmVal.i32 v1] }]
    for _ in [0:randCount] do
      let (u1, r1) := curRng.nextUInt32
      let (u2, r2) := r1.nextUInt32
      states := states ++ [{ stack := [WasmVal.i32 u2, WasmVal.i32 u1] }]
      curRng := r2

  -- 32-bit Division & Remainder (non-zero divisor)
  | .i32_div_u | .i32_rem_u =>
    let nonZero := curated32BitValues.filter (fun x => x != 0)
    for v1 in curated32BitValues.take 5 do
      for v2 in nonZero.take 5 do
        states := states ++ [{ stack := [WasmVal.i32 v2, WasmVal.i32 v1] }]
    for _ in [0:randCount] do
      let (u1, r1) := curRng.nextUInt32
      let (u2, r2) := r1.nextUInt32
      let divisor := if u2 == 0 then 1 else u2
      states := states ++ [{ stack := [WasmVal.i32 divisor, WasmVal.i32 u1] }]
      curRng := r2

  -- 32-bit Shifts
  | .i32_shl | .i32_shr_u =>
    for v in curated32BitValues.take 6 do
      for s in [0, 1, 7, 15, 31, 32, 33, 63] do
        states := states ++ [{ stack := [WasmVal.i32 (UInt32.ofNat s), WasmVal.i32 v] }]

  -- 32-bit Unary
  | .i32_eqz =>
    for v in curated32BitValues do
      states := states ++ [{ stack := [WasmVal.i32 v] }]

  -- Binary 64-bit Arithmetic & Bitwise
  | .i64_add | .i64_sub | .i64_mul | .i64_and | .i64_or | .i64_xor
  | .i64_eq | .i64_ne | .i64_lt_u | .i64_gt_u | .i64_le_u | .i64_ge_u =>
    for v1 in curated64BitValues.take 5 do
      for v2 in curated64BitValues.take 5 do
        states := states ++ [{ stack := [WasmVal.i64 v2, WasmVal.i64 v1] }]
    for _ in [0:randCount] do
      let (u1, r1) := curRng.next
      let (u2, r2) := r1.next
      states := states ++ [{ stack := [WasmVal.i64 u2, WasmVal.i64 u1] }]
      curRng := r2

  -- 64-bit Division & Remainder (non-zero divisor)
  | .i64_div_u | .i64_rem_u =>
    let nonZero := curated64BitValues.filter (fun x => x != 0)
    for v1 in curated64BitValues.take 5 do
      for v2 in nonZero.take 5 do
        states := states ++ [{ stack := [WasmVal.i64 v2, WasmVal.i64 v1] }]
    for _ in [0:randCount] do
      let (u1, r1) := curRng.next
      let (u2, r2) := r1.next
      let divisor := if u2 == 0 then 1 else u2
      states := states ++ [{ stack := [WasmVal.i64 divisor, WasmVal.i64 u1] }]
      curRng := r2

  -- 64-bit Shifts
  | .i64_shl | .i64_shr_u =>
    for v in curated64BitValues.take 6 do
      for s in [0, 1, 7, 31, 63, 64, 65, 127] do
        states := states ++ [{ stack := [WasmVal.i64 (UInt64.ofNat s), WasmVal.i64 v] }]

  -- 64-bit Unary
  | .i64_eqz =>
    for v in curated64BitValues do
      states := states ++ [{ stack := [WasmVal.i64 v] }]

  -- Variable & Stack operations
  | .drop =>
    states := [{ stack := [WasmVal.i32 42] }, { stack := [WasmVal.i64 0x123456789ABCDEF0] }]
  | .select_op =>
    states := [
      { stack := [WasmVal.i32 1, WasmVal.i32 20, WasmVal.i32 10] },
      { stack := [WasmVal.i32 0, WasmVal.i32 20, WasmVal.i32 10] },
      { stack := [WasmVal.i32 1, WasmVal.i64 200, WasmVal.i64 100] },
      { stack := [WasmVal.i32 0, WasmVal.i64 200, WasmVal.i64 100] }
    ]
  | .local_get idx =>
    let locs := List.replicate (idx + 1) (WasmVal.i32 123)
    states := [{ locals := locs }]
  | .local_set idx =>
    let locs := List.replicate (idx + 1) (WasmVal.i32 0)
    states := [{ stack := [WasmVal.i32 999], locals := locs }]
  | .local_tee idx =>
    let locs := List.replicate (idx + 1) (WasmVal.i32 0)
    states := [{ stack := [WasmVal.i32 999], locals := locs }]

  -- Memory Loads & Stores
  | .i32_store _ _offset | .i32_store8 _ _offset =>
    let mem := WasmMem.ofBytes (ByteArray.mk (Array.replicate 65536 (0 : UInt8)))
    states := [
      { stack := [WasmVal.i32 0x12345678, WasmVal.i32 16], memory := mem },
      { stack := [WasmVal.i32 0xFFFFFFFF, WasmVal.i32 64], memory := mem }
    ]
  | .i64_store _ _offset =>
    let mem := WasmMem.ofBytes (ByteArray.mk (Array.replicate 65536 (0 : UInt8)))
    states := [
      { stack := [WasmVal.i64 0x1122334455667788, WasmVal.i32 16], memory := mem }
    ]
  | .i32_load _ _offset =>
    let mem := WasmMem.ofBytes (ByteArray.mk (Array.replicate 65536 (0x55 : UInt8)))
    states := [{ stack := [WasmVal.i32 16], memory := mem }]
  | .i64_load _ _offset =>
    let mem := WasmMem.ofBytes (ByteArray.mk (Array.replicate 65536 (0xAA : UInt8)))
    states := [{ stack := [WasmVal.i32 16], memory := mem }]
  | .memory_size =>
    let mem := WasmMem.ofBytes (ByteArray.mk (Array.replicate 65536 (0 : UInt8)))
    states := [{ memory := mem }]
  | .memory_grow =>
    let mem := WasmMem.ofBytes (ByteArray.mk (Array.replicate 65536 (0 : UInt8)))
    states := [{ stack := [WasmVal.i32 1], memory := mem }]

  -- Conversions
  | .i32_wrap_i64 =>
    for v in curated64BitValues do
      states := states ++ [{ stack := [WasmVal.i64 v] }]
  | .i64_extend_i32_u =>
    for v in curated32BitValues do
      states := states ++ [{ stack := [WasmVal.i32 v] }]

  -- Control Flow & Constants
  | .i32_const _ => states := [{}]
  | .i64_const _ => states := [{}]
  | .nop => states := [{}]
  | _ => states := [{}]

  (states, curRng)

end Gasm.Targets.Wasm.Fuzzable

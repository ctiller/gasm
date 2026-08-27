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
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Binary
import Gasm.Targets.Wasm.Text
import Gasm.Targets.Wasm.Linker
import Gasm.Targets.WASI.ABI
import Spikes.Spike2Fibonacci.Spec

namespace Spikes.Spike2Fibonacci.Wasm

open Gasm.Core
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Spikes.Spike2Fibonacci

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- Pure UTF-8 byte payload for all 90 Fibonacci lines formatted with LF. -/
def fibFormattedBytes : ByteArray :=
  formattedFibonacciWasmOutput.toUTF8

/- REF: docs/TARGETS/WASI.md#31-wasiciovect-structure -/
/-- WASI ciovec buffer pointing to offset 0x10 with total formatted length. -/
def fibCiovec : ByteArray :=
  encodeCiovec 0x10 fibFormattedBytes.size.toUInt32

/- REF: docs/TARGETS/WASM.md#2-structured-ast-control-flow -/
/-- Structured WebAssembly instructions implementing the iterative 64-bit Fibonacci algorithm.
    Parameters: [n : i64] (local 0)
    Locals: [a : i64 (local 1), b : i64 (local 2), temp : i64 (local 3)]
    Returns: [result i64] -/
def fibIterWasmInstructions : List WasmInstr := [
  -- a = 0, b = 1
  .i64_const 0,
  .local_set 1,
  .i64_const 1,
  .local_set 2,

  -- while (n != 0) { temp = a + b; a = b; b = temp; n = n - 1; }
  .block .empty [
    .loop .empty [
      .local_get 0,
      .i64_eqz,
      .br_if 1,

      -- temp = a + b
      .local_get 1,
      .local_get 2,
      .i64_add,
      .local_set 3,

      -- a = b
      .local_get 2,
      .local_set 1,

      -- b = temp
      .local_get 3,
      .local_set 2,

      -- n = n - 1
      .local_get 0,
      .i64_const 1,
      .i64_sub,
      .local_set 0,

      .br 0
    ]
  ],

  -- Return a
  .local_get 1
]

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Exported/callable Fibonacci function in WebAssembly module. -/
def fibIterFunction : WasmFunction := {
  name       := "fibIter"
  params     := [.i64]
  results    := [.i64]
  locals     := [.i64, .i64, .i64]
  body       := fibIterWasmInstructions
  exportName := some "fibIter"
}

/- REF: docs/TARGETS/WASM.md#2-structured-ast-control-flow -/
/-- Structured WebAssembly instructions for the WASI _start entry point. -/
def spike2WasmInstructions : List WasmInstr := [
  -- 1. Call fd_write(fd=1, iovs_ptr=0, iovs_len=1, nwritten_ptr=8)
  .i32_const 1,
  .i32_const 0,
  .i32_const 1,
  .i32_const 8,
  .call 0,
  .drop,

  -- 2. Call proc_exit(rval=0)
  .i32_const 0,
  .call 1
]

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Function definition for _start. -/
def spike2StartFunction : WasmFunction := {
  name       := "_start"
  params     := []
  results    := []
  locals     := []
  body       := spike2WasmInstructions
  exportName := some "_start"
}

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Data segments initializing memory for Spike 2. -/
def spike2DataSegments : List WasmDataSegment := [
  { offset := 0x00, data := fibCiovec },
  { offset := 0x10, data := fibFormattedBytes }
]

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Complete WebAssembly WASI module definition for Spike 2. -/
def spike2WasmModule : WasmModule :=
  buildWasiModule spike2StartFunction [fibIterFunction] spike2DataSegments

/- REF: docs/TARGETS/WASM.md#4-text-format-wat-formatting -/
/-- WebAssembly text format (.wat) representation for Spike 2. -/
def spike2Wat : String :=
  emitWasmText spike2WasmModule

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Type signatures for Spike 2 functions and imports. -/
def spike2TypeSignatures : List FuncType := [
  fdWriteType,
  procExitType,
  { params := [], results := [] },
  { params := [.i64], results := [.i64] }
]

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- WebAssembly binary bytecode (.wasm) representation for Spike 2. -/
def spike2WasmBinary : Except String ByteArray :=
  emitWasmBinary spike2WasmModule spike2TypeSignatures

end Spikes.Spike2Fibonacci.Wasm

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

namespace Spikes.Spike1Hello.Wasm

open Gasm.Core
open Gasm.Targets.Wasm
open Gasm.Targets.WASI

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- Pure byte sequence for 'Hello, World!\n' placed in Wasm linear memory. -/
def helloMessage : ByteArray :=
  "Hello, World!\n".toUTF8

/- REF: docs/TARGETS/WASI.md#31-wasiciovect-structure -/
/-- ciovec buffer structure pointing to memory offset 0x10 with length 14. -/
def helloCiovec : ByteArray :=
  encodeCiovec 0x10 helloMessage.size.toUInt32

/- REF: docs/TARGETS/WASM.md#2-structured-ast-control-flow -/
/-- Structured WebAssembly instructions for the WASI _start entry point. -/
def spike1WasmInstructions : List WasmInstr := [
  -- 1. Call fd_write(fd=1 (stdout), iovs_ptr=0, iovs_len=1, nwritten_ptr=8)
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
def spike1StartFunction : WasmFunction := {
  name       := "_start"
  params     := []
  results    := []
  locals     := []
  body       := spike1WasmInstructions
  exportName := some "_start"
}

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Data segments initializing memory for Spike 1. -/
def spike1DataSegments : List WasmDataSegment := [
  { offset := 0x00, data := helloCiovec },
  { offset := 0x10, data := helloMessage }
]

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Complete WebAssembly WASI module definition for Spike 1. -/
def spike1WasmModule : WasmModule :=
  buildWasiModule spike1StartFunction [] spike1DataSegments

/- REF: docs/TARGETS/WASM.md#4-text-format-wat-formatting -/
/-- WebAssembly text format (.wat) representation for Spike 1. -/
def spike1Wat : String :=
  emitWasmText spike1WasmModule

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Type signatures for Spike 1 functions and imports. -/
def spike1TypeSignatures : List FuncType := [
  fdWriteType,
  procExitType,
  { params := [], results := [] }
]

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- WebAssembly binary bytecode (.wasm) representation for Spike 1. -/
def spike1WasmBinary : Except String ByteArray :=
  emitWasmBinary spike1WasmModule spike1TypeSignatures

end Spikes.Spike1Hello.Wasm

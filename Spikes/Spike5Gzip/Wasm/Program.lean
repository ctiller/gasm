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
import Stdlib.Zlib.Wasm
import Spikes.Spike5Gzip.Spec

namespace Spikes.Spike5Gzip.Wasm

open Gasm.Core
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Stdlib.Zlib.Wasm
open Spikes.Spike5Gzip

/- REF: docs/TARGETS/WASI.md#31-wasiciovect-structure -/
/-- ciovec buffer structure pointing to memory offset 0x10 with compressed stream length. -/
def gzipCiovec : ByteArray :=
  encodeCiovec 0x10 canonicalCompressedStream.size.toUInt32

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Structured WebAssembly instructions for the WASI _start entry point: writes compressed stream to stdout. -/
def spike5WasmInstructions : List WasmInstr := [
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

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Function definition for _start. -/
def spike5StartFunction : WasmFunction := {
  name       := "_start"
  params     := []
  results    := []
  locals     := []
  body       := spike5WasmInstructions
  exportName := some "_start"
}

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Data segments initializing memory for Spike 5 with GZIP compressed payload. -/
def spike5DataSegments : List WasmDataSegment := [
  { offset := 0x00, data := gzipCiovec },
  { offset := 0x10, data := canonicalCompressedStream }
]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Complete WebAssembly WASI module definition for Spike 5. -/
def spike5WasmModule : WasmModule :=
  buildWasiModule spike5StartFunction [] spike5DataSegments

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- WebAssembly text format (.wat) representation for Spike 5. -/
def spike5Wat : String :=
  emitWasmText spike5WasmModule

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Type signatures for Spike 5 functions and imports. -/
def spike5TypeSignatures : List FuncType := [
  fdWriteType,
  procExitType,
  { params := [], results := [] }
]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- WebAssembly binary bytecode (.wasm) representation for Spike 5. -/
def spike5WasmBinary : Except String ByteArray :=
  emitWasmBinary spike5WasmModule spike5TypeSignatures

end Spikes.Spike5Gzip.Wasm

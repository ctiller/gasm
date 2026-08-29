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
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
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
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI
open Stdlib.Zlib.Wasm
open Spikes.Spike5Gzip

/- REF: docs/TARGETS/WASI.md#31-wasiciovect-structure -/
/-- The fixed ABI workspace for Spike 5's WASI stream boundary.  The first
    ciovec directs `fd_read` to the mutable input buffer; the second is filled
    with the actual byte count before `fd_write`.  No application payload is
    embedded in the module image. -/
def gzipWasiWorkspace : ByteArray :=
  encodeCiovec 0x20 65504 ++
    ByteArray.mk #[0, 0, 0, 0] ++
    encodeCiovec 0x20 0 ++
    ByteArray.mk #[0, 0, 0, 0]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Structured WebAssembly instructions for the WASI _start entry point.
    The program reads stdin through `fd_read` into linear memory, carries the
    returned byte count into the output ciovec, then writes precisely those
    bytes.  The compression lowering is intentionally not claimed here: this
    establishes the real external input boundary that its future Zlib-library
    call must sit between. -/
def spike5WasmInstructions : List WasmInstr := [
  -- 1. fd_read(fd=0, iovs_ptr=0, iovs_len=1, nread_ptr=8)
  .i32_const 0,
  .i32_const 0,
  .i32_const 1,
  .i32_const 8,
  .call 0,
  .drop,

  -- 2. Copy nread into the output ciovec's length field at byte 16.
  .i32_const 12,
  .i32_const 8,
  .i32_load 2 0,
  .i32_store 2 4,

  -- 3. fd_write(fd=1, iovs_ptr=12, iovs_len=1, nwritten_ptr=20)
  .i32_const 1,
  .i32_const 12,
  .i32_const 1,
  .i32_const 20,
  .call 1,
  .drop,

  -- 4. Call proc_exit(rval=0)
  .i32_const 0,
  .call 2
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
/-- Data segments initializing only the WASI stream workspace.  In particular,
    this target no longer embeds `canonicalCompressedStream`. -/
def spike5DataSegments : List WasmDataSegment := [
  { offset := 0x00, data := gzipWasiWorkspace }
]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Complete WebAssembly WASI module definition for Spike 5. -/
def spike5WasmModule : WasmModule :=
  buildWasiStdinModule spike5StartFunction [] spike5DataSegments

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- WebAssembly text format (.wat) representation for Spike 5. -/
def spike5Wat : String :=
  emitWasmText spike5WasmModule

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- Type signatures for Spike 5 functions and imports. -/
def spike5TypeSignatures : List FuncType := [
  fdReadType,
  fdWriteType,
  procExitType,
  { params := [], results := [] }
]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#42-webassembly-wasi-wasisnapshotpreview1 -/
/-- WebAssembly binary bytecode (.wasm) representation for Spike 5. -/
def spike5WasmBinary : Except String ByteArray :=
  emitWasmBinary spike5WasmModule spike5TypeSignatures

-- A concrete non-canonical smoke vector for the *artifact* boundary.  This is
-- not a compression-equivalence theorem; it prevents the old, payload-embedded
-- implementation from silently returning by checking that fd_read's supplied
-- byte is the byte presented to fd_write.
#guard runWasiTrace spike5WasmInstructions spike5DataSegments "Q".toUTF8
  ["fd_read", "fd_write", "proc_exit"] =
  [Inject.inject (ConsoleEvent.out "Q"), Inject.inject (ProcessEvent.exit 0)]

end Spikes.Spike5Gzip.Wasm

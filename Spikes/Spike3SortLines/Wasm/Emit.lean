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
import Gasm.Core.Verification
import Gasm.Targets.WASI.ABI
import Spikes.Spike3SortLines.Wasm.Program
import Spikes.Spike3SortLines.Wasm.Equivalence

open Gasm.Core.Verification
open Gasm.Targets.WASI
open Spikes.Spike3SortLines.Wasm

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- CLI Emitter Target for WebAssembly Spike 3:
    Serializes and writes sort.wasm binary and sort.wat text to disk strictly through
    the verified program contract (`VerifiedWasmProgram`). -/
def main : IO UInt32 := do
  let wasmBinary ← IO.ofExcept (emitVerifiedWasmBinary spike3VerifiedWasmProgram)
  let wasmText := emitVerifiedWasmText spike3VerifiedWasmProgram

  let binPath := "sort.wasm"
  let watPath := "sort.wat"

  IO.println s!"[*] Emitting {wasmBinary.size} bytes to {binPath}..."
  IO.FS.writeBinFile binPath wasmBinary
  IO.println s!"[+] Generated WebAssembly binary: {binPath}"

  IO.println s!"[*] Emitting WAT text to {watPath}..."
  IO.FS.writeFile watPath wasmText
  IO.println s!"[+] Generated WebAssembly text: {watPath}"

  return 0

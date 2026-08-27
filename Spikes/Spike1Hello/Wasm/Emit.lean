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
import Spikes.Spike1Hello.Wasm.Program
import Spikes.Spike1Hello.Wasm.Equivalence

open Spikes.Spike1Hello.Wasm

/- REF: docs/SPIKES.md#2-spike-1-windows-x64-hello-world-pe-binary -/
/-- CLI Emitter Target: Serializes and writes hello.wat and hello.wasm to disk via verified program contract. -/
def main : IO UInt32 := do
  let watPath := "hello.wat"
  let wasmPath := "hello.wasm"

  let watText := Gasm.Targets.WASI.emitVerifiedWasmText spike1VerifiedWasmProgram
  let wasmBytes ← IO.ofExcept (Gasm.Targets.WASI.emitVerifiedWasmBinary spike1VerifiedWasmProgram)

  IO.println s!"[*] Emitting WAT text format to {watPath}..."
  IO.FS.writeFile watPath watText
  IO.println s!"[+] Generated WAT file: {watPath}"

  IO.println s!"[*] Emitting {wasmBytes.size} bytes to {wasmPath}..."
  IO.FS.writeBinFile wasmPath wasmBytes
  IO.println s!"[+] Generated WASM binary: {wasmPath}"

  return 0

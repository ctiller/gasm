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
import Spikes.Common.WasmHostRunner

open Spikes.Spike1Hello.Wasm
open Spikes.Common.WasmHostRunner

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- CLI Test Target: Verifies WebAssembly execution via in-Lean trace checking and host CLI runner.
    Exit codes: `0` = in-Lean check passed AND a host runner actually executed and verified the
    binary; `1` = a genuine verification failure (in-Lean mismatch, or a found host runner
    produced the wrong output); `2` = no host Wasm CLI runner was found on PATH at all — the
    in-Lean check passed but host-runtime validation did NOT run (Law 13(4): an oracle that
    cannot run must fail the run, never report a synthesized "100% sound" pass). -/
def main : IO UInt32 := do
  IO.println "[*] 1. In-Lean Formal Verification..."
  let inLeanTrace := Gasm.Targets.WASI.runWasiTrace spike1WasmInstructions spike1DataSegments
  let specTrace := Gasm.Effects.runModelTrace (Spikes.Spike1Hello.helloWorldSpec : Gasm.Effects.TraceM Gasm.Effects.AnyEvent Unit)
  if inLeanTrace == specTrace then
    IO.println "[+] PASS: In-Lean formal semantic trace matches high-level specification."
  else
    IO.println s!"[!] FAIL: In-Lean trace mismatch:\n  Got: {repr inLeanTrace}\n  Expected: {repr specTrace}"
    return 1

  IO.println "[*] 2. Host Wasm Runtime Verification..."
  let wasmPath := "hello.wasm"
  if !(← (System.FilePath.mk wasmPath).pathExists) then
    IO.FS.writeBinFile wasmPath (← IO.ofExcept (Gasm.Targets.WASI.emitVerifiedWasmBinary spike1VerifiedWasmProgram))

  match ← tryHostRunners wasmPath (fun exitCode stdout => exitCode == 0 && stdout.trimAscii.toString == "Hello, World!") with
  | .passed cmd =>
    IO.println s!"[+] PASS: Executed and verified successfully via host runtime: '{cmd}'."
    return 0
  | .mismatch cmd exitCode stdout stderr =>
    IO.println s!"[!] FAIL: Host runner '{cmd}' failed with exit code {exitCode}."
    IO.println s!"    Stdout: {repr stdout}"
    IO.println s!"    Stderr: {repr stderr}"
    return 1
  | .runnerAbsent =>
    IO.println "[!] SKIP: No external Wasm CLI runner (node, wasmtime, wasmer, deno) detected on PATH."
    IO.println "    Host-runtime validation did NOT run. The in-Lean formal trace check above passed, but that is NOT a substitute for host execution — zero external validation occurred."
    return 2

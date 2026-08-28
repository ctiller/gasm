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
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Wasm.Program
import Spikes.Spike3SortLines.Wasm.Equivalence
import Spikes.Common.WasmHostRunner

open Gasm.Core.Verification
open Gasm.Targets.WASI
open Spikes.Spike3SortLines
open Spikes.Spike3SortLines.Wasm

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- CLI Test Target for WebAssembly Spike 3:
    1. In-Lean Formal Verification: Executes the verified program inside the formal Wasm semantic interpreter.
    2. Host Runtime Verification: Executes the emitted Wasm binary via host Node.js WASI runtime with piped stdin across multiple datasets. -/
def main : IO UInt32 := do
  IO.println "=== Running Spike 3 (WebAssembly / WASI Line Sorter) Test Suite ==="

  -- 1. In-Lean Formal Trace Verification
  IO.println "[*] 1. In-Lean Formal Semantic Verification..."
  
  -- Test Vector 1: Canonical 3-line input
  let trace1 := runWasiTrace spike3WasmInstructions spike3DataSegments defaultSampleInput ["fd_read", "fd_write", "proc_exit"]
  if trace1 == specTraceCanonical then
    IO.println "[+] PASS: In-Lean formal semantic trace matches canonical specification."
  else
    IO.eprintln s!"[!] FAIL: In-Lean trace mismatch on canonical input:\n  Got: {repr trace1}\n  Expected: {repr specTraceCanonical}"
    return 1

  -- Test Vector 2: Empty input
  let traceEmpty := runWasiTrace spike3WasmInstructions spike3DataSegments ByteArray.empty ["fd_read", "fd_write", "proc_exit"]
  let expectedEmpty := [Gasm.Effects.Inject.inject (Gasm.Effects.ProcessEvent.exit 0)]
  if traceEmpty == expectedEmpty then
    IO.println "[+] PASS: In-Lean formal semantic trace matches empty input specification."
  else
    IO.eprintln s!"[!] FAIL: In-Lean trace mismatch on empty input:\n  Got: {repr traceEmpty}\n  Expected: {repr expectedEmpty}"
    return 1

  -- Test Vector 3: 4 arbitrary lines
  let input4 := "zebra\r\nelephant\r\nmonkey\r\ngiraffe\r\n".toUTF8
  let trace4 := runWasiTrace spike3WasmInstructions spike3DataSegments input4 ["fd_read", "fd_write", "proc_exit"]
  let expected4 : List Gasm.Effects.AnyEvent := [
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "elephant"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "\r\n"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "giraffe"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "\r\n"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "monkey"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "\r\n"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "zebra"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ConsoleEvent.out "\r\n"),
    Gasm.Effects.Inject.inject (Gasm.Effects.ProcessEvent.exit 0)
  ]
  if trace4 == expected4 then
    IO.println "[+] PASS: In-Lean formal semantic trace correctly sorts 4 arbitrary lines."
  else
    IO.eprintln s!"[!] FAIL: In-Lean trace mismatch on 4-line input:\n  Got: {repr trace4}\n  Expected: {repr expected4}"
    return 1

  -- 2. Host Wasm Runtime Verification (Node.js WASI Preview 1)
  IO.println "[*] 2. Host Wasm Runtime Verification (Node.js WASI)..."
  let wasmPath := "sort.wasm"
  if !(← (System.FilePath.mk wasmPath).pathExists) then
    IO.FS.writeBinFile wasmPath (← IO.ofExcept (emitVerifiedWasmBinary spike3VerifiedWasmProgram))

  let nodeScript := Spikes.Common.WasmHostRunner.nodeWasiScript wasmPath (pipeStdin := true)

  -- Spawns `node` directly with `stdin := .piped` (via `IO.Process.output`'s `input?`
  -- parameter, which writes through `Handle.putStr` -- the same raw-UTF-8-no-BOM
  -- primitive `IO.FS.writeFile` uses) instead of shelling out to
  -- `powershell.exe -Command "Get-Content ... -Raw | node -e ..."`. That PowerShell
  -- pipe re-encoded the file's content a second time on its way into node's stdin,
  -- and was observed injecting a UTF-8 BOM (`EF BB BF`) at the start of the piped
  -- bytes on some runs, corrupting the first line the sorter read. Writing node's
  -- stdin directly from Lean removes that intermediary (and the file + cleanup it
  -- required) entirely, so the bytes node receives are exactly the bytes `input`
  -- names -- and this is also what makes this test genuinely portable: it no longer
  -- hardcodes `powershell.exe` (docs/CI.md #4), matching Spike 1/2's Wasm tests.
  let runHostWithInput (input : String) : IO (String × UInt32) := do
    let out ← IO.Process.output {
      cmd := "node"
      args := #["-e", nodeScript]
    } (some input)
    return (out.stdout, out.exitCode)

  try
    -- Host Test A: 3 lines
    let (stdoutA, exitCodeA) ← runHostWithInput "cherry\r\napple\r\nbanana\r\n"
    let expectedA := "apple\r\nbanana\r\ncherry\r\n"
    if exitCodeA != 0 || stdoutA != expectedA then
      IO.eprintln s!"[!] FAIL Host Test A: Expected {repr expectedA}, got {repr stdoutA} (exit {exitCodeA})"
      return 1
    IO.println "[PASS] Host Test A: 3 unsorted lines sorted successfully via Node.js WASI."

    -- Host Test B: 4 lines
    let (stdoutB, exitCodeB) ← runHostWithInput "zebra\r\nelephant\r\nmonkey\r\ngiraffe\r\n"
    let expectedB := "elephant\r\ngiraffe\r\nmonkey\r\nzebra\r\n"
    if exitCodeB != 0 || stdoutB != expectedB then
      IO.eprintln s!"[!] FAIL Host Test B: Expected {repr expectedB}, got {repr stdoutB} (exit {exitCodeB})"
      return 1
    IO.println "[PASS] Host Test B: 4 arbitrary lines sorted successfully via Node.js WASI."

    -- Host Test C: Presorted input
    let (stdoutC, exitCodeC) ← runHostWithInput "alpha\r\nbeta\r\ngamma\r\n"
    let expectedC := "alpha\r\nbeta\r\ngamma\r\n"
    if exitCodeC != 0 || stdoutC != expectedC then
      IO.eprintln s!"[!] FAIL Host Test C: Expected {repr expectedC}, got {repr stdoutC} (exit {exitCodeC})"
      return 1
    IO.println "[PASS] Host Test C: Presorted input preserved via Node.js WASI."

    IO.println "=== All Spike 3 Wasm Tests Passed Successfully! ==="
    return 0
  catch e =>
    IO.eprintln s!"[!] FAIL: Could not execute host runner: {e}"
    return 1
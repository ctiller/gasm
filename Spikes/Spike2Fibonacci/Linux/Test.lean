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
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Linux.Equivalence

open Gasm.Core.Verification
open Spikes.Spike2Fibonacci
open Spikes.Spike2Fibonacci.Linux

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- CLI Test Target: Executes fib_linux and verifies output matches expected Fibonacci sequence. -/
def main : IO UInt32 := do
  let exePath := "./fib_linux"
  if !(← (System.FilePath.mk exePath).pathExists) then
    IO.FS.writeBinFile exePath (emitVerifiedLinuxExecutable spike2VerifiedProgram)

  IO.println s!"[*] Testing binary execution: {exePath}..."
  try
    let _ ← IO.Process.run {
      cmd := "chmod"
      args := #["+x", exePath]
    }
    let child ← IO.Process.spawn {
      cmd := exePath
      stdout := .piped
      stderr := .piped
    }
    let stdout ← child.stdout.readToEnd
    let exitCode ← child.wait

    IO.println s!"[*] Captured Output Length: {stdout.length} chars"
    IO.println s!"[*] Exit Code: {exitCode}"

    if exitCode == 0 && stdout == formattedFibonacciWindowsOutput then
      IO.println "[+] PASS: Spike 2 Linux executable verified successfully."
      return 0
    else
      IO.println s!"[!] FAIL: Expected exit code 0 and exact match of formatted output, got code {exitCode}"
      return 1
  catch e =>
    IO.println s!"[!] FAIL: Could not execute {exePath}: {e}"
    IO.println "    Make sure to run 'lake exe spike2_fibonacci_linux' first to emit the binary."
    return 1

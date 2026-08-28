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
import Spikes.Spike1Hello.Linux.Equivalence

open Gasm.Core.Verification
open Spikes.Spike1Hello.Linux

/- REF: docs/TARGETS/LINUX.md#spikes-verification -/
/-- CLI Test Target: Executes hello_linux and verifies output matches expected Hello World string. -/
def main : IO UInt32 := do
  let exePath := "./hello_linux"
  if !(← (System.FilePath.mk exePath).pathExists) then
    IO.FS.writeBinFile exePath (emitVerifiedLinuxExecutable spike1VerifiedProgram)

  IO.println s!"[*] Testing binary execution: {exePath}..."
  try
    -- Ensure executable permission on Linux
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

    IO.println s!"[*] Captured Output: {repr stdout}"
    IO.println s!"[*] Exit Code: {exitCode}"

    if exitCode == 0 && stdout.trimAscii.toString == "Hello, World!" then
      IO.println "[+] PASS: Spike 1 Linux executable verified successfully."
      return 0
    else
      IO.println s!"[!] FAIL: Expected exit code 0 and 'Hello, World!', got code {exitCode} and output {repr stdout}"
      return 1
  catch e =>
    IO.println s!"[!] FAIL: Could not execute {exePath}: {e}"
    IO.println "    Make sure to run 'lake exe spike1_hello_linux' first to emit the binary."
    return 1

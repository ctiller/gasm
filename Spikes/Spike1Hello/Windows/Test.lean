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

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- CLI Test Target: Executes hello.exe and verifies output matches expected Hello World string. -/
def main : IO UInt32 := do
  let exePath := ".\\hello.exe"
  
  IO.println s!"[*] Testing binary execution: {exePath}..."
  try
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
      IO.println "[+] PASS: Spike 1 Windows executable verified successfully."
      return 0
    else
      IO.println s!"[!] FAIL: Expected exit code 0 and 'Hello, World!', got code {exitCode} and output {repr stdout}"
      return 1
  catch e =>
    IO.println s!"[!] FAIL: Could not execute {exePath}: {e}"
    IO.println "    Make sure to run 'lake exe spike1_hello_windows' first to emit the binary."
    return 1

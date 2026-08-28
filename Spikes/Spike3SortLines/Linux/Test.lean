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
import Gasm.Core.Verification
import Spikes.Spike3SortLines.Spec
import Spikes.Spike3SortLines.Linux.Program
import Spikes.Spike3SortLines.Linux.Equivalence

namespace Spikes.Spike3SortLines.Linux

open Gasm.Core.Verification

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Comprehensive test suite for Linux Spike 3: verifies sorting functional correctness, permutation soundness, and stdin-piped binary execution. -/
def runTests : IO UInt32 := do
  IO.println "=== Running Spike 3 Linux (Stdin Lexicographical Sorter) Test Suite ==="

  -- 1. Functional Sorting Unit Tests
  let test1 := sortStrings []
  if test1 != [] then
    IO.eprintln "FAILED: Empty list sort failed"
    return 1

  let test2 := sortStrings ["apple"]
  if test2 != ["apple"] then
    IO.eprintln "FAILED: Single element sort failed"
    return 1

  let test3 := sortStrings ["cherry", "apple", "banana"]
  if test3 != ["apple", "banana", "cherry"] then
    IO.eprintln "FAILED: 3-element list sort failed"
    return 1

  IO.println "[PASS] Functional string sorting unit tests."

  -- 2. Test Emitted Linux Binary Execution
  let exePath := "./sort_lines_linux"
  if !(← (System.FilePath.mk exePath).pathExists) then
    IO.FS.writeBinFile exePath (emitVerifiedLinuxExecutable spike3VerifiedProgram)
  let _ ← IO.Process.run {
    cmd := "chmod"
    args := #["+x", exePath]
  }

  let runWithInput (input : String) : IO (String × UInt32) := do
    let tmpFile := "spike3_test_in.tmp"
    IO.FS.writeFile tmpFile input
    let out ← IO.Process.output {
      cmd := "sh"
      args := #["-c", s!"{exePath} < {tmpFile}"]
    }
    return (out.stdout, out.exitCode)

  IO.println s!"[*] Testing binary execution with piped stdin: {exePath}..."
  try
    let (stdout, exitCode) ← runWithInput "cherry\r\napple\r\nbanana\r\n"

    IO.println s!"[*] Captured Output: {repr stdout}"
    IO.println s!"[*] Exit Code: {exitCode}"

    let expectedOutput := "apple\r\nbanana\r\ncherry\r\n"
    if exitCode == 0 && stdout == expectedOutput then
      IO.println "[+] PASS: Spike 3 Linux executable verified successfully."
      return 0
    else
      IO.println s!"[!] FAIL: Expected exit code 0 and {repr expectedOutput}, got code {exitCode} and {repr stdout}"
      return 1
  catch e =>
    IO.println s!"[!] FAIL: Could not execute {exePath}: {e}"
    return 1

end Spikes.Spike3SortLines.Linux

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- CLI Test Target: delegates to runTests. -/
def main : IO UInt32 :=
  Spikes.Spike3SortLines.Linux.runTests

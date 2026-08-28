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
import Spikes.Spike3SortLines.Windows.Program
import Spikes.Spike3SortLines.Windows.Equivalence

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core.Verification

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Comprehensive test suite for Spike 3: verifies sorting functional correctness, permutation soundness, and stdin-piped binary execution. -/
def runTests : IO UInt32 := do
  IO.println "=== Running Spike 3 (Stdin Lexicographical Sorter) Test Suite ==="

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

  let test4 := sortStrings ["delta", "beta", "alpha", "gamma", "epsilon"]
  if test4 != ["alpha", "beta", "delta", "epsilon", "gamma"] then
    IO.eprintln "FAILED: 5-element list sort failed"
    return 1

  let test5 := sortStrings ["banana", "apple", "banana", "apple"]
  if test5 != ["apple", "apple", "banana", "banana"] then
    IO.eprintln "FAILED: Duplicate element sort failed"
    return 1

  IO.println "[PASS] Functional string sorting unit tests (empty, single, 3-elem, 5-elem, duplicates)."

  -- 2. Verified Program Contract Summary
  IO.println s!"[DEBUG] asmTraceEmpty:       {repr asmTraceEmpty}"
  IO.println s!"[DEBUG] modelTraceEmpty:     {repr modelTraceEmpty}"
  IO.println s!"[DEBUG] asmTraceCanonical:   {repr asmTraceCanonical}"
  IO.println s!"[DEBUG] modelTraceCanonical: {repr modelTraceCanonical}"
  IO.println s!"[PASS] VerifiedProgram Contract: {spike3VerifiedProgram.name} validated mathematically."
  IO.println s!"       Machine Instructions: {spike3Instructions.length}"
  IO.println s!"       Emitted Text Bytes:   {spike3Executable.textBytes.size}"
  IO.println s!"       Emitted Rdata Bytes:  {spike3Executable.rdataBytes.size}"

  -- 3. Binary Execution Tests (with Piped Stdin Inputs)
  let exePath := ".\\spike3_sort.exe"
  if !(← (System.FilePath.mk "spike3_sort.exe").pathExists) then
    IO.FS.writeBinFile "spike3_sort.exe" (emitVerifiedExecutable spike3VerifiedProgram)
  IO.println s!"[*] Testing binary execution with piped stdin: {exePath}..."

  -- Feeds `input` to the child process's stdin via Lean's own `IO.Process.output`
  -- (which spawns the child with `stdin := .piped` and writes with `Handle.putStr`,
  -- the same raw-UTF-8-no-BOM primitive `IO.FS.writeFile` itself uses -- see
  -- `Init/System/IO.lean`'s `Process.output`). This previously shelled out to
  -- `powershell.exe -Command "Get-Content ... -Raw | ..."`, which piped the file's
  -- content through a second text-mode re-encoding step; PowerShell's own stdin/pipe
  -- encoding is configuration-dependent and was observed injecting a UTF-8 BOM
  -- (`EF BB BF`) at the start of the piped bytes on some runs, corrupting the first
  -- line of input the sorter saw. Spawning the child directly and writing its stdin
  -- ourselves removes that intermediary (and the file + cleanup it required)
  -- entirely, so the bytes the sorter receives are exactly the bytes `input` names.
  let runWithInput (input : String) : IO (String × UInt32) := do
    let out ← IO.Process.output {
      cmd := exePath
      args := #[]
    } (some input)
    if out.exitCode != 0 then
      IO.eprintln s!"[DEBUG CMD ERROR] stderr: {repr out.stderr}, stdout: {repr out.stdout}"
    return (out.stdout, out.exitCode)

  try
    -- Test Case A: 3 lines ("cherry\r\napple\r\nbanana\r\n")
    let (stdoutA, exitCodeA) ← runWithInput "cherry\r\napple\r\nbanana\r\n"
    IO.println s!"[*] Test A Captured Output: {repr stdoutA}"
    IO.println s!"[*] Test A Exit Code: {exitCodeA}"
    let expectedA := "apple\r\nbanana\r\ncherry\r\n"
    if exitCodeA != 0 || stdoutA != expectedA then
      IO.eprintln s!"[!] FAIL Test A: Expected {repr expectedA}, got {repr stdoutA} (exit {exitCodeA})"
      return 1
    IO.println "[PASS] Test A: 3 unsorted lines correctly parsed and sorted."

    -- Test Case B: 4 lines ("zebra\r\nmonkey\r\ngiraffe\r\nelephant\r\n")
    let (stdoutB, exitCodeB) ← runWithInput "zebra\r\nmonkey\r\ngiraffe\r\nelephant\r\n"
    IO.println s!"[*] Test B Captured Output: {repr stdoutB}"
    IO.println s!"[*] Test B Exit Code: {exitCodeB}"
    let expectedB := "elephant\r\ngiraffe\r\nmonkey\r\nzebra\r\n"
    if exitCodeB != 0 || stdoutB != expectedB then
      IO.eprintln s!"[!] FAIL Test B: Expected {repr expectedB}, got {repr stdoutB} (exit {exitCodeB})"
      return 1
    IO.println "[PASS] Test B: 4 arbitrary lines correctly parsed and sorted in-place."

    -- Test Case C: Already sorted lines ("alpha\r\nbeta\r\ngamma\r\n")
    let (stdoutC, exitCodeC) ← runWithInput "alpha\r\nbeta\r\ngamma\r\n"
    let expectedC := "alpha\r\nbeta\r\ngamma\r\n"
    if exitCodeC != 0 || stdoutC != expectedC then
      IO.eprintln s!"[!] FAIL Test C: Expected {repr expectedC}, got {repr stdoutC} (exit {exitCodeC})"
      return 1
    IO.println "[PASS] Test C: Presorted input preserved."

    IO.println "=== All Spike 3 Tests Passed Successfully! ==="
    return 0
  catch e =>
    IO.eprintln s!"[!] FAIL: Could not execute {exePath}: {e}"
    return 1

end Spikes.Spike3SortLines.Windows

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Main entry point for Spike 3 test runner executable. -/
def main : IO UInt32 :=
  Spikes.Spike3SortLines.Windows.runTests

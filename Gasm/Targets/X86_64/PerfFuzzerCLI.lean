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
import Gasm.Targets.X86_64.Uop
import Gasm.Targets.X86_64.Performance
import Gasm.Targets.X86_64.Fuzzer

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Fuzzer

/- REF: intel-sdm#vol=1;sec=3.2;part=32-overview-of-the-basic-execution-environment -/
/-- CLI entry point for the x86-64 performance analysis & cycle bounds invariant fuzzer. -/
def main (args : List String) : IO UInt32 := do
  IO.println "================================================================================"
  IO.println "             GASM X86-64 MICROARCHITECTURAL PERFORMANCE FUZZER                  "
  IO.println "================================================================================"

  let mut count := 100
  let mut length := 20
  let mut iterations := 10
  let mut fuzzLoops := false
  let mut seedVal : UInt64 := 133742

  let mut i := 0
  while i < args.length do
    match args[i]! with
    | "--count" =>
      if i + 1 < args.length then
        count := args[i + 1]!.toNat?.getD 100
        i := i + 2
      else i := i + 1
    | "--length" =>
      if i + 1 < args.length then
        length := args[i + 1]!.toNat?.getD 20
        i := i + 2
      else i := i + 1
    | "--iterations" =>
      if i + 1 < args.length then
        iterations := args[i + 1]!.toNat?.getD 10
        i := i + 2
      else i := i + 1
    | "--loops" =>
      fuzzLoops := true
      i := i + 1
    | "--seed" =>
      if i + 1 < args.length then
        seedVal := args[i + 1]!.toNat?.getD 133742 |>.toUInt64
        i := i + 2
      else i := i + 1
    | _ => i := i + 1

  let modeStr := if fuzzLoops then s!"Deterministic Loops ({iterations} iters/loop)" else "Basic Blocks"
  IO.println s!"[Configuration] Mode: {modeStr}, Programs: {count}, Length: {length} instrs, Profile: Intel Golden Cove"
  IO.println "[Invariants Checked] Monotonicity (0 < minCycles <= nominalCycles <= maxCycles), Uop Conservation"
  IO.println "--------------------------------------------------------------------------------"

  -- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law
  -- TC17 vacuity floor (TCB.md T11-b): `--count 0` must not fuzz nothing and still report
  -- "100% SUCCESS" — a run with no programs has verified no invariant and must hard-fail.
  if count == 0 then
    IO.println "[VACUITY FLOOR TRIPPED] --count 0 requests zero fuzzed programs — 0 vectors exercised verifies nothing."
    IO.println "A fuzzer run that exercises zero programs has verified no cycle-bound invariant — this is a hard FAIL, not a clean PASS (TCB.md T11-b)."
    IO.println "================================================================================"
    return 1

  let mut rng : FuzzerRng := { seed := seedVal }
  let mut passedCount := 0
  let mut failedCount := 0

  for pIdx in [0:count] do
    let (result, nextRng) := if fuzzLoops then
      let ((prog, bodyUops), nRng) := generateRandomLoopProgram iterations length rng
      (verifyLoopPerfInvariants prog iterations bodyUops goldenCoveProfile, nRng)
    else
      let (prog, nRng) := generateRandomProgram length rng
      (verifyPerfInvariants prog goldenCoveProfile, nRng)
    rng := nextRng

    if result.passed then
      passedCount := passedCount + 1
      if pIdx < 5 || pIdx % 25 == 0 || pIdx == count - 1 then
        IO.println s!"  [PASS] Program #{pIdx + 1}: {result.progLength} instrs, {result.totalUops} uops => Cycle Bounds [{result.minCycles}, {result.nominalCycles}, {result.maxCycles}]"
    else
      failedCount := failedCount + 1
      let errMsg := match result.errorMsg with | some m => m | none => "Unknown error"
      IO.println s!"  [FAIL] Program #{pIdx + 1}: {errMsg}"

  let pct := (passedCount.toFloat / count.toFloat) * 100.0
  IO.println "================================================================================"
  IO.println s!"Fuzzing Complete! Passed: {passedCount} / {count} ({pct}%), Failed: {failedCount}"
  IO.println "================================================================================"

  if failedCount == 0 then
    IO.println "[+] ALL PERFORMANCE & CYCLE BOUND INVARIANTS HELD WITH 100% SUCCESS!"
    IO.println "[Evidentiary Scope] Validated against exactly 1 microarchitectural profile (Intel Golden Cove model; no hardware oracle)."
    return 0
  else
    return 1

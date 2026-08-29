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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.NASM
import Gasm.Targets.X86_64.EncodingFuzzer
import Spikes.Spike1Hello.Windows.Program
import Spikes.Spike2Fibonacci.Windows.Program

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.EncodingFuzzer
open Spikes.Spike1Hello.Windows
open Spikes.Spike2Fibonacci.Windows

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- CLI runner for the x86-64 binary encoding differential test against NASM. -/
def main (args : List String) : IO UInt32 := do
  IO.println "================================================================================"
  IO.println "             GASM X86-64 BINARY ENCODING DIFFERENTIAL FUZZER                   "
  IO.println "                     (Oracle: Netwide Assembler NASM)                           "
  IO.println "================================================================================"

  let mut count := 100
  let mut length := 20
  let mut seedVal : UInt64 := 9876543210123
  let mut nasmOverride : Option String := none

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
    | "--seed" =>
      if i + 1 < args.length then
        seedVal := args[i + 1]!.toNat?.getD 9876543210123 |>.toUInt64
        i := i + 2
      else i := i + 1
    | "--nasm" =>
      if i + 1 < args.length then
        nasmOverride := some args[i + 1]!
        i := i + 2
      else i := i + 1
    | _ => i := i + 1

  let nasmPath ← findNasmPath nasmOverride
  IO.println ("[Configuration] Programs: " ++ toString count ++ ", Length: " ++ toString length ++ " instrs, Oracle: " ++ nasmPath)
  IO.println "--------------------------------------------------------------------------------"

  -- 0. Law 13(4) mandatory oracle control vectors: must pass before ANY fuzzed result counts.
  -- Both controls route through `verifyDifferential` itself (see EncodingFuzzer.lean's
  -- `runNasmControlVectors`), so a hardcoded/short-circuited `verifyDifferential` is caught
  -- here too, not just a broken standalone comparison helper.
  IO.println "[Control] Verifying NASM oracle against known-good/known-bad control vectors..."
  match ← runNasmControlVectors nasmPath with
  | .error err =>
    IO.println s!"❌ NASM CONTROL VECTOR FAILURE (aborting — no fuzzed result below would be trustworthy):\n{err}"
    return 2
  | .ok () =>
    pure ()
  IO.println "[+] PASS: NASM oracle control vectors verified (positive + negative)."
  IO.println "--------------------------------------------------------------------------------"

  -- 1. Test Spike 1 Hello World Program
  IO.println "[Test 1/3] Verifying Spike 1 (Windows Hello World) instruction sequence against NASM..."
  let spike1Res ← verifyDifferential spike1Instructions nasmPath ".tmp_diff_spike1"
  if !spike1Res.passed then
    let err := spike1Res.errorMsg.getD "Unknown error"
    IO.println ("❌ Spike 1 Differential Mismatch:\n" ++ err)
    pure 1
  else
    IO.println ("[+] PASS: Spike 1 (" ++ toString spike1Instructions.length ++ " instrs, " ++ toString spike1Res.gasmBytes.size ++ " bytes) matched NASM byte-for-byte.")

    -- 2. Test Spike 2 Fibonacci Programs (fibIter and spike2 full driver)
    IO.println "[Test 2/3] Verifying Spike 2 (Fibonacci Iterative & Driver) instruction sequences against NASM..."
    let fibIterRes ← verifyDifferential fibIterInstructions nasmPath ".tmp_diff_fibiter"
    if !fibIterRes.passed then
      let err := fibIterRes.errorMsg.getD "Unknown error"
      IO.println ("❌ Spike 2 fibIter Differential Mismatch:\n" ++ err)
      pure 1
    else
      let spike2Res ← verifyDifferential spike2Instructions nasmPath ".tmp_diff_spike2"
      if !spike2Res.passed then
        let err := spike2Res.errorMsg.getD "Unknown error"
        IO.println ("❌ Spike 2 Driver Differential Mismatch:\n" ++ err)
        pure 1
      else
        IO.println ("[+] PASS: Spike 2 (" ++ toString spike2Instructions.length ++ " instrs, " ++ toString spike2Res.gasmBytes.size ++ " bytes) matched NASM byte-for-byte.")

        -- 3. Run Randomized Differential Fuzzer
        -- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law
        -- TC17 vacuity floor (docs/REVIEW.md Law 13): `--count 0` must not silently skip the randomized
        -- suite and still report "100% BYTE-FOR-BYTE EXACT EQUALITY" — 0 programs exercised
        -- verifies nothing, and must hard-fail rather than fall through to a clean summary.
        if count == 0 then
          IO.println "[Test 3/3] --count 0 requests zero randomized programs."
          IO.println "[VACUITY FLOOR TRIPPED] 0 randomized encoding vectors were exercised — this is a hard FAIL, not a clean PASS (docs/REVIEW.md Law 13)."
          pure 1
        else
          IO.println ("[Test 3/3] Running " ++ toString count ++ " randomized comprehensive programs (" ++ toString length ++ " instrs each)...")
          let (passed, failed, firstError) ← runEncodingFuzzerSuite count length seedVal (some nasmPath)

          IO.println "================================================================================"
          let pctStr := toString ((passed.toFloat / count.toFloat) * 100.0)
          IO.println ("Differential Fuzzing Complete! Passed: " ++ toString passed ++ " / " ++ toString count ++ " (" ++ pctStr ++ "%), Failed: " ++ toString failed)
          IO.println "================================================================================"

          if failed > 0 then
            let err := firstError.getD ""
            IO.println ("❌ First Failure Details:\n" ++ err)
            pure 1
          else
            IO.println "[+] ALL ENCODINGS MATCHED NASM OUTPUT WITH 100% BYTE-FOR-BYTE EXACT EQUALITY!"
            IO.println "[Evidentiary Scope] Validated against exactly 1 oracle (NASM assembler)."
            pure 0


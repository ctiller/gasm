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
import Gasm.Effects.Trace
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Executable
import Gasm.Execution.QEMUAArch64
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.AArch64BareMetal.Program
import Spikes.Spike1Hello.AArch64BareMetal.Equivalence

open Gasm.Effects
open Gasm.Targets.AArch64.BareMetal
open Spikes.Spike1Hello
open Spikes.Spike1Hello.AArch64BareMetal

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- CLI Test Target: Verifies Bare Metal AArch64 execution via in-Lean trace checking and QEMU hardware runner.
    Exit codes: `0` = in-Lean check passed AND QEMU executed and verified the binary;
    `1` = verification failure (in-Lean mismatch or QEMU output mismatch);
    `2` = QEMU not found (see `findQemuSystemPath`). -/
def main : IO UInt32 := do
  IO.println "[*] 1. In-Lean Formal Verification..."
  let inLeanTrace := runBareMetalTrace spike1AArch64BareMetalInstructions spike1AArch64BareMetalExecutable.load
  let specTrace := runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  if inLeanTrace == specTrace then
    IO.println "[+] PASS: In-Lean formal semantic trace matches high-level specification."
  else
    IO.println s!"[!] FAIL: In-Lean trace mismatch:\n  Got: {repr inLeanTrace}\n  Expected: {repr specTrace}"
    return 1

  IO.println "[*] 2. QEMU Bare Metal System Verification..."
  let elfPath := "spike1_hello_aarch64_baremetal.elf"
  if !(← (System.FilePath.mk elfPath).pathExists) then
    IO.FS.writeBinFile elfPath (emitVerifiedBareMetalExecutable spike1AArch64VerifiedBareMetalProgram)

  match ← Gasm.Execution.QEMUAArch64.runBareMetal elfPath "Hello, World!\n" 0 with
  | .passed =>
    IO.println "[+] PASS: Spike 1 Bare Metal AArch64 ELF64 verified successfully via QEMU."
    return 0
  | .mismatch exitCode stdout stderr =>
    IO.println s!"[!] FAIL: Unexpected QEMU execution result."
    IO.println s!"    Stdout: {repr stdout}"
    IO.println s!"    Stderr: {repr stderr}"
    IO.println s!"    Exit Code: {exitCode} (expected 0)"
    return 1
  | .runnerAbsent =>
    IO.println "[!] SKIP: qemu-system-aarch64 not found (checked GASM_QEMU_AARCH64, PATH, and standard locations)."
    IO.println "    Host-runtime QEMU validation did NOT run. The in-Lean formal trace check passed."
    return 2

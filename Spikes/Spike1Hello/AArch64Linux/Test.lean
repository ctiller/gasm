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
import Gasm.Targets.AArch64.Semantics
import Gasm.Execution.QEMUAArch64
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.AArch64Linux.Program
import Spikes.Spike1Hello.AArch64Linux.Equivalence

open Gasm.Effects
open Gasm.Core.Verification
open Spikes.Spike1Hello
open Spikes.Spike1Hello.AArch64Linux

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- CLI Test Target: Verifies Linux AArch64 execution via in-Lean trace checking and QEMU hardware runner.
    Exit codes: `0` = in-Lean check passed AND QEMU executed and verified the binary;
    `1` = verification failure (in-Lean mismatch or QEMU output mismatch);
    `2` = QEMU user emulator not found. -/
def main : IO UInt32 := do
  IO.println "[*] 1. In-Lean Formal Verification..."
  let inLeanTrace := Gasm.Targets.AArch64.runAArch64Trace (Event := AnyEvent) spike1AArch64LinuxInstructions spike1AArch64LinuxExecutable.load
  let specTrace := runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  if inLeanTrace == specTrace then
    IO.println "[+] PASS: In-Lean formal semantic trace matches high-level specification."
  else
    IO.println s!"[!] FAIL: In-Lean trace mismatch:\n  Got: {repr inLeanTrace}\n  Expected: {repr specTrace}"
    return 1

  IO.println "[*] 2. QEMU Linux User-Mode Verification..."
  let elfPath := "spike1_hello_aarch64_linux"
  if !(← (System.FilePath.mk elfPath).pathExists) then
    IO.FS.writeBinFile elfPath (emitVerifiedAArch64LinuxExecutable spike1AArch64LinuxVerifiedProgram)

  match ← Gasm.Execution.QEMUAArch64.runLinux elfPath ByteArray.empty "Hello, World!\n" 0 with
  | .passed =>
    IO.println "[+] PASS: Spike 1 Linux AArch64 ELF64 verified successfully via QEMU user-mode."
    return 0
  | .mismatch exitCode stdout stderr =>
    IO.println s!"[!] FAIL: Unexpected QEMU execution result."
    IO.println s!"    Stdout: {repr stdout}"
    IO.println s!"    Stderr: {repr stderr}"
    IO.println s!"    Exit Code: {exitCode} (expected 0)"
    return 1
  | .runnerAbsent =>
    IO.println "[!] SKIP: qemu-aarch64 not found (checked GASM_QEMU_USER_AARCH64, PATH, and standard locations)."
    IO.println "    Host-runtime QEMU validation did NOT run. The in-Lean formal trace check passed."
    return 2

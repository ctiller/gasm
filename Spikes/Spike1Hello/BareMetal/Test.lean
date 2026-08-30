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
import Gasm.Effects.Trace
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Executable
import Gasm.Targets.BareMetal.QEMU
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.BareMetal.Program
import Spikes.Spike1Hello.BareMetal.Equivalence

open Gasm.Effects
open Gasm.Core.Platform
open Gasm.Targets.BareMetal
open Spikes.Spike1Hello
open Spikes.Spike1Hello.BareMetal

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- CLI Test Target: Verifies Bare Metal x86-64 execution via in-Lean trace checking and QEMU hardware runner.
    Exit codes: `0` = in-Lean check passed AND QEMU executed and verified the binary;
    `1` = verification failure (in-Lean mismatch or QEMU output mismatch);
    `2` = QEMU not found (see `findQemuPath`: `GASM_QEMU` env var, PATH, or standard
    install locations). -/
def main : IO UInt32 := do
  IO.println "[*] 1. In-Lean Formal Verification..."
  let inLeanTrace := runBareMetalTrace spike1BareMetalInstructions spike1BareMetalExecutable.load
  let specTrace := runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)
  if inLeanTrace == specTrace then
    IO.println "[+] PASS: In-Lean formal semantic trace matches high-level specification."
  else
    IO.println s!"[!] FAIL: In-Lean trace mismatch:\n  Got: {repr inLeanTrace}\n  Expected: {repr specTrace}"
    return 1

  IO.println "[*] 2. QEMU Bare Metal System Verification..."
  let elfPath := "spike1_hello_baremetal.elf"
  if !(← (System.FilePath.mk elfPath).pathExists) then
    match emitVerifiedProgram spike1VerifiedBareMetalProgram with
    | .error message =>
      IO.eprintln s!"[!] Verified emission failed: {message}"
      return 1
    | .ok elfBytes =>
      IO.FS.writeBinFile elfPath elfBytes

  -- Resolution order (see Gasm.Targets.BareMetal.findQemuPath): explicit GASM_QEMU env var,
  -- then PATH, then standard Windows/Linux install locations. `none` means the oracle is
  -- genuinely absent -- reported as exit 2 (hardware validation did NOT run), never silently
  -- treated as a pass, per docs/SPIKES.md §4 item 5's honest-runner convention.
  match ← findQemuPath with
  | none =>
    IO.println "[!] SKIP: qemu-system-x86_64 not found (checked GASM_QEMU, PATH, and standard install locations)."
    IO.println "    Host-runtime QEMU validation did NOT run. The in-Lean formal trace check above passed, but external QEMU validation was skipped."
    return 2
  | some qemuPath =>
  try
    let child ← IO.Process.spawn {
      cmd := qemuPath
      args := #["-kernel", elfPath, "-serial", "stdio", "-display", "none", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04"]
      stdout := .piped
      stderr := .piped
    }
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait

    IO.println s!"[*] Captured QEMU Serial Output: {repr stdout}"
    IO.println s!"[*] QEMU Exit Code: {exitCode}"

    -- QEMU isa-debug-exit on port 0xF4 with value 0 exits with (0 << 1) | 1 = 1
    if exitCode == 1 && stdout == "Hello, World!\n" then
      IO.println "[+] PASS: Spike 1 Bare Metal ELF64 verified successfully via QEMU."
      return 0
    else
      IO.println s!"[!] FAIL: Unexpected QEMU execution result."
      IO.println s!"    Stdout: {repr stdout}"
      IO.println s!"    Stderr: {repr stderr}"
      IO.println s!"    Exit Code: {exitCode} (expected 1)"
      return 1
  catch e =>
    IO.println s!"[!] SKIP: Could not launch {qemuPath}: {e}"
    IO.println "    Host-runtime QEMU validation did NOT run. The in-Lean formal trace check above passed, but external QEMU validation was skipped."
    return 2

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

import Gasm.Execution.QEMUAArch64
import Spikes.CompilerBulk.AArch64Linux.Equivalence

open Gasm.Core.Platform
open Gasm.Execution
open Spikes.CompilerBulk.AArch64Linux

def main : IO UInt32 := do
  IO.println "[*] Checking the production semantic trace..."
  if Gasm.Targets.AArch64.runAArch64Trace (Event := Event) instructions executable.load ==
      [Gasm.Effects.Inject.inject (Gasm.Effects.ProcessEvent.exit 42)] then
    IO.println "[+] Production semantics returned exit(42)."
  else
    IO.eprintln "[!] Production semantic trace mismatch."
    return 1
  let output := "spike_compiler_bulk_aarch64_linux"
  IO.FS.writeBinFile output (← IO.ofExcept (emitVerifiedProgram verifiedProgram))
  match ← QEMUAArch64.runLinux output ByteArray.empty "" 42 with
  | .passed =>
      IO.println "[+] QEMU executed the verified compiler-generated program and returned 42."
      return 0
  | .mismatch exitCode stdout stderr =>
      IO.eprintln s!"[!] QEMU mismatch: exit={exitCode}, stdout={repr stdout}, stderr={repr stderr}"
      return 1
  | .runnerAbsent =>
      IO.println "[!] qemu-aarch64 is unavailable; formal execution and emission passed."
      return 2

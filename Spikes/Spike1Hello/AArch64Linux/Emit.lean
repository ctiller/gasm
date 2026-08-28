/-
Copyright 2026 Google LLC

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
import Spikes.Spike1Hello.AArch64Linux.Program
import Spikes.Spike1Hello.AArch64Linux.Equivalence

open Gasm.Core.Verification
open Spikes.Spike1Hello.AArch64Linux

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- CLI Emitter Target: Serializes and writes spike1_hello_aarch64_linux to disk strictly from the verified program contract. -/
def main : IO UInt32 := do
  let elfBytes := emitVerifiedAArch64LinuxExecutable spike1AArch64LinuxVerifiedProgram
  let outputPath := "spike1_hello_aarch64_linux"
  IO.println s!"[*] Emitting {elfBytes.size} bytes to {outputPath}..."
  IO.FS.writeBinFile outputPath elfBytes
  IO.println s!"[+] Generated AArch64 Linux ELF64 binary: {outputPath}"
  return 0

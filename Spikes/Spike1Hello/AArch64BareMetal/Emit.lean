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
import Spikes.Spike1Hello.AArch64BareMetal.Program
import Spikes.Spike1Hello.AArch64BareMetal.Equivalence

open Gasm.Core.Platform
open Spikes.Spike1Hello.AArch64BareMetal

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- CLI Emitter Target: Serializes and writes spike1_hello_aarch64_baremetal.elf to disk strictly from the verified program contract. -/
def main : IO UInt32 := do
  match emitVerifiedProgram spike1AArch64VerifiedBareMetalProgram with
  | .error message =>
    IO.eprintln s!"[!] Verified emission failed: {message}"
    return 1
  | .ok elfBytes =>
    let outputPath := "spike1_hello_aarch64_baremetal.elf"
    IO.println s!"[*] Emitting {elfBytes.size} bytes to {outputPath}..."
    IO.FS.writeBinFile outputPath elfBytes
    IO.println s!"[+] Generated AArch64 Bare Metal ELF64 binary: {outputPath}"
    return 0

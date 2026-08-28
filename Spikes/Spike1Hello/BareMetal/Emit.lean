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
import Gasm.Targets.BareMetal.Executable
import Spikes.Spike1Hello.BareMetal.Program
import Spikes.Spike1Hello.BareMetal.Equivalence

open Gasm.Targets.BareMetal
open Spikes.Spike1Hello.BareMetal

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- CLI Emitter Target: Serializes and writes spike1_hello_baremetal.elf to disk strictly from the verified program contract. -/
def main : IO UInt32 := do
  let elfBytes := emitVerifiedBareMetalExecutable spike1VerifiedBareMetalProgram
  let outputPath := "spike1_hello_baremetal.elf"
  IO.println s!"[*] Emitting {elfBytes.size} bytes to {outputPath}..."
  IO.FS.writeBinFile outputPath elfBytes
  IO.println s!"[+] Generated Bare Metal ELF64 binary: {outputPath}"
  return 0

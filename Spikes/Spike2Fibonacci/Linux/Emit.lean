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
import Spikes.Spike2Fibonacci.Linux.Program
import Spikes.Spike2Fibonacci.Linux.Equivalence

open Gasm.Core.Verification
open Spikes.Spike2Fibonacci.Linux

/- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
/-- CLI Emitter Target: Serializes and writes fib_linux to disk strictly from the verified program contract. -/
def main : IO UInt32 := do
  let exeBytes ← IO.ofExcept (emitVerifiedProgram spike2VerifiedProgram)
  let outputPath := "fib_linux"
  IO.println s!"[*] Emitting {exeBytes.size} bytes to {outputPath}..."
  IO.FS.writeBinFile outputPath exeBytes
  IO.println s!"[+] Generated ELF64 binary: {outputPath}"
  return 0

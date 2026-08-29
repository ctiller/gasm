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
import Spikes.Spike5Gzip.Equivalence

open Gasm.Core.Platform
open Gasm.Core.Verification
open Spikes.Spike5Gzip

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- CLI Emitter Target: Serializes and writes spike5_gunzip_linux to disk from the verified program contract. -/
def main : IO UInt32 := do
  let exeBytes ← IO.ofExcept (emitVerifiedProgram spike5GunzipLinuxVerifiedProgram)
  let outputPath := "spike5_gunzip_linux"
  IO.println s!"[*] Emitting {exeBytes.size} bytes to {outputPath}..."
  IO.FS.writeBinFile outputPath exeBytes
  IO.println s!"[+] Generated ELF64 binary: {outputPath}"
  return 0

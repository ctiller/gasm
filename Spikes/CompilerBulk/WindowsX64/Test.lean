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

import Spikes.CompilerBulk.WindowsX64.Equivalence

open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.X86_64
open Spikes.CompilerBulk.WindowsX64

def main : IO UInt32 := do
  IO.println "[*] Checking the production semantic outcome..."
  let outcome := runProgramOutcomeWithLoops (Event := Event) executable.load.rip instructions
    proofBudget.evaluatorFuel executable.load
  if outcome.observable !=
      .processExited 42 [Inject.inject (ProcessEvent.exit 42)] then
    IO.eprintln "[!] Production semantic outcome mismatch."
    return 1
  let output := ".\\spike_compiler_bulk_windows_x64.exe"
  IO.FS.writeBinFile output (← IO.ofExcept (emitVerifiedProgram verifiedProgram))
  IO.println "[+] Production semantics and VerifiedProgram emission passed."
  try
    let child ← IO.Process.spawn { cmd := output, stdout := .piped, stderr := .piped }
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    if exitCode == 42 then
      IO.println "[+] Native PE execution returned the compiler-proved exit code 42."
      return 0
    IO.eprintln s!"[!] Native PE mismatch: exit={exitCode}, stdout={repr stdout}, stderr={repr stderr}"
    return 1
  catch error =>
    IO.eprintln s!"[!] PE execution unavailable after formal execution and emission passed: {error}"
    return 2

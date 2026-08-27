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

namespace Spikes.Common.WasmHostRunner

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- Builds the inline Node.js script that instantiates and runs a WASI preview1 Wasm binary
    via the host `node` CLI runner. Shared verbatim by every spike's Wasm host-runtime check
    (previously copy-pasted byte-for-byte across Spike1/Spike2/Spike3's `Wasm/Test.lean`
    files — a Law 12 unlinked-twin violation). `pipeStdin` wires the host process's stdin
    (fd 0) into the WASI instance, for spikes (e.g. Spike 3) that read from stdin. -/
def nodeWasiScript (wasmPath : String) (pipeStdin : Bool := false) : String :=
  let wasiOpts := if pipeStdin then "{ version: 'preview1', stdin: 0 }" else "{ version: 'preview1' }"
  s!"const fs = require('fs'); const \{ WASI } = require('wasi'); const wasi = new WASI({wasiOpts}); const wasm = fs.readFileSync('{wasmPath}'); WebAssembly.instantiate(wasm, \{ wasi_snapshot_preview1: wasi.wasiImport }).then(r => wasi.start(r.instance));"

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- Candidate host Wasm CLI runners to probe, in preference order, each paired with the argv
    that invokes it against `wasmPath`. `node` is driven via an inline `-e` script built by
    `nodeWasiScript`; the others accept the `.wasm` file directly. -/
def candidateRunners (wasmPath : String) : List (String × Array String) :=
  [ ("node", #["-e", nodeWasiScript wasmPath])
  , ("wasmtime", #["run", wasmPath])
  , ("wasmer", #["run", wasmPath])
  , ("deno", #["run", "--allow-read", wasmPath])
  ]

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- Outcome of attempting host-runtime validation of an emitted Wasm binary. Per Law 13(4)
    ("an oracle that cannot run must fail the run; it must never no-op, skip, or synthesize
    results"), the absence of every candidate runner is its OWN distinct outcome
    (`runnerAbsent`) — it is NEVER folded into `.passed`. Callers MUST map `.runnerAbsent` to
    a non-zero exit and an honest "host-runtime validation did not run" message, never to a
    success message. -/
inductive HostRunOutcome
  | passed (cmd : String)
  | mismatch (cmd : String) (exitCode : UInt32) (stdout stderr : String)
  | runnerAbsent
  deriving Inhabited

/- REF: docs/SPIKES.md#4-continuous-spike-testing-verification-protocol -/
/-- Tries each candidate host Wasm runner in turn, stopping at the first one actually found
    and invokable on PATH (regardless of whether its output verifies) — never continuing past
    a found runner to fabricate a different outcome. `checkOutput` judges pass/fail from the
    captured exit code and stdout. Returns `HostRunOutcome.runnerAbsent` — never a synthesized
    pass — when NO candidate runner could be spawned at all. -/
def tryHostRunners (wasmPath : String) (checkOutput : UInt32 → String → Bool) : IO HostRunOutcome := do
  let runners := candidateRunners wasmPath
  let mut result : HostRunOutcome := .runnerAbsent
  for (cmd, args) in runners do
    let attempt ← try
      let child ← IO.Process.spawn {
        cmd := cmd
        args := args
        stdout := .piped
        stderr := .piped
      }
      let stdout ← child.stdout.readToEnd
      let stderr ← child.stderr.readToEnd
      let exitCode ← child.wait
      pure (some (exitCode, stdout, stderr))
    catch _ =>
      pure none
    match attempt with
    | some (exitCode, stdout, stderr) =>
      result := if checkOutput exitCode stdout then .passed cmd else .mismatch cmd exitCode stdout stderr
      break
    | none => pure ()
  pure result

end Spikes.Common.WasmHostRunner

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

namespace Gasm.Targets.BareMetal

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Resolves the path to the `qemu-system-x86_64` executable used to hardware-validate
    bare-metal x86-64 spikes. Resolution order mirrors `Gasm.Targets.X86_64.findNasmPath`'s
    NASM resolution exactly, substituting QEMU's own env var and install locations: (1) an
    explicit `overridePath` argument; (2) the `GASM_QEMU` environment variable, which callers
    should set to the full path of their `qemu-system-x86_64(.exe)` when it is not
    discoverable by the remaining generic candidates (e.g.
    `GASM_QEMU` environment variable, which callers should set to the full path of their
    `qemu-system-x86_64(.exe)` when it is not discoverable by the remaining generic candidates;
    (3) `qemu-system-x86_64` / `qemu-system-x86_64.exe` on PATH; (4) the standard machine-wide
    Windows install locations (`Program Files`, `Program Files (x86)`); (5) the standard Linux
    package-manager install location (`/usr/bin/qemu-system-x86_64`).
    Returns `none` (never throws) if none of these resolve to a working QEMU binary, so callers
    can honor the honest-runner convention rather than have an exception synthesize a false failure. -/
def findQemuPath (overridePath : Option String := none) : IO (Option String) := do
  if let some p := overridePath then
    return some p
  if let some envPath ← IO.getEnv "GASM_QEMU" then
    return some envPath
  let mut candidates := #[
    "qemu-system-x86_64",
    "qemu-system-x86_64.exe",
    "/usr/bin/qemu-system-x86_64",
    "/usr/local/bin/qemu-system-x86_64"
  ]
  if let some pf ← IO.getEnv "ProgramFiles" then
    candidates := candidates.push s!"{pf}\\qemu\\qemu-system-x86_64.exe"
  if let some pfx86 ← IO.getEnv "ProgramFiles(x86)" then
    candidates := candidates.push s!"{pfx86}\\qemu\\qemu-system-x86_64.exe"
  for p in candidates do
    let isAvail ← try
      let proc ← IO.Process.spawn {
        cmd := p
        args := #["--version"]
        stdout := .piped
        stderr := .piped
      }
      let code ← proc.wait
      pure (code == 0)
    catch _ =>
      pure false
    if isAvail then
      return some p
  return none

end Gasm.Targets.BareMetal

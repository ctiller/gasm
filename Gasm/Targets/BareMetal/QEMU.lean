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
    `GASM_QEMU=C:\Program Files\qemu\qemu-system-x86_64.exe` -- the default winget/upstream
    Windows install location, not on PATH by default); (3) `qemu-system-x86_64` /
    `qemu-system-x86_64.exe` on PATH; (4) the standard machine-wide Windows install locations
    (`Program Files`, `Program Files (x86)`); (5) the standard Linux package-manager install
    location (`/usr/bin/qemu-system-x86_64`, where `apt-get install qemu-system-x86` puts it).
    Returns `none` (never throws) if none of these resolve to a working QEMU binary, so callers
    can honor the honest-runner convention (`docs/SPIKES.md` §4 item 5: exit `2` = oracle
    absent, hardware validation did not run) rather than have an exception synthesize a false
    failure that looks identical to a genuine verification mismatch. -/
def findQemuPath (overridePath : Option String := none) : IO (Option String) := do
  if let some p := overridePath then
    return some p
  if let some envPath ← IO.getEnv "GASM_QEMU" then
    return some envPath
  let standardPaths := [
    "qemu-system-x86_64",
    "qemu-system-x86_64.exe",
    "C:\\Program Files\\qemu\\qemu-system-x86_64.exe",
    "C:\\Program Files (x86)\\qemu\\qemu-system-x86_64.exe",
    "/usr/bin/qemu-system-x86_64"
  ]
  for p in standardPaths do
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

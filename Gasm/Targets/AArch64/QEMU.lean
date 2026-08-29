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

namespace Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Resolves the path to the `qemu-system-aarch64` executable used to validate bare-metal AArch64.
    Checks (1) explicit override, (2) `GASM_QEMU_AARCH64` env var, (3) `qemu-system-aarch64` on PATH,
    (4) standard Windows / Linux package-manager install locations. -/
def findQemuSystemPath (overridePath : Option String := none) : IO (Option String) := do
  if let some p := overridePath then
    return some p
  if let some envPath ← IO.getEnv "GASM_QEMU_AARCH64" then
    return some envPath
  let standardPaths := [
    "qemu-system-aarch64",
    "qemu-system-aarch64.exe",
    "C:\\Program Files\\qemu\\qemu-system-aarch64.exe",
    "/usr/bin/qemu-system-aarch64"
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

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Resolves the path to the `qemu-aarch64` user-mode emulator executable used to validate Linux AArch64.
    Checks (1) explicit override, (2) `GASM_QEMU_USER_AARCH64` env var, (3) `qemu-aarch64` on PATH,
    (4) standard package-manager install locations. -/
def findQemuUserPath (overridePath : Option String := none) : IO (Option String) := do
  if let some p := overridePath then
    return some p
  if let some envPath ← IO.getEnv "GASM_QEMU_USER_AARCH64" then
    return some envPath
  let standardPaths := [
    "qemu-aarch64",
    "qemu-aarch64.exe",
    "/usr/bin/qemu-aarch64"
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

end Gasm.Targets.AArch64

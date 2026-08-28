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
import Gasm.Targets.AArch64.QEMU

namespace Gasm.Execution.QEMUAArch64

open Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
inductive QemuRunOutcome where
  | passed
  | mismatch (exitCode : UInt32) (stdout stderr : String)
  | runnerAbsent
  deriving Inhabited, Repr, BEq

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Runs the given AArch64 flat ELF executable under qemu-system-aarch64 using semihosting and PL011. -/
def runBareMetal (elfPath : String) (expectedStdout : String) (expectedExitCode : UInt32 := 0) : IO QemuRunOutcome := do
  match ← findQemuSystemPath with
  | none => return .runnerAbsent
  | some qemuPath =>
    try
      let child ← IO.Process.spawn {
        cmd := qemuPath
        args := #["-M", "virt", "-cpu", "cortex-a53", "-display", "none", "-semihosting", "-kernel", elfPath, "-serial", "stdio"]
        stdout := .piped
        stderr := .piped
      }
      let stdout ← child.stdout.readToEnd
      let stderr ← child.stderr.readToEnd
      let exitCode ← child.wait
      if exitCode == expectedExitCode && stdout == expectedStdout then
        return .passed
      else
        return .mismatch exitCode stdout stderr
    catch _ =>
      return .runnerAbsent

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- Runs the given static AArch64 Linux ELF executable under qemu-aarch64 user-mode emulator. -/
def runLinux (elfPath : String) (stdin : ByteArray) (expectedStdout : String) (expectedExitCode : UInt32 := 0) : IO QemuRunOutcome := do
  match ← findQemuUserPath with
  | none => return .runnerAbsent
  | some qemuPath =>
    try
      let child ← IO.Process.spawn {
        cmd := qemuPath
        args := #[elfPath]
        stdin := .piped
        stdout := .piped
        stderr := .piped
      }
      child.stdin.write stdin
      child.stdin.flush
      let stdout ← child.stdout.readToEnd
      let stderr ← child.stderr.readToEnd
      let exitCode ← child.wait
      if exitCode == expectedExitCode && stdout == expectedStdout then
        return .passed
      else
        return .mismatch exitCode stdout stderr
    catch _ =>
      return .runnerAbsent

end Gasm.Execution.QEMUAArch64

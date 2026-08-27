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
import Gasm.Core.Types
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64

open Gasm.Targets.X86_64.Instructions

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Standard NASM platform compilation envelope for 64-bit flat binary output. -/
def toNasmAssembly (instrs : List AnyX86_64Instruction) (org : Nat := 0) : String :=
  let header := s!"[BITS 64]\ndefault rel\norg 0x{String.ofList (Nat.toDigits 16 org)}\n\n"
  let body := String.intercalate "\n" (instrs.map (fun i => s!"    {X86_64Instruction.toNASM i}"))
  header ++ body ++ "\n"

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Resolves the path to the NASM assembler executable on the host system. Resolution order:
    (1) an explicit `overridePath` argument; (2) the `GASM_NASM` environment variable, which
    callers should set to the full path of their `nasm(.exe)` when it is not discoverable by
    the remaining generic candidates (e.g. `GASM_NASM=C:\tools\nasm\nasm.exe`); (3) `nasm` /
    `nasm.exe` on PATH; (4) `%LOCALAPPDATA%\bin\NASM\nasm.exe`, a common per-user install
    location; (5) the standard machine-wide Program Files install locations. Throws if none of
    these resolve to a working NASM binary, rather than silently returning an unusable path. -/
def findNasmPath (overridePath : Option String := none) : IO String := do
  if let some p := overridePath then
    return p
  if let some envPath ← IO.getEnv "GASM_NASM" then
    return envPath
  let mut standardPaths := [
    "nasm",
    "nasm.exe"
  ]
  if let some localAppData ← IO.getEnv "LOCALAPPDATA" then
    standardPaths := standardPaths ++ [s!"{localAppData}\\bin\\NASM\\nasm.exe"]
  standardPaths := standardPaths ++ [
    "C:\\Program Files\\NASM\\nasm.exe",
    "C:\\Program Files (x86)\\NASM\\nasm.exe"
  ]
  for p in standardPaths do
    let isAvail ← try
      let proc ← IO.Process.spawn {
        cmd := p
        args := #["-v"]
        stdout := .piped
        stderr := .piped
      }
      let code ← proc.wait
      pure (code == 0)
    catch _ =>
      pure false
    if isAvail then
      return p
  throw (IO.userError "NASM not found on PATH or any standard install location; install NASM or set the GASM_NASM environment variable to its full path")

/- REF: intel-sdm#vol=2;sec=2.1;part=21-instruction-format-for-protected-mode-real-address-mode-and-virtual-8086-mode -/
/-- Invokes NASM to assemble an assembly text string into a flat raw binary byte array. -/
def assembleWithNasm (nasmPath : String) (asmCode : String) (tmpPrefix : String := ".tmp_gasm_nasm") : IO (Except String ByteArray) := do
  let asmFile := s!"{tmpPrefix}.asm"
  let binFile := s!"{tmpPrefix}.bin"
  IO.FS.writeFile asmFile asmCode
  let proc ← IO.Process.spawn {
    cmd := nasmPath
    args := #["-f", "bin", "-o", binFile, asmFile]
    stdout := .piped
    stderr := .piped
  }
  let exitCode ← proc.wait
  if exitCode != 0 then
    let stderr ← proc.stderr.readToEnd
    let _ ← try IO.FS.removeFile asmFile catch _ => pure ()
    let _ ← try IO.FS.removeFile binFile catch _ => pure ()
    return .error s!"NASM exited with code {exitCode}:\n{stderr}"
  let bytes ← IO.FS.readBinFile binFile
  let _ ← try IO.FS.removeFile asmFile catch _ => pure ()
  let _ ← try IO.FS.removeFile binFile catch _ => pure ()
  return .ok bytes

end Gasm.Targets.X86_64

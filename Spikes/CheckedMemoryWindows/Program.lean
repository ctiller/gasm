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

import Gasm.Targets.X86_64.StackStorePrefixExecution
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.Windows.Linker

/-!
The exact production program used by the checked-memory Windows demonstration. It contains one
selected checked-family access: the byte store following the explicit 40-byte frame allocation.
The later imported `ExitProcess` call has its ordinary implicit stack write and IAT read; those
effects are deliberately unselected in this first M1 profile and are not presented as checked.
-/

namespace Spikes.CheckedMemoryWindows

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.StackStorePrefix
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def storedValue : UInt8 := 0xA5

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- One checked byte store followed by a real typed Windows process termination. -/
def symbolicProgram : List SymbolicInstr := [
  instr (sub_rsp frameSize),
  instr (mov_rsp_byte byteOffset storedValue),
  instr (xor_r32 .ecx .ecx),
  call_import "ExitProcess"
]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def linked : LinkedWindowsProgram :=
  linkWindowsProgram symbolicProgram []

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def instructions : List X86_64Instr := linked.instructions

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def executable : WindowsExecutable := linked.executable

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Exact loader core state selected by the checked-memory profile. -/
def entryState : X86_64MachineState := executable.load

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The linked artifact begins with the exact prefix certified by `StackStorePrefixExecution`. -/
theorem instructions_shape :
    instructions =
      [sub_rsp frameSize, mov_rsp_byte byteOffset storedValue,
        xor_r32 .ecx .ecx, call_rip 8199] := by
  rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem artifact_connected :
    executable.textBytes = serializeInstructions instructions := by
  rfl

end Spikes.CheckedMemoryWindows

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

import Gasm.Targets.X86_64.HardwareMemoryControls
import Gasm.Targets.X86_64.HardwareMemoryDifferential
import Gasm.Targets.X86_64.HardwareMemoryDifferentialControls

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.HardwareMemoryPlan
open Gasm.Targets.X86_64.HardwareMemoryHarness
open Gasm.Targets.X86_64.HardwareMemoryDifferential

private def seededState : X86_64MachineState :=
  let state := (default : X86_64MachineState).setGpr64 .rbx 0x0123456789abcdef
  let state := state.setGpr64 .rcx 0xfedcba9876543210
  let state := state.setGpr64 .r10 0x8877665544332211
  let state := state.setGpr64 .r13 0xffffffffffffffff
  { state with flags := 0x8d5 }

private def controls : List Request := [
  -- Reads the asymmetric/nonzero native preimage into RBX.
  { caseId := 0x101, form := .reg64Mem64Disp ⟨.rbx, .rax, 0⟩, seed := seededState },
  -- Destination/base alias: address must come from pre-state RAX before RAX is overwritten.
  { caseId := 0x102, form := .reg64Mem64Disp ⟨.rax, .rax, 0x80⟩, seed := seededState },
  -- Store with independent source; full-region comparison checks both canaries and neighbors.
  { caseId := 0x103, form := .mem64DispReg64 ⟨.r10, 0x7f, .rbx⟩, seed := seededState },
  -- Immediate store covers a production encoding whose data is not sourced from a GPR.
  { caseId := 0x104, form := .mem64DispImm32 ⟨.r11, 0, 0x87654321⟩, seed := seededState },
  -- Byte store proves the validator does not silently widen the declared footprint.
  { caseId := 0x105, form := .mem8Reg8 ⟨.r12, .rcx⟩, seed := seededState },
  -- Byte load into an all-ones destination proves the production step zero-extends rather than
  -- preserving stale high bits; the nonzero displacement also exercises its distinct codec path.
  { caseId := 0x106, form := .movzxR64Mem8 ⟨.r13, .r15, 0x7f⟩, seed := seededState }
]

private def coverageComplete : Bool :=
  ScratchClass.all.all fun cls => controls.any fun request => request.form.scratchClass == cls

private def negativeCalibration (observations : List Observation) : Except String Unit := do
  let baseline ← match observations with
    | [] => throw "runtime negative calibration received no native observation"
    | observation :: _ => pure observation
  HardwareMemoryDifferential.calibrateLeadingGuardRejection baseline
  HardwareMemoryDifferential.calibratePayloadNeighborRejection baseline
  HardwareMemoryDifferential.calibrateTrailingGuardRejection baseline
  let movzx ← match observations.find? fun observation =>
      observation.plan.form.scratchClass == .movzxR64Mem8 with
    | some observation => pure observation
    | none => throw "runtime negative calibration received no MOVZX native observation"
  HardwareMemoryDifferential.calibrateMovzxStaleHighBitsRejection movzx

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Adding an admitted class without a nonempty native control turns this module red.
#guard coverageComplete

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Executes all five supplemental MOV/MOVZX memory-form classes through the native guarded scratch
    runner and compares them with their exact production `step` semantics. -/
def main (_args : List String) : IO UInt32 := do
  let result ← run controls
  match result with
  | .error msg =>
      IO.eprintln s!"x86 scratch-memory harness failed: {msg}"
      pure 1
  | .ok observations =>
      match negativeCalibration observations with
      | .error msg =>
          IO.eprintln s!"x86 scratch-memory negative calibration failed: {msg}"
          pure 1
      | .ok () =>
          match compareBatch observations with
          | .error msg =>
              IO.eprintln s!"x86 scratch-memory differential mismatch: {msg}"
              pure 1
          | .ok () =>
              IO.println s!"x86 scratch-memory hardware controls passed ({observations.length} exact guarded observations; all four negative calibrations rejected)"
              pure 0

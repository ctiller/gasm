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

import Gasm.Targets.X86_64.HardwareMemoryHarness

namespace Gasm.Targets.X86_64.HardwareMemoryDifferential

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.HardwareMemoryPlan
open Gasm.Targets.X86_64.HardwareMemoryHarness

private def comparableRegs : List Reg64 :=
  [.rax, .rcx, .rdx, .rbx, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

private def firstByteMismatch (expected actual : ByteArray) : Option Nat :=
  (List.range (min expected.size actual.size)).find? fun i => expected.get! i != actual.get! i

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Compares one case against the exact production step used to construct its plan.  RSP is the
    sole excluded register because the Windows harness owns its stack; the planner rejects every
    admitted form that reads or writes RSP.  All other GPRs, defined arithmetic flags, model fault
    status, and every byte of both canaries plus payload are checked. -/
def compare (observation : Observation) : Except String Unit := do
  let plan := observation.plan
  let native := observation.result.machine
  let decoded ← plan.decodeAndStep
  let model := decoded.state
  if model.faulted then
    throw s!"case {plan.caseId}: production model faulted for an admitted mapped scratch plan"
  if native.faulted then
    throw s!"case {plan.caseId}: native instruction faulted for an admitted mapped scratch plan"
  for reg in comparableRegs do
    if model.gprs reg != native.gprs reg then
      throw s!"case {plan.caseId}: register {reg} mismatch (model={formatHex64 (model.gprs reg)}, native={formatHex64 (native.gprs reg)})"
  let undefined := decoded.undefinedFlagsMask
  let mask := arithmeticStatusMask &&& (~~~undefined)
  if (model.flags &&& mask) != (native.flags &&& mask) then
    throw s!"case {plan.caseId}: defined arithmetic flags mismatch"
  let expectedRegion ← plan.modelRegionAfter
  let actualRegion := observation.result.regionAfter
  if actualRegion.size != regionBytes then
    throw s!"case {plan.caseId}: guarded postimage length mismatch"
  if expectedRegion != actualRegion then
    match firstByteMismatch expectedRegion actualRegion with
    | some index =>
        throw s!"case {plan.caseId}: guarded postimage byte {index} mismatch (model={expectedRegion.get! index}, native={actualRegion.get! index})"
    | none => throw s!"case {plan.caseId}: guarded postimage mismatch"

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Runs the exact comparator over a nonempty batch.  An enabled batch producing no observations
    is a hard coverage failure rather than a vacuous pass. -/
def compareBatch (observations : List Observation) : Except String Unit := do
  if observations.isEmpty then throw "scratch-memory differential batch produced zero observations"
  for observation in observations do
    compare observation

end Gasm.Targets.X86_64.HardwareMemoryDifferential

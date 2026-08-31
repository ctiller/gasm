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

import Gasm.Targets.X86_64.HardwareMemoryDifferential

namespace Gasm.Targets.X86_64.HardwareMemoryDifferentialControls

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.HardwareMemoryPlan

private def baselinePlan : Except String Plan :=
  let seed := (default : X86_64MachineState).setGpr64 .rbx 0x0123456789abcdef
  prepare 0x221 (.mem64DispReg64 ⟨.rax, 0, .rbx⟩) seed 0x140004000

private def baselineValid : Bool :=
  match baselinePlan with
  | .ok plan => plan.decodeAndStep |>.isOk
  | .error _ => false

private def planMutationRejected (mutate : Plan → Plan) : Bool :=
  match baselinePlan with
  | .error _ => false
  | .ok plan =>
      match (mutate plan).decodeAndStep with
      | .error _ => true
      | .ok _ => false

private def trailingInstructionByteRejected : Bool :=
  planMutationRejected fun plan =>
    { plan with instructionBytes := plan.instructionBytes.push 0x90 }

private def mutatedAccessAddressRejected : Bool :=
  planMutationRejected fun plan => { plan with accessAddress := plan.accessAddress + 1 }

private def mutatedAccessKindRejected : Bool :=
  planMutationRejected fun plan => { plan with accessKind := .load }

private def mutatedAccessWidthRejected : Bool :=
  planMutationRejected fun plan => { plan with accessWidth := .w8 }

private def mutatedAccessPrestateRejected : Bool :=
  planMutationRejected fun plan =>
    let base := plan.form.baseReg
    { plan with initialState := plan.initialState.setGpr64 base (plan.initialState.gprs base + 1) }

private def mutatedClosedFormRejected : Bool :=
  planMutationRejected fun plan =>
    { plan with form := .mem64DispReg64 ⟨.rax, 0, .rcx⟩ }

private def mutatedOutOfPayloadRejected : Bool :=
  planMutationRejected fun plan =>
    let base := plan.form.baseReg
    let address := plan.payloadBase + payloadBytes.toUInt64
    { plan with
      accessAddress := address
      initialState := plan.initialState.setGpr64 base address }

private def mutatedRegionLayoutRejected : Bool :=
  planMutationRejected fun plan => { plan with regionBase := plan.regionBase + 1 }

private def coherentRspFormRejected : Bool :=
  planMutationRejected fun plan =>
    let form : ScratchMov := .mem64DispReg64 ⟨.rsp, 0, .rbx⟩
    { plan with
      form := form
      instructionBytes := X86_64Instruction.encode form.pack
      initialState := plan.initialState.setGpr64 .rsp plan.accessAddress }

private def mutatedExactPreimageRejected : Bool :=
  planMutationRejected fun plan =>
    let old := X86_64Mem.readByte plan.initialState.memory plan.accessAddress
    let memory := X86_64Mem.writeByte plan.initialState.memory plan.accessAddress (old ^^^ 0xff)
    { plan with initialState := { plan.initialState with memory := memory } }

private def coherentPreimageCopiesRejected : Bool :=
  planMutationRejected fun plan =>
    let index := (plan.accessAddress - plan.regionBase).toNat
    let changed := plan.regionBefore.get! index ^^^ 0xff
    let memory := X86_64Mem.writeByte plan.initialState.memory plan.accessAddress changed
    { plan with
      regionBefore := plan.regionBefore.set! index changed
      initialState := { plan.initialState with memory := memory } }

private def publicPlanRetagRejected : Bool :=
  planMutationRejected fun plan => { plan with caseId := plan.caseId + 0x100 }

private def coherentMovzxRelabelHasDistinctIdentity : Bool :=
  let seed := (default : X86_64MachineState).setGpr64 .r13 0xffffffffffffffff
  match prepare 0x222 (.movzxR64Mem8 ⟨.r13, .r15, 0x7f⟩) seed 0x140004000 with
  | .error _ => false
  | .ok original =>
      let relabeledSeed := original.initialState.setGpr64 .r13 (original.accessAddress - 0x7f)
      match prepare original.caseId (.movzxR64Mem8 ⟨.r13, .r13, 0x7f⟩)
          relabeledSeed original.regionBase with
      | .error _ => false
      | .ok relabeled => original.planIdentity != relabeled.planIdentity

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- The owner-derived baseline plan remains inhabited and validates.
#guard baselineValid

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Every caller-visible component used by native execution is covered by the exact identity.
#guard trailingInstructionByteRejected
#guard mutatedAccessAddressRejected
#guard mutatedAccessKindRejected
#guard mutatedAccessWidthRejected
#guard mutatedAccessPrestateRejected
#guard mutatedClosedFormRejected
#guard mutatedOutOfPayloadRejected
#guard mutatedRegionLayoutRejected
#guard coherentRspFormRejected
#guard mutatedExactPreimageRejected
#guard coherentPreimageCopiesRejected
#guard publicPlanRetagRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- The adversarial destination/base-alias MOVZX relabel is observationally equivalent after the
-- load, but its exact form/bytes/pre-state identity is necessarily different.  Native
-- observations are harness-constructed, so the relabeled plan cannot be paired with the old
-- native identity through the public API.
#guard coherentMovzxRelabelHasDistinctIdentity

end Gasm.Targets.X86_64.HardwareMemoryDifferentialControls

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
open Gasm.Targets.X86_64.HardwareHarness
open Gasm.Targets.X86_64.HardwareMemoryPlan
open Gasm.Targets.X86_64.HardwareMemoryProtocol
open Gasm.Targets.X86_64.HardwareMemoryHarness
open Gasm.Targets.X86_64.HardwareMemoryDifferential

private def matchingObservation : Except String Observation := do
  let seed := (default : X86_64MachineState).setGpr64 .rbx 0x0123456789abcdef
  let plan ← prepare 0x221 (.mem64DispReg64 ⟨.rax, 0, .rbx⟩) seed 0x140004000
  let decoded ← plan.decodeAndStep
  let regionAfter ← plan.modelRegionAfter
  pure {
    plan := plan
    result := {
      caseId := plan.caseId
      machine := { gprs := decoded.state.gprs, flags := decoded.state.flags, faulted := false }
      regionAfter := regionAfter
    }
  }

private def baselineAccepted : Bool :=
  match matchingObservation with
  | .ok observation => (compare observation).isOk
  | .error _ => false

private def comparisonRejected (result : Except String Unit) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def corruptionRejected (index : Nat) : Bool :=
  match matchingObservation with
  | .error _ => false
  | .ok observation =>
      let old := observation.result.regionAfter.get! index
      let corrupted := observation.result.regionAfter.set! index (old ^^^ 0xff)
      let observation := { observation with result := { observation.result with regionAfter := corrupted } }
      comparisonRejected (compare observation)

private def trailingInstructionByteRejected : Bool :=
  match matchingObservation with
  | .error _ => false
  | .ok observation =>
      let plan := { observation.plan with instructionBytes := observation.plan.instructionBytes.push 0x90 }
      comparisonRejected (compare { observation with plan := plan })

private def planMutationRejected (mutate : Plan → Plan) : Bool :=
  match matchingObservation with
  | .error _ => false
  | .ok observation =>
      comparisonRejected (compare { observation with plan := mutate observation.plan })

private def mutatedAccessAddressRejected : Bool :=
  planMutationRejected fun plan => { plan with accessAddress := plan.accessAddress + 1 }

private def mutatedAccessKindRejected : Bool :=
  planMutationRejected fun plan => { plan with accessKind := .load }

private def mutatedAccessWidthRejected : Bool :=
  planMutationRejected fun plan => { plan with accessWidth := .w8 }

private def mutatedAccessPrestateRejected : Bool :=
  planMutationRejected fun plan =>
    let base := plan.form.baseReg
    let initialState := plan.initialState.setGpr64 base (plan.initialState.gprs base + 1)
    { plan with initialState := initialState }

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
    let initialState := plan.initialState.setGpr64 .rsp plan.accessAddress
    { plan with
      form := form
      instructionBytes := X86_64Instruction.encode form.pack
      initialState := initialState }

private def mutatedExactPreimageRejected : Bool :=
  planMutationRejected fun plan =>
    let old := X86_64Mem.readByte plan.initialState.memory plan.accessAddress
    let memory := X86_64Mem.writeByte plan.initialState.memory plan.accessAddress (old ^^^ 0xff)
    let initialState := { plan.initialState with memory := memory }
    { plan with initialState := initialState }

private def coherentPreimageCopiesRejected : Bool :=
  planMutationRejected fun plan =>
    let index := (plan.accessAddress - plan.regionBase).toNat
    let old := plan.regionBefore.get! index
    let changed := old ^^^ 0xff
    let regionBefore := plan.regionBefore.set! index changed
    let memory := X86_64Mem.writeByte plan.initialState.memory plan.accessAddress changed
    let initialState := { plan.initialState with memory := memory }
    { plan with regionBefore := regionBefore, initialState := initialState }

private def publicPlanRetagRejected : Bool :=
  match matchingObservation with
  | .error _ => false
  | .ok observation =>
      let plan := { observation.plan with caseId := observation.plan.caseId + 0x100 }
      comparisonRejected (compare { observation with plan := plan })

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- An exact model-shaped observation is accepted.
#guard baselineAccepted

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Leading-canary corruption is observed and rejected.
#guard corruptionRejected 0

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Corruption inside the payload but outside this store's declared bytes is also rejected.
#guard corruptionRejected guardBytes

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Trailing-canary corruption is independently observed and rejected.
#guard corruptionRejected (guardBytes + payloadBytes)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Native/model instruction identity is exact; an ignored trailing byte cannot pass.
#guard trailingInstructionByteRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Stored address identity is rechecked from the decoded descriptor and exact pre-state.
#guard mutatedAccessAddressRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Stored access kind cannot drift from the production descriptor.
#guard mutatedAccessKindRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Stored access width cannot drift from the production descriptor.
#guard mutatedAccessWidthRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Descriptor evaluation is pinned to the exact stored pre-state, not a reconstructed address.
#guard mutatedAccessPrestateRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- The stored closed constructor cannot drift from the exact decoded production bytes.
#guard mutatedClosedFormRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Even a self-consistent descriptor/pre-state mutation cannot move the access outside payload.
#guard mutatedOutOfPayloadRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Region and payload coordinates remain one exact guarded layout.
#guard mutatedRegionLayoutRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Coherent form/bytes/prestate mutation cannot bypass the native harness's RSP ownership.
#guard coherentRspFormRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Initial memory must equal the exact stored guarded preimage, even at an overwritten store byte.
#guard mutatedExactPreimageRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Mutating both stored preimage copies cannot relabel the independently generated case pattern.
#guard coherentPreimageCopiesRejected

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
-- Public comparison binds native result identity to the plan; a high-byte retag cannot pass.
#guard publicPlanRetagRejected

end Gasm.Targets.X86_64.HardwareMemoryDifferentialControls

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
-- Native/model instruction identity is exact; an ignored trailing byte cannot pass.
#guard trailingInstructionByteRejected

end Gasm.Targets.X86_64.HardwareMemoryDifferentialControls

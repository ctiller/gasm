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
import Gasm.Core.Verification
import Gasm.Effects.Inject
import Gasm.Effects.Trace
import Gasm.Targets.AArch64.Instructions.Base
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Executable
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.AArch64BareMetal.Program

namespace Spikes.Spike1Hello.AArch64BareMetal

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.BareMetal

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered bare-metal AArch64 execution. -/
theorem spike1_aarch64_baremetal_canonical_effect_trace_equivalence :
    (runBareMetalTrace spike1AArch64BareMetalInstructions spike1AArch64BareMetalExecutable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  set_option maxRecDepth 4000 in
  decide

def spike1AArch64BareMetalArtifact : BareMetalArtifact where
  executable := spike1AArch64BareMetalExecutable
  instructions := spike1AArch64BareMetalInstructions
  artifactConnected := rfl

def spike1AArch64BareMetalCapabilities : CapabilityComposition (BareMetalAArch64 AnyEvent) where
  root :=
    { Context := Unit
      providers := []
      establishes := fun artifact _ _ _ => artifact = spike1AArch64BareMetalArtifact }
  realize := fun _ _ => ()
  realizeSupports := by
    intro _ _ provider membership
    exact nomatch provider

theorem spike1_aarch64_baremetal_outcome :
    runBareMetalOutcome spike1AArch64BareMetalInstructions spike1AArch64BareMetalExecutable.load =
      .semihostingExited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) := by
  set_option maxRecDepth 4000 in
    decide

def spike1AArch64BareMetalArtifactCertificate : ProgramArtifactCertificate (BareMetalAArch64 AnyEvent) where
  artifact := spike1AArch64BareMetalArtifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := spike1AArch64BareMetalArtifact.artifactConnected

def spike1AArch64BareMetalProviderCertificate :
    ProgramProviderCertificate (BareMetalAArch64 AnyEvent)
      spike1AArch64BareMetalCapabilities spike1AArch64BareMetalArtifact where
  importsCovered := by
    intro imported h
    exact nomatch imported
  providersLinked := by
    intro provider h
    exact nomatch provider

def spike1AArch64BareMetalEntryCertificate :
    ProgramEntryCertificate (BareMetalAArch64 AnyEvent)
      spike1AArch64BareMetalCapabilities spike1AArch64BareMetalArtifact where
  entryContext := fun _ => ()
  entryEstablished := by
    intro environment
    rfl

def spike1AArch64BareMetalAdmissibilityCertificate :
    ProgramAdmissibilityCertificate (BareMetalAArch64 AnyEvent)
      spike1AArch64BareMetalCapabilities spike1AArch64BareMetalArtifact
      spike1AArch64BareMetalEntryCertificate where
  platformAdmissible := by
    intro environment
    change (runBareMetalOutcome spike1AArch64BareMetalInstructions
      spike1AArch64BareMetalExecutable.load).isAdmissible
    rw [spike1_aarch64_baremetal_outcome]
    trivial

def spike1AArch64BareMetalBehaviorCertificate :
    ProgramBehaviorCertificate (BareMetalAArch64 AnyEvent)
      spike1AArch64BareMetalCapabilities spike1AArch64BareMetalArtifact
      spike1AArch64BareMetalEntryCertificate where
  spec := fun _ => .semihostingExited 0
    (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit))
  traceEquivalence := by
    intro environment
    exact spike1_aarch64_baremetal_outcome

/-- Sole universal verified authority for the AArch64 bare-metal image. -/
def spike1AArch64VerifiedBareMetalProgram :
    VerifiedProgram (BareMetalAArch64 AnyEvent) spike1AArch64BareMetalCapabilities :=
  VerifiedProgram.compose "Spike 1: Bare Metal AArch64 Hello World"
    spike1AArch64BareMetalArtifactCertificate
    spike1AArch64BareMetalProviderCertificate spike1AArch64BareMetalEntryCertificate
    spike1AArch64BareMetalAdmissibilityCertificate
    spike1AArch64BareMetalBehaviorCertificate

end Spikes.Spike1Hello.AArch64BareMetal

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
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Executable
import Spikes.Spike1Hello.Spec
import Spikes.Spike1Hello.BareMetal.Program

namespace Spikes.Spike1Hello.BareMetal

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.BareMetal

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive proof of semantic trace equivalence between high-level spec and lowered bare-metal
    execution.

    **Oracle-debt retirement (2026-08-27): `native_decide` -> `decide`.** Spike 1 takes no input, so
    this is a closed-term claim about one fixed program, not a real `∀`. `runBareMetalTrace`
    (`Gasm/Targets/BareMetal/Device.lean`) and the shared `runProgramTraceWithLoops`
    (`Gasm/Targets/X86_64/Semantics.lean`) are ordinary structurally-recursive `def`s (`grep -rn
    "partial def" Gasm/Targets/X86_64 Gasm/Targets/BareMetal` returns nothing), so there is no opaque
    interpreter core here -- unlike the Wasm sibling of this theorem, which remains blocked on the
    `evalInstrs`/`evalLoop` `mutual partial` group being a genuine `opaque` constant. The only
    obstacle empirically found was depth, not opacity: plain `decide` hit Lean's elaborator recursion
    guard ("maximum recursion depth has been reached") on the UART byte-by-byte console-output
    unfolding, which `set_option maxRecDepth 4000` clears -- a real, terminating, kernel-checked
    reduction that was simply deeper than the 512 default, not a stuck or missing equation. -/
theorem spike1_baremetal_canonical_effect_trace_equivalence :
    (runBareMetalTrace spike1BareMetalInstructions spike1BareMetalExecutable.load ==
     runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) = true := by
  set_option maxRecDepth 4000 in
  decide

/-- Exact linked x86 bare-metal artifact used at the universal program boundary. -/
def spike1BareMetalArtifact : BareMetalArtifact where
  executable := spike1BareMetalExecutable
  instructions := spike1BareMetalInstructions
  artifactConnected := rfl

def spike1BareMetalCapabilities : CapabilityComposition (BareMetalX86_64 AnyEvent) where
  root :=
    { Context := Unit
      providers := []
      establishes := fun artifact _ _ _ => artifact = spike1BareMetalArtifact }
  realize := fun _ _ => ()
  realizeSupports := by
    intro _ _ provider membership
    exact nomatch provider

def spike1BareMetalSpecification :
    ProgramSpecification (BareMetalX86_64 AnyEvent) spike1BareMetalCapabilities where
  observe := fun _ _ => .debugExited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit))

theorem spike1_baremetal_outcome :
    runBareMetalOutcome spike1BareMetalInstructions spike1BareMetalExecutable.load =
      .debugExited 0 (runModelTrace (helloWorldSpec : TraceM AnyEvent Unit)) := by
  set_option maxRecDepth 4000 in
    decide

def spike1BareMetalArtifactCertificate : ProgramArtifactCertificate (BareMetalX86_64 AnyEvent) where
  artifact := spike1BareMetalArtifact
  exports := VerifiedExportSet.empty _ _ _ _ _ () rfl rfl rfl
  exportsArtifact := rfl
  artifactConnection := spike1BareMetalArtifact.artifactConnected

def spike1BareMetalProviderCertificate :
    ProgramProviderCertificate (BareMetalX86_64 AnyEvent)
      spike1BareMetalCapabilities spike1BareMetalArtifact where
  importsCovered := by
    intro imported h
    exact nomatch imported
  providersLinked := by
    intro provider h
    exact nomatch provider

def spike1BareMetalAdmissibilityCertificate :
    ProgramAdmissibilityCertificate (BareMetalX86_64 AnyEvent)
      spike1BareMetalCapabilities spike1BareMetalArtifact where
  platformAdmissible := by
    intro _ context _
    rcases context with ⟨⟩
    change (runBareMetalOutcome spike1BareMetalInstructions spike1BareMetalExecutable.load).isAdmissible
    rw [spike1_baremetal_outcome]
    trivial

def spike1BareMetalBehaviorCertificate :
    ProgramBehaviorCertificate (BareMetalX86_64 AnyEvent)
      spike1BareMetalCapabilities spike1BareMetalArtifact spike1BareMetalSpecification where
  traceEquivalence := by
    intro _ context _
    rcases context with ⟨⟩
    exact spike1_baremetal_outcome

/-- Sole universal verified authority for the x86 bare-metal image. -/
def spike1VerifiedBareMetalProgram :
    VerifiedProgram (BareMetalX86_64 AnyEvent) spike1BareMetalCapabilities
      spike1BareMetalSpecification :=
  VerifiedProgram.compose "Spike 1: Bare Metal x86-64 Hello World"
    spike1BareMetalSpecification spike1BareMetalArtifactCertificate spike1BareMetalProviderCertificate
    spike1BareMetalAdmissibilityCertificate spike1BareMetalBehaviorCertificate

end Spikes.Spike1Hello.BareMetal

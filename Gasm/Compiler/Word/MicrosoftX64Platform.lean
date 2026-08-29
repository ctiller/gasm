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

import Gasm.Compiler.Word.MicrosoftX64
import Gasm.Core.Verification
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge

namespace Gasm.Compiler.Word.MicrosoftX64

open Gasm.Core.Verification
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#microsoft-x64-staged-platform-adapter -/
/-- Artifact-owned staging evidence for one compiled straight-line body. It deliberately stops
    before boundary publication: native platform profiles do not yet expose callable entries. -/
structure MicrosoftX64StraightLinePlacement {Event : Type} (source : Function)
    (lowered : LocalCertificate source) (artifact : WindowsX86_64Artifact)
    (runtime : ExternalCallInterceptor X86_64 Event) (initial : X86_64MachineState) where
  bodyBase : UInt64
  lookup : ContextualStraightLinePlacement
    (indexInstructions artifact.executable.load.rip artifact.instructions)
    bodyBase lowered.instructions initial
  initialSafe : initial.fault = none
  runtimeSilent : @RuntimeSilentOn Event runtime lowered.instructions initial

/- REF: docs/MACRO_ASSEMBLER.md#microsoft-x64-staged-platform-adapter -/
/-- The compiler's local certificate and artifact-owned placement jointly refine exactly the body
    prefix of production execution. The continuation and its fuel remain caller-owned. -/
theorem LocalCertificate.runProgramOutcomeLoop_prefix {Event : Type} {source : Function}
    (lowered : LocalCertificate source) (artifact : WindowsX86_64Artifact)
    (runtime : ExternalCallInterceptor X86_64 Event) (initial : X86_64MachineState)
    (placed : MicrosoftX64StraightLinePlacement source lowered artifact runtime initial)
    (continuationFuel : Nat) (eventsRev : List Event) :
    letI := runtime
    runProgramOutcomeLoop
        (indexInstructions artifact.executable.load.rip artifact.instructions)
        (lowered.instructions.length + continuationFuel) initial eventsRev =
      runProgramOutcomeLoop
        (indexInstructions artifact.executable.load.rip artifact.instructions)
        continuationFuel (runLocalSteps lowered.instructions initial) eventsRev := by
  letI := runtime
  exact Gasm.Targets.X86_64.MacroAssembler.runProgramOutcomeLoop_prefix
    lowered.instructions lowered.controlFlowFree
    (indexInstructions artifact.executable.load.rip artifact.instructions)
    placed.bodyBase initial placed.lookup placed.runtimeSilent placed.initialSafe
    continuationFuel eventsRev

/- REF: docs/MACRO_ASSEMBLER.md#microsoft-x64-staged-platform-adapter -/
/-- Source-level result at the exact fallthrough state reached by the contextual runner bridge. -/
theorem LocalCertificate.fallthroughResult {source : Function}
    (lowered : LocalCertificate source) (initial : X86_64MachineState) :
    (runLocalSteps lowered.instructions initial).gprs .rax =
      source.fn (argsOfState initial) :=
  lowered.localResult initial

/- REF: docs/MACRO_ASSEMBLER.md#microsoft-x64-staged-platform-adapter -/
theorem LocalCertificate.fallthroughPreservesGpr {source : Function}
    (lowered : LocalCertificate source) (initial : X86_64MachineState) (register : Reg64)
    (preserved : register ∉ lowered.clobberedGprs) :
    (runLocalSteps lowered.instructions initial).gprs register = initial.gprs register :=
  lowered.preservesGpr initial register preserved

/- REF: docs/MACRO_ASSEMBLER.md#microsoft-x64-staged-platform-adapter -/
theorem LocalCertificate.fallthroughPreservesMemory {source : Function}
    (lowered : LocalCertificate source) (initial : X86_64MachineState) :
    (runLocalSteps lowered.instructions initial).memory = initial.memory :=
  lowered.preservesMemory initial

/- REF: docs/MACRO_ASSEMBLER.md#microsoft-x64-staged-platform-adapter -/
theorem LocalCertificate.fallthroughPreservesInputs {source : Function}
    (lowered : LocalCertificate source) (initial : X86_64MachineState) :
    argsOfState (runLocalSteps lowered.instructions initial) = argsOfState initial :=
  lowered.preservesInputs initial

end Gasm.Compiler.Word.MicrosoftX64

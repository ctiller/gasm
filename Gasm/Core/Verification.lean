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
import Gasm.Core.Platform
import Gasm.Effects.Trace
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Dispatcher
import Gasm.Targets.Linux.Linker
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.Linux.Linker

namespace Gasm.Core.Verification

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Linux

export Gasm.Core.Platform
  (Environment Platform Capability CapabilityComposition VerifiedProgram
   emitVerifiedProgram FuzzingEmitter rawEmitForFuzzing)

/-! Native platform profiles. The artifact pairs the emitted image with the
instruction sequence whose operational semantics is proved. -/

structure WindowsX86_64Artifact where
  executable : WindowsExecutable
  instructions : List X86_64Instr

structure LinuxX86_64Artifact where
  executable : LinuxExecutable
  instructions : List X86_64Instr

structure LinuxAArch64Artifact where
  executable : AArch64LinuxExecutable
  instructions : List AnyAArch64Instruction

inductive WindowsX86_64 (Event : Type)
inductive LinuxX86_64 (Event : Type)
inductive LinuxAArch64 (Event : Type)

/-- Standalone executables publish no callable library boundary. -/
inductive NoExport

instance {Event : Type} : Platform (WindowsX86_64 Event) where
  Artifact := WindowsX86_64Artifact
  State := X86_64MachineState
  Observation := List Event
  RuntimeContext := Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event
  Import := Win32Function
  ExportName := String
  ABIRequirement := String
  ConcreteImplementation := Address
  Export := NoExport
  imports := fun artifact => artifact.executable.imports
  artifactExports := fun _ => []
  exportName := fun exported => nomatch exported
  exportContract := fun exported => nomatch exported
  exportImplementation := fun exported => nomatch exported
  exportABI := fun exported => nomatch exported
  exportRuntime := fun exported => nomatch exported
  realizesExport := fun _ exported => nomatch exported
  artifactConnected := fun artifact =>
    artifact.executable.textBytes =
      Gasm.Targets.X86_64.Assembler.serializeInstructions artifact.instructions
  load := fun artifact environment =>
    let state := artifact.executable.loadWithStdin environment.stdin
    { state with incomingRequests := environment.incomingRequests }
  run := fun runtime artifact state =>
    letI := runtime
    runAsmTrace artifact.instructions state
  admissible := fun runtime artifact state =>
    letI := runtime
    (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions 50000 state).isAdmissible
  emit := fun artifact => .ok artifact.executable.emit

instance {Event : Type} : Platform (LinuxX86_64 Event) where
  Artifact := LinuxX86_64Artifact
  State := X86_64MachineState
  Observation := List Event
  RuntimeContext := Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event
  Import := Unit
  ExportName := String
  ABIRequirement := String
  ConcreteImplementation := Address
  Export := NoExport
  imports := fun _ => []
  artifactExports := fun _ => []
  exportName := fun exported => nomatch exported
  exportContract := fun exported => nomatch exported
  exportImplementation := fun exported => nomatch exported
  exportABI := fun exported => nomatch exported
  exportRuntime := fun exported => nomatch exported
  realizesExport := fun _ exported => nomatch exported
  artifactConnected := fun artifact =>
    artifact.executable.textBytes =
      Gasm.Targets.X86_64.Assembler.serializeInstructions artifact.instructions
  load := fun artifact environment =>
    let state := artifact.executable.loadWithStdin environment.stdin
    { state with incomingRequests := environment.incomingRequests }
  run := fun runtime artifact state =>
    letI := runtime
    runAsmTrace artifact.instructions state
  admissible := fun runtime artifact state =>
    letI := runtime
    (runProgramOutcomeWithLoops (Event := Event) state.rip artifact.instructions 50000 state).isAdmissible
  emit := fun artifact => .ok artifact.executable.emit

instance {Event : Type} : Platform (LinuxAArch64 Event) where
  Artifact := LinuxAArch64Artifact
  State := AArch64MachineState
  Observation := List Event
  RuntimeContext := Gasm.Targets.AArch64.ExternalCallInterceptor AArch64 Event
  Import := Unit
  ExportName := String
  ABIRequirement := String
  ConcreteImplementation := Address
  Export := NoExport
  imports := fun _ => []
  artifactExports := fun _ => []
  exportName := fun exported => nomatch exported
  exportContract := fun exported => nomatch exported
  exportImplementation := fun exported => nomatch exported
  exportABI := fun exported => nomatch exported
  exportRuntime := fun exported => nomatch exported
  realizesExport := fun _ exported => nomatch exported
  artifactConnected := fun artifact =>
    artifact.executable.textBytes =
      Gasm.Targets.AArch64.Linux.serializeInstructions artifact.instructions
  load := fun artifact environment =>
    let state := artifact.executable.loadWithStdin environment.stdin
    { state with incomingRequests := environment.incomingRequests }
  run := fun runtime artifact state =>
    letI := runtime
    runAArch64Trace artifact.instructions state
  admissible := fun runtime artifact state =>
    letI := runtime
    (Gasm.Targets.AArch64.runAArch64Outcome (Event := Event)
      state.pc artifact.instructions 50000 state).isAdmissible
  emit := fun artifact => .ok artifact.executable.emit

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- Windows host services form an explicit typed capability row. -/
def windowsHostCapability (Event : Type)
    [Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event] :
    Capability (WindowsX86_64 Event) where
  Context := Unit
  provides := fun _ => True
  implementationConnected := fun artifact => Platform.artifactConnected artifact
  establishes := fun _ _ _ _ => True

def windowsHostCapabilities (Event : Type)
    [Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event] :
    CapabilityComposition (WindowsX86_64 Event) where
  root := windowsHostCapability Event
  realize := fun _ => inferInstance

def linuxHostCapabilities (Event : Type)
    [Gasm.Targets.X86_64.ExternalCallInterceptor X86_64 Event] :
    CapabilityComposition (LinuxX86_64 Event) where
  root := Capability.empty _
  realize := fun _ => inferInstance

def aarch64LinuxHostCapabilities (Event : Type)
    [Gasm.Targets.AArch64.ExternalCallInterceptor AArch64 Event] :
    CapabilityComposition (LinuxAArch64 Event) where
  root := Capability.empty _
  realize := fun _ => inferInstance

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- A verified library routine remains target-independent. -/
structure VerifiedRoutine (SpecState : Type) (MachineState : Type) (Event : Type) [BEq Event] where
  name : String
  program : List SymbolicInstr
  couplingInv : SpecState → MachineState → Bool
  specStep : SpecState → Option (SpecState × List Event)
  machStep : MachineState → Option (MachineState × List Event)
  traceEquivalence :
    ∀ (s_spec : SpecState) (s_mach : MachineState),
      couplingInv s_spec s_mach = true →
      match specStep s_spec, machStep s_mach with
      | some (s_spec', specTrace), some (s_mach', machTrace) =>
          (specTrace == machTrace && couplingInv s_spec' s_mach' == true) = true
      | none, none => True
      | _, _ => False

end Gasm.Core.Verification

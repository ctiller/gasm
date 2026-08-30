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
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.BareMetal.ELFFormat
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Emitter

namespace Gasm.Targets.BareMetal

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.X86_64

/-- x86-64 freestanding execution profile for the universal verified-program boundary. -/
inductive BareMetalX86_64 (Event : Type) where
  | profile

/- REF: docs/TARGETS/BARE_METAL.md#3-minimal-64-bit-elf-executable-packaging-pvh-boot-protocol -/
/-- Structured bare-metal ELF64 executable image. -/
structure BareMetalExecutable where
  textBytes : ByteArray
  dataBytes : ByteArray := ByteArray.empty
  deriving DecidableEq, Inhabited

namespace BareMetalExecutable

/- REF: docs/TARGETS/BARE_METAL.md#31-elf64-header-program-headers -/
/-- The sole flat-image layout.  It is shared by execution and emission, so a verified artifact
cannot pair a custom in-memory entry point with a different canonical ELF header. -/
def layout (exe : BareMetalExecutable) : BareMetalLayout :=
  computeBareMetalLayout exe.textBytes.size exe.dataBytes.size

/- REF: docs/TARGETS/BARE_METAL.md#31-elf64-header-program-headers -/
/-- Serializes the executable to flat ELF64 binary image bytes with Xen PVH boot note. -/
def emit (exe : BareMetalExecutable) : ByteArray :=
  emitBareMetalELFExecutableWithLayout exe.layout exe.textBytes exe.dataBytes

/-- Emission and loading use the exact same derived layout. -/
theorem emit_uses_load_layout (exe : BareMetalExecutable) :
    exe.emit = emitBareMetalELFExecutableWithLayout exe.layout exe.textBytes exe.dataBytes := rfl

/- REF: docs/TARGETS/BARE_METAL.md#1-machine-model-in-freestanding-mode -/
/-- Constructs the initial machine state for bare-metal x86-64 execution. -/
def load (exe : BareMetalExecutable) : BareMetalMachineState :=
  let imageLayout := exe.layout
  let textStart := imageLayout.entryAddr
  let textEnd := textStart + exe.textBytes.size.toUInt64
  let dataStart := textEnd
  let dataEnd := dataStart + exe.dataBytes.size.toUInt64
  let mem : Address → Byte := fun a =>
    if a >= textStart && a < textEnd then
      exe.textBytes.get! (a - textStart).toNat
    else if a >= dataStart && a < dataEnd then
      exe.dataBytes.get! (a - dataStart).toNat
    else 0
  let cpu : X86_64MachineState := {
    rip := imageLayout.entryAddr,
    gprs := fun r => if r == .rsp then imageLayout.loadBase + 0x20000 else 0,
    flags := 0,
    memory := X86_64Mem.initRegion mem
  }
  { cpu := cpu, devices := {} }

end BareMetalExecutable

/-- An emitted bare-metal image paired with the exact instruction stream whose classified
execution it exposes. -/
structure BareMetalArtifact where
  executable : BareMetalExecutable
  instructions : List X86_64Instr
  artifactConnected : executable.textBytes = Gasm.Targets.X86_64.Assembler.serializeInstructions instructions

def BareMetalArtifact.connected (artifact : BareMetalArtifact) : Prop :=
  artifact.executable.textBytes = Gasm.Targets.X86_64.Assembler.serializeInstructions artifact.instructions

instance {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] :
    Platform (BareMetalX86_64 Event) where
  Artifact := BareMetalArtifact
  State := BareMetalMachineState
  Observation := BareMetalRunOutcome Event
  RuntimeContext := Unit
  Import := Unit
  Provider := Empty
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := BareMetalX86_64 Event
  boundarySpec := Gasm.Core.Verification.emptyBoundarySpec
  boundarySemantics := Gasm.Core.Verification.emptyBoundarySemantics _ BareMetalMachineState
  imports := fun _ => []
  providerProvides := fun provider => nomatch provider
  providerLinked := fun _ provider => nomatch provider
  runtimeSupports := fun _ _ provider => nomatch provider
  boundaryArtifact := fun _ => ()
  artifactConnected := BareMetalArtifact.connected
  load := fun artifact _ => artifact.executable.load
  run := fun _ artifact state => runBareMetalOutcome (Event := Event) artifact.instructions state
  admissible := fun _ artifact state =>
    (runBareMetalOutcome (Event := Event) artifact.instructions state).isAdmissible
  emit := fun artifact => .ok artifact.executable.emit

end Gasm.Targets.BareMetal

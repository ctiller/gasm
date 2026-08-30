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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Instructions.Base
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Emitter

namespace Gasm.Targets.AArch64.BareMetal

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/-- AArch64 freestanding execution profile for the universal verified-program boundary. -/
inductive BareMetalAArch64 (Event : Type) where
  | profile

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Structured AArch64 bare-metal ELF64 executable image. -/
structure AArch64BareMetalExecutable where
  textBytes : ByteArray
  dataBytes : ByteArray := ByteArray.empty
  deriving DecidableEq, Inhabited

namespace AArch64BareMetalExecutable

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- The shared canonical layout for the serialized image and in-memory machine state. -/
def layout (exe : AArch64BareMetalExecutable) : AArch64BareMetalLayout :=
  computeAArch64BareMetalLayout exe.textBytes.size exe.dataBytes.size

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Serializes the executable to flat ELF64 binary image bytes with EM_AARCH64. -/
def emit (exe : AArch64BareMetalExecutable) : ByteArray :=
  emitBareMetalELFExecutableWithLayout exe.layout exe.textBytes exe.dataBytes

/-- Emission and loading use the exact same derived layout. -/
theorem emit_uses_load_layout (exe : AArch64BareMetalExecutable) :
    exe.emit = emitBareMetalELFExecutableWithLayout exe.layout exe.textBytes exe.dataBytes := rfl

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Constructs the initial machine state for bare-metal AArch64 execution. -/
def load (exe : AArch64BareMetalExecutable) : AArch64BareMetalMachineState :=
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
  let cpu : AArch64MachineState := {
    pc := imageLayout.entryAddr,
    gprs := fun _ => 0,
    sp := imageLayout.loadBase + 0x100000, -- 1 MB stack offset
    nzcv := default,
    memory := AArch64Mem.initRegion mem
  }
  { cpu := cpu, devices := {} }

end AArch64BareMetalExecutable

/-- Canonical instruction serialization shared by the linker and artifact boundary. -/
def serializeInstructions (instrs : List AnyAArch64Instruction) : ByteArray :=
  instrs.foldl (fun acc instruction => acc ++ AArch64Instruction.encode instruction) ByteArray.empty

/-- AArch64 bare-metal image paired with the exact instruction stream exposed by its classified
platform execution. -/
structure BareMetalArtifact where
  executable : AArch64BareMetalExecutable
  instructions : List AnyAArch64Instruction
  artifactConnected : executable.textBytes = serializeInstructions instructions

def BareMetalArtifact.connected (artifact : BareMetalArtifact) : Prop :=
  artifact.executable.textBytes = serializeInstructions artifact.instructions

instance {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event] :
    Platform (BareMetalAArch64 Event) where
  Artifact := BareMetalArtifact
  State := AArch64BareMetalMachineState
  Observation := BareMetalRunOutcome Event
  RuntimeContext := Unit
  Import := Unit
  Provider := Empty
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := BareMetalAArch64 Event
  boundarySpec := Gasm.Core.Verification.emptyBoundarySpec
  boundarySemantics := Gasm.Core.Verification.emptyBoundarySemantics _ AArch64BareMetalMachineState
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

end Gasm.Targets.AArch64.BareMetal

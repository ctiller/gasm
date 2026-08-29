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
open Gasm.Effects
open Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Structured AArch64 bare-metal ELF64 executable image. -/
structure AArch64BareMetalExecutable where
  loadBase  : Address   := 0x40000000 -- 1 GB RAM Base
  entryAddr : Address   := 0x40001000 -- Entry at .text start
  textBytes : ByteArray
  dataBytes : ByteArray := ByteArray.empty
  deriving DecidableEq, Inhabited

namespace AArch64BareMetalExecutable

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Serializes the executable to flat ELF64 binary image bytes with EM_AARCH64. -/
def emit (exe : AArch64BareMetalExecutable) : ByteArray :=
  emitBareMetalELFExecutable exe.textBytes exe.dataBytes

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Constructs the initial machine state for bare-metal AArch64 execution. -/
def load (exe : AArch64BareMetalExecutable) : AArch64BareMetalMachineState :=
  let textStart := exe.entryAddr
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
    pc := exe.entryAddr,
    gprs := fun _ => 0,
    sp := exe.loadBase + 0x100000, -- 1 MB stack offset
    nzcv := default,
    memory := AArch64Mem.initRegion mem
  }
  { cpu := cpu, devices := {} }

end AArch64BareMetalExecutable

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- First-Class Verified Program Contract for AArch64 Bare Metal execution. -/
structure VerifiedBareMetalProgram (Env : Type := Unit) (Event : Type := AnyEvent)
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [BEq Event] where
  name             : String
  executable       : AArch64BareMetalExecutable
  instructions     : List AnyAArch64Instruction
  spec             : Env → List Event
  traceEquivalence : ∀ (env : Env),
    (runBareMetalTrace instructions executable.load == spec env) = true

/- REF: docs/TARGETS/ARM64.md#13-bare-metal-target-qemu-virt-platform-execution -/
/-- Type-Enforced Code Emission for verified bare-metal programs on AArch64. -/
def emitVerifiedBareMetalExecutable {Env : Type} {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [BEq Event]
    (p : VerifiedBareMetalProgram Env Event) : ByteArray :=
  p.executable.emit

end Gasm.Targets.AArch64.BareMetal

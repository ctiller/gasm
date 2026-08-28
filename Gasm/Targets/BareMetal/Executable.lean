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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.BareMetal.ELFFormat
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Emitter

namespace Gasm.Targets.BareMetal

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64

/- REF: docs/TARGETS/BARE_METAL.md#3-minimal-64-bit-elf-executable-packaging-pvh-boot-protocol -/
/-- Structured bare-metal ELF64 executable image. -/
structure BareMetalExecutable where
  loadBase  : Address   := 0x200000
  entryAddr : Address   := 0x201000
  textBytes : ByteArray
  dataBytes : ByteArray := ByteArray.empty
  deriving DecidableEq, Inhabited

namespace BareMetalExecutable

/- REF: docs/TARGETS/BARE_METAL.md#31-elf64-header-program-headers -/
/-- Serializes the executable to flat ELF64 binary image bytes with Xen PVH boot note. -/
def emit (exe : BareMetalExecutable) : ByteArray :=
  emitBareMetalELFExecutable exe.textBytes exe.dataBytes

/- REF: docs/TARGETS/BARE_METAL.md#1-machine-model-in-freestanding-mode -/
/-- Constructs the initial machine state for bare-metal x86-64 execution. -/
def load (exe : BareMetalExecutable) : BareMetalMachineState :=
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
  let cpu : X86_64MachineState := {
    rip := exe.entryAddr,
    gprs := fun r => if r == .rsp then 0x200000 + 0x20000 else 0,
    flags := 0,
    memory := X86_64Mem.initRegion mem
  }
  { cpu := cpu, devices := {} }

end BareMetalExecutable

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-Class Verified Program Contract for x86-64 Bare Metal execution. -/
structure VerifiedBareMetalProgram (Env : Type := Unit) (Event : Type := AnyEvent)
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [BEq Event] where
  name             : String
  executable       : BareMetalExecutable
  instructions     : List X86_64Instr
  spec             : Env → List Event
  traceEquivalence : ∀ (env : Env),
    (runBareMetalTrace instructions executable.load == spec env) = true

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Type-Enforced Code Emission for verified bare-metal programs. -/
def emitVerifiedBareMetalExecutable {Env : Type} {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [BEq Event]
    (p : VerifiedBareMetalProgram Env Event) : ByteArray :=
  p.executable.emit

end Gasm.Targets.BareMetal

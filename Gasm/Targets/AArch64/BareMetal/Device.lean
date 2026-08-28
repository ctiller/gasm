/-
Copyright 2026 Google LLC

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
import Gasm.Targets.AArch64.Machine
import Gasm.Targets.AArch64.MemoryCell

namespace Gasm.Targets.AArch64.BareMetal

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- State container for bare-metal simulated hardware peripheral devices on AArch64. -/
structure AArch64BareMetalDeviceState where
  serialBuffer : ByteArray := ByteArray.empty
  exitStatus   : Option UInt32 := none
  deriving DecidableEq, Inhabited, BEq

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Combined AArch64 bare-metal machine and device state. -/
structure AArch64BareMetalMachineState where
  cpu     : AArch64MachineState
  devices : AArch64BareMetalDeviceState := {}
  deriving Inhabited

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Single-step transition for bare-metal AArch64 execution with MMIO device simulation. -/
def stepBareMetal (instr : AnyAArch64Instruction) (s : AArch64BareMetalMachineState) : AArch64BareMetalMachineState :=
  let sCpu' := step instr s.cpu
  if sCpu'.terminated then
    let dev' := { s.devices with exitStatus := some sCpu'.exitCode }
    { cpu := sCpu', devices := dev' }
  else
    -- Capture MMIO store to UART Data Register at 0x09000000
    let oldVal := AArch64Mem.readByte s.cpu.memory 0x09000000
    let newVal := AArch64Mem.readByte sCpu'.memory 0x09000000
    if newVal != oldVal then
      let dev' := { s.devices with serialBuffer := s.devices.serialBuffer.push newVal }
      let cpu' := { sCpu' with memory := AArch64Mem.writeByte sCpu'.memory 0x09000000 oldVal }
      { cpu := cpu', devices := dev' }
    else
      { cpu := sCpu', devices := s.devices }

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Fuel-based evaluator executing AArch64 instructions on bare-metal machine state. -/
def runBareMetalProgram (baseRip : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat) (s : AArch64BareMetalMachineState) : AArch64BareMetalMachineState :=
  let indexed := indexInstructions baseRip instructions
  let rec loop (fuel : Nat) (s : AArch64BareMetalMachineState) : AArch64BareMetalMachineState :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match instructionAtPcIndexed indexed s.cpu.pc with
      | none => s
      | some instr =>
        let s' := stepBareMetal instr s
        if s'.cpu.terminated || s'.cpu.fault.isSome then s'
        else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Evaluates bare-metal execution and produces canonical observable effect trace. -/
def runBareMetalTrace {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    (instructions : List AnyAArch64Instruction) (s0 : AArch64BareMetalMachineState) (fuel : Nat := 50000) : List Event :=
  let finalState := runBareMetalProgram s0.cpu.pc instructions fuel s0
  let consoleStr := match String.fromUTF8? finalState.devices.serialBuffer with
    | some str => str
    | none => String.ofList (finalState.devices.serialBuffer.toList.map (fun b => Char.ofNat b.toNat))
  let exitCode := finalState.devices.exitStatus.getD 0
  [ Inject.inject (ConsoleEvent.out consoleStr),
    Inject.inject (ProcessEvent.exit exitCode) ]

end Gasm.Targets.AArch64.BareMetal

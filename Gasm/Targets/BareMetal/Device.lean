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
import Gasm.Targets.BareMetal.UART

namespace Gasm.Targets.BareMetal

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.BareMetal.UART

/- REF: docs/TARGETS/BARE_METAL.md#42-qemu-isa-debug-exit-port-control-0xf4-0x501 -/
/-- QEMU isa-debug-exit default I/O port. -/
def DEBUG_EXIT_PORT : UInt16 := 0xF4

/- REF: docs/TARGETS/BARE_METAL.md#42-qemu-isa-debug-exit-port-control-0xf4-0x501 -/
/-- QEMU isa-debug-exit alternate I/O port. -/
def DEBUG_EXIT_PORT_ALT : UInt16 := 0x501

/- REF: docs/TARGETS/BARE_METAL.md#1-machine-model-in-freestanding-mode -/
/-- State container for bare-metal simulated hardware peripheral devices. -/
structure BareMetalDeviceState where
  dlab         : Bool := false
  dll          : UInt8 := 0
  dlm          : UInt8 := 0
  ier          : UInt8 := 0
  lcr          : UInt8 := 0
  fcr          : UInt8 := 0
  mcr          : UInt8 := 0
  serialBuffer : ByteArray := ByteArray.empty
  exitStatus   : Option UInt32 := none
  /-- Set only by the QEMU debug-exit device.  A CPU halt is a distinct platform stop. -/
  debugExitRequested : Option UInt32 := none
  deriving DecidableEq, Inhabited

/- REF: docs/TARGETS/BARE_METAL.md#1-machine-model-in-freestanding-mode -/
/-- Combined bare-metal machine and device state. -/
structure BareMetalMachineState where
  cpu     : X86_64MachineState
  devices : BareMetalDeviceState := {}
  deriving Inhabited

/- REF: docs/TARGETS/BARE_METAL.md#41-16550-uart-serial-port-protocol-0x3f8-com1 -/
/- REF: docs/TARGETS/BARE_METAL.md#42-qemu-isa-debug-exit-port-control-0xf4-0x501 -/
/-- Single-step transition for bare-metal x86-64 execution with port I/O device simulation. -/
def stepBareMetal (instr : X86_64Instr) (s : BareMetalMachineState) : BareMetalMachineState :=
  let sCpu' := X86_64Instruction.step instr s.cpu
  -- Check for port I/O instruction interactions
  let bytes := X86_64Instruction.encode instr
  if bytes.size > 0 then
    let op := bytes.get! 0
    -- 1. IN AL, DX (0xEC) / IN AL, imm8 (0xE4)
    if op == 0xEC || op == 0xE4 then
      let port : UInt16 := if op == 0xEC then (s.cpu.gprs .rdx &&& 0xFFFF).toUInt16 else if bytes.size > 1 then (bytes.get! 1).toUInt16 else 0
      if port == UART_LSR then
        -- Return Transmitter Empty (0x20) in AL
        let rax := sCpu'.gprs .rax
        let rax' := (rax &&& 0xFFFFFFFFFFFFFF00) ||| LSR_THRE.toUInt64
        let gprs' := fun r => if r == .rax then rax' else sCpu'.gprs r
        { s with cpu := { sCpu' with gprs := gprs' } }
      else
        { s with cpu := sCpu' }

    -- 2. OUT DX, AL (0xEE) / OUT imm8, AL (0xE6)
    else if op == 0xEE || op == 0xE6 then
      let port : UInt16 := if op == 0xEE then (s.cpu.gprs .rdx &&& 0xFFFF).toUInt16 else if bytes.size > 1 then (bytes.get! 1).toUInt16 else 0
      let byteVal := (s.cpu.gprs .rax &&& 0xFF).toUInt8
      if port == UART_LCR then
        let dlab' := (byteVal &&& LCR_DLAB) != 0
        let dev' := { s.devices with lcr := byteVal, dlab := dlab' }
        { s with cpu := sCpu', devices := dev' }
      else if port == UART_DATA then
        if s.devices.dlab then
          let dev' := { s.devices with dll := byteVal }
          { s with cpu := sCpu', devices := dev' }
        else
          let dev' := { s.devices with serialBuffer := s.devices.serialBuffer.push byteVal }
          { s with cpu := sCpu', devices := dev' }
      else if port == UART_IER then
        if s.devices.dlab then
          let dev' := { s.devices with dlm := byteVal }
          { s with cpu := sCpu', devices := dev' }
        else
          let dev' := { s.devices with ier := byteVal }
          { s with cpu := sCpu', devices := dev' }
      else if port == UART_IIR_FCR then
        let dev' := { s.devices with fcr := byteVal }
        { s with cpu := sCpu', devices := dev' }
      else if port == UART_MCR then
        let dev' := { s.devices with mcr := byteVal }
        { s with cpu := sCpu', devices := dev' }
      else if port == DEBUG_EXIT_PORT || port == DEBUG_EXIT_PORT_ALT then
        let dev' := { { s.devices with exitStatus := some (byteVal.toUInt32) } with
          debugExitRequested := some (byteVal.toUInt32) }
        { s with cpu := { sCpu' with fault := some .halted }, devices := dev' }
      else
        { s with cpu := sCpu' }

    -- 3. HLT (0xF4)
    else if op == 0xF4 then
      let dev' := if s.devices.exitStatus.isNone then { s.devices with exitStatus := some 0 } else s.devices
      { s with cpu := { sCpu' with fault := some .halted }, devices := dev' }

    else
      { s with cpu := sCpu' }
  else
    { s with cpu := sCpu' }

/- REF: docs/TARGETS/BARE_METAL.md#1-machine-model-in-freestanding-mode -/
/-- Fuel-based evaluator executing a list of x86-64 instructions on bare-metal machine state. -/
def runBareMetalProgram (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : BareMetalMachineState) : BareMetalMachineState :=
  let indexed := indexInstructions baseRip instructions
  let rec loop (fuel : Nat) (s : BareMetalMachineState) : BareMetalMachineState :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match instructionAtRipIndexed indexed s.cpu.rip with
      | none => s
      | some instr =>
        let s' := stepBareMetal instr s
        if s'.cpu.faulted then s'
        else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/BARE_METAL.md#7-spike-1-bare-metal-hello-world-verification -/
/-- Evaluates bare-metal execution and produces canonical observable effect trace. -/
def bareMetalConsoleEvents {Event : Type} [Inject ConsoleEvent Event]
    (finalState : BareMetalMachineState) : List Event :=
  let consoleStr := match String.fromUTF8? finalState.devices.serialBuffer with
    | some str => str
    | none => String.ofList (finalState.devices.serialBuffer.toList.map (fun b => Char.ofNat b.toNat))
  [Inject.inject (ConsoleEvent.out consoleStr)]

/-- Bare-metal execution preserves its stop classification.  In particular, fuel exhaustion,
faults, a CPU halt, and falling off the instruction stream are not synthesized as debug exits. -/
inductive BareMetalRunOutcome (Event : Type) where
  | debugExited (code : UInt32) (events : List Event)
  | platformStopped (cause : X86_64Fault) (events : List Event)
  | faulted (cause : X86_64Fault) (events : List Event)
  | completed (events : List Event)
  | fuelExhausted (events : List Event)
  deriving DecidableEq

namespace BareMetalRunOutcome

def events : BareMetalRunOutcome Event → List Event
  | .debugExited _ events | .platformStopped _ events | .faulted _ events |
      .completed events | .fuelExhausted events => events

def isAdmissible : BareMetalRunOutcome Event → Prop
  | .debugExited _ _ => True
  | .platformStopped _ _ | .faulted _ _ | .completed _ | .fuelExhausted _ => False

end BareMetalRunOutcome

/-- Classified bare-metal execution with an explicit evaluator bound. -/
def runBareMetalOutcome {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    (instructions : List X86_64Instr) (s0 : BareMetalMachineState) (fuel : Nat := 50000) :
    BareMetalRunOutcome Event :=
  let indexed := indexInstructions s0.cpu.rip instructions
  let finish (state : BareMetalMachineState) : BareMetalRunOutcome Event :=
    let console := bareMetalConsoleEvents state
    match state.devices.debugExitRequested with
    | some code => .debugExited code (console ++ [Inject.inject (ProcessEvent.exit code)])
    | none =>
      match state.cpu.fault with
      | some .halted => .platformStopped .halted console
      | some cause => .faulted cause console
      | none => .completed console
  let rec loop (remaining : Nat) (state : BareMetalMachineState) : BareMetalRunOutcome Event :=
    -- A supplied terminal state is already an observable platform result.  It must win over
    -- fuel accounting and instruction lookup, including when the caller supplies zero fuel.
    match state.devices.debugExitRequested with
    | some _ => finish state
    | none =>
      match state.cpu.fault with
      | some _ => finish state
      | none =>
        match remaining with
        | 0 =>
          match instructionAtRipIndexed indexed state.cpu.rip with
          | none => finish state
          | some _ => .fuelExhausted (bareMetalConsoleEvents state)
        | remaining + 1 =>
          match instructionAtRipIndexed indexed state.cpu.rip with
          | none => finish state
          | some instruction =>
            let after := stepBareMetal instruction state
            if after.cpu.faulted then finish after else loop remaining after
  loop fuel s0

/-- Legacy list observations are now an explicit projection of a classified run. -/
def runBareMetalTrace {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    (instructions : List X86_64Instr) (s0 : BareMetalMachineState) (fuel : Nat := 50000) : List Event :=
  (runBareMetalOutcome instructions s0 fuel).events

end Gasm.Targets.BareMetal

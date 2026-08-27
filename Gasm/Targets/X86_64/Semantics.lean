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
import Gasm.Core.Arch
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Open external call interceptor typeclass allowing target platform ABI hooks (e.g. Win32 API). -/
class ExternalCallInterceptor (Arch : Type) (Event : Type) where
  interceptCall : Address → X86_64MachineState → Option (X86_64MachineState × Option Event)

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Pure single-step transition function for x86-64 machine instructions with dynamic interception. -/
def stepX86_64 {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (instr : X86_64Instr) (s : X86_64MachineState) : X86_64MachineState × Option Event :=
  let s' := X86_64Instruction.step instr s
  match interceptor.interceptCall s'.rip s' with
  | some (s_hooked, evt) => (s_hooked, evt)
  | none => (s', none)

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Resolves the instruction positioned at targetRip dynamically from an instruction list starting at baseRip. -/
def instructionAtRip (baseRip : UInt64) (instructions : List X86_64Instr) (targetRip : UInt64) : Option X86_64Instr :=
  let rec loop (curRip : UInt64) : List X86_64Instr → Option X86_64Instr
    | [] => none
    | instr :: rest =>
      if curRip == targetRip then some instr
      else
        let sz := (X86_64Instruction.encode instr).size
        loop (curRip + sz.toUInt64) rest
  loop baseRip instructions

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Trace evaluator executing an x86-64 program with dynamic branches, loops, and external API interception. -/
def runProgramTraceWithLoops {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : X86_64MachineState) : List Event :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match instructionAtRip baseRip instructions s.rip with
    | none => []
    | some instr =>
      let s' := X86_64Instruction.step instr s
      match interceptor.interceptCall s'.rip s' with
      | some (s_hooked, some evt) =>
        if s_hooked.faulted then [evt]
        else evt :: runProgramTraceWithLoops baseRip instructions fuel s_hooked
      | some (s_hooked, none) =>
        if s_hooked.faulted then []
        else runProgramTraceWithLoops baseRip instructions fuel s_hooked
      | none =>
        if s'.faulted then []
        else runProgramTraceWithLoops baseRip instructions fuel s'

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Trace evaluator executing a list of lowered x86-64 instructions with dynamic control flow. -/
def runAsmTrace {Event : Type} [ExternalCallInterceptor X86_64 Event]
    (instructions : List X86_64Instr) (s : X86_64MachineState) (fuel : Nat := 50000) : List Event :=
  runProgramTraceWithLoops s.rip instructions fuel s

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Executes an x86-64 instruction sequence supporting branches and loops with fuel-based termination. -/
def runProgramWithLoops (baseRip : UInt64) (instructions : List X86_64Instr) (fuel : Nat) (s : X86_64MachineState) : X86_64MachineState :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    match instructionAtRip baseRip instructions s.rip with
    | none => s
    | some instr =>
      let s' := X86_64Instruction.step instr s
      if s'.faulted then s'
      else runProgramWithLoops baseRip instructions fuel s'

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Initializes a clean x86-64 machine state for function invocation with arguments. -/
def initMachineState (entryRip : Address) (args : List UInt64 := []) (stackTop : Address := 0x7FFFFFFF0008) : X86_64MachineState :=
  let argGprs : List Reg64 := [.rcx, .rdx, .r8, .r9]
  let rec setArgs (remGprs : List Reg64) (remArgs : List UInt64) (s : X86_64MachineState) : X86_64MachineState :=
    match remGprs, remArgs with
    | g :: grest, a :: arest => setArgs grest arest (s.setGpr64 g a)
    | _, _ => s
  let s0 : X86_64MachineState := {
    rip := entryRip,
    gprs := fun r => if r == .rsp then stackTop else 0,
    flags := 0,
    memory := fun _ => 0
  }
  setArgs argGprs args s0

/- REF: docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing -/
/-- Invokes an x86-64 subroutine with the given arguments and returns the 64-bit return value in RAX. -/
def callSubroutine (instructions : List X86_64Instr) (args : List UInt64) (fuel : Nat := 1000) (entryRip : Address := 0x1000) : UInt64 :=
  let s0 := initMachineState entryRip args
  let finalState := runProgramWithLoops entryRip instructions fuel s0
  finalState.gprs .rax

end Gasm.Targets.X86_64

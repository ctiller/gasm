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
import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Machine
import Gasm.Targets.AArch64.Instructions

namespace Gasm.Targets.AArch64

open Gasm.Core
open Gasm.Targets.AArch64.Instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Pure single-step operational transition function for AArch64 machine instructions via typeclass dispatch. -/
def step (instr : AnyAArch64Instruction) (s : AArch64MachineState) : AArch64MachineState :=
  AArch64Instruction.step instr s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
instance : TargetArch AArch64 where
  wordWidth    := 8
  MachineState := AArch64MachineState
  Instruction  := AnyAArch64Instruction
  stepPure pkg s := AArch64Instruction.step pkg s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Open external call interceptor typeclass allowing target platform ABI hooks (e.g. Linux syscalls or bare-metal UART). -/
class ExternalCallInterceptor (Arch : Type) (Event : Type) where
  interceptCall : UInt64 → AArch64MachineState → Option (AArch64MachineState × Option Event)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Pure single-step transition function for AArch64 machine instructions with dynamic interception. -/
def stepAArch64 {Event : Type} [interceptor : ExternalCallInterceptor AArch64 Event]
    (instr : AnyAArch64Instruction) (s : AArch64MachineState) : AArch64MachineState × Option Event :=
  let s' := step instr s
  match interceptor.interceptCall s'.pc s' with
  | some (s_hooked, evt) => (s_hooked, evt)
  | none => (s', none)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Resolves the instruction positioned at targetPc dynamically from an instruction list starting at basePc. -/
def instructionAtPc (basePc : UInt64) (instructions : List AnyAArch64Instruction) (targetPc : UInt64) : Option AnyAArch64Instruction :=
  let rec loop (curPc : UInt64) : List AnyAArch64Instruction → Option AnyAArch64Instruction
    | [] => none
    | instr :: rest =>
      if curPc == targetPc then some instr
      else loop (curPc + 4) rest
  loop basePc instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Computes byte offsets for each instruction in a sequence with fixed 4-byte stride. -/
def indexInstructions (basePc : UInt64) (instructions : List AnyAArch64Instruction) : List (UInt64 × AnyAArch64Instruction) :=
  let rec loop (curPc : UInt64) : List AnyAArch64Instruction → List (UInt64 × AnyAArch64Instruction)
    | [] => []
    | instr :: rest =>
      (curPc, instr) :: loop (curPc + 4) rest
  loop basePc instructions

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Resolves an instruction from pre-indexed address-instruction pairs without re-traversal. -/
def instructionAtPcIndexed : List (UInt64 × AnyAArch64Instruction) → UInt64 → Option AnyAArch64Instruction
  | [], _ => none
  | (pc, instr) :: rest, targetPc =>
    if pc == targetPc then some instr
    else instructionAtPcIndexed rest targetPc

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Proves that recursive indexing loop matches the linear instruction search loop. -/
theorem instructionAtPcIndexed_loop_eq (curPc : UInt64) (instructions : List AnyAArch64Instruction) (targetPc : UInt64) :
    instructionAtPcIndexed (indexInstructions.loop curPc instructions) targetPc =
    instructionAtPc.loop targetPc curPc instructions := by
  induction instructions generalizing curPc with
  | nil => rfl
  | cons i rest ih =>
    unfold indexInstructions.loop instructionAtPc.loop instructionAtPcIndexed
    split
    · rfl
    · exact ih (curPc + 4)

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Proves that pre-indexed instruction lookup is strictly equivalent to dynamic linear search. -/
theorem instructionAtPcIndexed_eq_instructionAtPc (basePc : UInt64) (instructions : List AnyAArch64Instruction) (targetPc : UInt64) :
    instructionAtPcIndexed (indexInstructions basePc instructions) targetPc =
    instructionAtPc basePc instructions targetPc := by
  exact instructionAtPcIndexed_loop_eq basePc instructions targetPc

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Executes an AArch64 instruction sequence supporting branches and loops with fuel-based termination. -/
def runProgramWithLoops (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat) (s : AArch64MachineState) : AArch64MachineState :=
  let indexed := indexInstructions basePc instructions
  let rec loop (fuel : Nat) (s : AArch64MachineState) : AArch64MachineState :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      match instructionAtPcIndexed indexed s.pc with
      | none => s
      | some instr =>
        let s' := step instr s
        if s'.isHalted then s'
        else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Initializes a clean AArch64 machine state conforming to AAPCS64. -/
def initMachineState (entryPc : UInt64) (args : List UInt64 := []) (stackTop : UInt64 := 0x7FFFFFFF0000) : AArch64MachineState :=
  let argGprs : List Reg64 := aapcs64ArgRegs
  let rec setArgs (remGprs : List Reg64) (remArgs : List UInt64) (s : AArch64MachineState) : AArch64MachineState :=
    match remGprs, remArgs with
    | g :: grest, a :: arest => setArgs grest arest (s.setReg64 g a)
    | _, _ => s
  let s0 : AArch64MachineState := {
    pc := entryPc,
    gprs := fun _ => 0,
    sp := stackTop,
    nzcv := default,
    memory := default
  }
  setArgs argGprs args s0

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Trace evaluator executing an AArch64 program with dynamic branches, loops, and external API interception. -/
def runProgramTraceWithLoops {Event : Type} [interceptor : ExternalCallInterceptor AArch64 Event]
    (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat) (s : AArch64MachineState) : List Event :=
  let indexed := indexInstructions basePc instructions
  let rec loop (fuel : Nat) (s : AArch64MachineState) : List Event :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match instructionAtPcIndexed indexed s.pc with
      | none => []
      | some instr =>
        let s' := AArch64Instruction.step instr s
        match interceptor.interceptCall s'.pc s' with
        | some (s_hooked, some evt) =>
          if s_hooked.terminated || s_hooked.fault.isSome then [evt]
          else evt :: loop fuel s_hooked
        | some (s_hooked, none) =>
          if s_hooked.terminated || s_hooked.fault.isSome then []
          else loop fuel s_hooked
        | none =>
          if s'.terminated || s'.fault.isSome then []
          else loop fuel s'
  loop fuel s

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Trace evaluator executing a list of lowered AArch64 instructions with dynamic control flow. -/
def runAArch64Trace {Event : Type} [ExternalCallInterceptor AArch64 Event]
    (instructions : List AnyAArch64Instruction) (s : AArch64MachineState) (fuel : Nat := 50000) : List Event :=
  runProgramTraceWithLoops s.pc instructions fuel s

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Fault- and fuel-honest AArch64 execution outcome used by platform admissibility. -/
inductive AArch64RunOutcome (Event : Type) where
  | completed (state : AArch64MachineState) (events : List Event)
  | faulted (state : AArch64MachineState) (events : List Event)
  | fuelExhausted (state : AArch64MachineState) (events : List Event)

def runAArch64Outcome {Event : Type} [interceptor : ExternalCallInterceptor AArch64 Event]
    (basePc : UInt64) (instructions : List AnyAArch64Instruction) (fuel : Nat)
    (initial : AArch64MachineState) : AArch64RunOutcome Event :=
  let indexed := indexInstructions basePc instructions
  let rec loop (fuel : Nat) (state : AArch64MachineState) (eventsRev : List Event) :
      AArch64RunOutcome Event :=
    match fuel with
    | 0 => .fuelExhausted state eventsRev.reverse
    | fuel + 1 =>
      match instructionAtPcIndexed indexed state.pc with
      | none => .completed state eventsRev.reverse
      | some instr =>
        let stepped := AArch64Instruction.step instr state
        match interceptor.interceptCall stepped.pc stepped with
        | some (hooked, event) =>
          let eventsRev' := match event with | some emitted => emitted :: eventsRev | none => eventsRev
          if hooked.fault.isSome then .faulted hooked eventsRev'.reverse
          else if hooked.terminated then .completed hooked eventsRev'.reverse
          else loop fuel hooked eventsRev'
        | none =>
          if stepped.fault.isSome then .faulted stepped eventsRev.reverse
          else if stepped.terminated then .completed stepped eventsRev.reverse
          else loop fuel stepped eventsRev
  loop fuel initial []

def AArch64RunOutcome.isAdmissible : AArch64RunOutcome Event → Prop
  | .completed _ _ => True
  | .faulted _ _ | .fuelExhausted _ _ => False

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Invokes an AArch64 subroutine with arguments and returns the 64-bit return value in X0. -/
def callSubroutine (instructions : List AnyAArch64Instruction) (args : List UInt64) (fuel : Nat := 1000) (entryPc : UInt64 := 0x400000) : UInt64 :=
  let s0 := initMachineState entryPc args
  let finalState := runProgramWithLoops entryPc instructions fuel s0
  finalState.getReg64 .x0

end Gasm.Targets.AArch64

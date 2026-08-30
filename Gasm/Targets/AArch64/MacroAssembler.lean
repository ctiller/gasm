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

import Gasm.Targets.AArch64.Semantics
import Gasm.Proof.LocalExecution

namespace Gasm.Targets.AArch64.MacroAssembler

open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- A data-processing GPR, restricted to architectural X0--X30.  Register encoding 31 is
    deliberately absent: these instruction forms interpret it as XZR, while other machine-model
    contexts may interpret it as SP. -/
abbrev Gpr := Fin 31

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- One of the four 16-bit lanes of a 64-bit MOV-wide instruction. -/
abbrev MovWideLane := Fin 4

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def MovWideLane.encoding (lane : MovWideLane) : UInt8 := lane.val.toUInt8

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem getReg64_reg64OfFin31 (state : AArch64MachineState) (register : Gpr) :
    state.getReg64 (reg64OfFin31 register) = state.getGpr64 register := by
  match register with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl
  | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl | ⟨15, _⟩ => rfl
  | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl
  | ⟨24, _⟩ => rfl | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨28, _⟩ => rfl | ⟨29, _⟩ => rfl | ⟨30, _⟩ => rfl
  | ⟨n + 31, h⟩ => omega

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem setReg64_reg64OfFin31 (state : AArch64MachineState) (register : Gpr)
    (value : UInt64) :
    state.setReg64 (reg64OfFin31 register) value = state.setGpr64 register value := by
  match register with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl
  | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl | ⟨15, _⟩ => rfl
  | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl
  | ⟨24, _⟩ => rfl | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨28, _⟩ => rfl | ⟨29, _⟩ => rfl | ⟨30, _⟩ => rfl
  | ⟨n + 31, h⟩ => omega

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- The closed, nominal set of 64-bit ordinary instruction forms admitted by this frontend.
    Shifted-register forms are fixed to `LSL #0`; flag-setting and logical inversion are absent by
    construction. Extending this type is a target-side proof obligation. -/
inductive Instruction where
  | movReg (dst src : Gpr)
  | movz (dst : Gpr) (imm : UInt16) (lane : MovWideLane)
  | movk (dst : Gpr) (imm : UInt16) (lane : MovWideLane)
  | add (dst lhs rhs : Gpr)
  | sub (dst lhs rhs : Gpr)
  | bitAnd (dst lhs rhs : Gpr)

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private def andReg64 (dst lhs rhs : Gpr) : AndReg where
  is64 := true
  setFlags := false
  rd := reg64OfFin31 dst
  rn := reg64OfFin31 lhs
  rm := reg64OfFin31 rhs
  shift := .LSL
  amount := 0
  invert := false

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- Lower one admitted nominal form to the existing open target instruction type. -/
def Instruction.emit : Instruction → AnyAArch64Instruction
  | .movReg dst src => .mk (movReg64 (reg64OfFin31 dst) (reg64OfFin31 src))
  | .movz dst imm lane => .mk (movz64 (reg64OfFin31 dst) imm lane.encoding)
  | .movk dst imm lane => .mk (movk64 (reg64OfFin31 dst) imm lane.encoding)
  | .add dst lhs rhs => .mk (addReg64 (reg64OfFin31 dst) (reg64OfFin31 lhs)
      (reg64OfFin31 rhs) .LSL 0)
  | .sub dst lhs rhs => .mk (subReg64 (reg64OfFin31 dst) (reg64OfFin31 lhs)
      (reg64OfFin31 rhs) .LSL 0)
  | .bitAnd dst lhs rhs => .mk (andReg64 dst lhs rhs)

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- Direct constructor-local semantics for the admitted form. This deliberately does not invoke
    the platform's open-instruction wrapper or host interception. -/
def Instruction.step : Instruction → AArch64MachineState → AArch64MachineState
  | .movReg dst src =>
      AArch64Instruction.step (movReg64 (reg64OfFin31 dst) (reg64OfFin31 src))
  | .movz dst imm lane =>
      AArch64Instruction.step (movz64 (reg64OfFin31 dst) imm lane.encoding)
  | .movk dst imm lane =>
      AArch64Instruction.step (movk64 (reg64OfFin31 dst) imm lane.encoding)
  | .add dst lhs rhs =>
      AArch64Instruction.step (addReg64 (reg64OfFin31 dst) (reg64OfFin31 lhs)
        (reg64OfFin31 rhs) .LSL 0)
  | .sub dst lhs rhs =>
      AArch64Instruction.step (subReg64 (reg64OfFin31 dst) (reg64OfFin31 lhs)
        (reg64OfFin31 rhs) .LSL 0)
  | .bitAnd dst lhs rhs => AArch64Instruction.step (andReg64 dst lhs rhs)

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- Target-owned constructor classification of the emitted straight-line forms. This classification
    cannot be established by observing a coincidental `pc + 4` result. -/
inductive ControlFlowFree : AnyAArch64Instruction → Prop where
  | movReg (dst src : Gpr) : ControlFlowFree (Instruction.movReg dst src).emit
  | movz (dst : Gpr) (imm : UInt16) (lane : MovWideLane) :
      ControlFlowFree (Instruction.movz dst imm lane).emit
  | movk (dst : Gpr) (imm : UInt16) (lane : MovWideLane) :
      ControlFlowFree (Instruction.movk dst imm lane).emit
  | add (dst lhs rhs : Gpr) : ControlFlowFree (Instruction.add dst lhs rhs).emit
  | sub (dst lhs rhs : Gpr) : ControlFlowFree (Instruction.sub dst lhs rhs).emit
  | bitAnd (dst lhs rhs : Gpr) : ControlFlowFree (Instruction.bitAnd dst lhs rhs).emit

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Instruction.controlFlowFree (i : Instruction) : ControlFlowFree i.emit := by
  cases i <;> constructor

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def Instruction.clobberedGprs : Instruction → List Gpr
  | .movReg dst _ | .movz dst _ _ | .movk dst _ _
  | .add dst _ _ | .sub dst _ _ | .bitAnd dst _ _ => [dst]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_pc (instruction : Instruction) (state : AArch64MachineState) :
    (instruction.step state).pc = state.pc + 4 := by
  cases instruction <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_memory (instruction : Instruction) (state : AArch64MachineState) :
    (instruction.step state).memory = state.memory := by
  cases instruction <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_sp (instruction : Instruction) (state : AArch64MachineState) :
    (instruction.step state).sp = state.sp := by
  cases instruction <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_nzcv (instruction : Instruction) (state : AArch64MachineState) :
    (instruction.step state).nzcv = state.nzcv := by
  cases instruction <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_fault (instruction : Instruction) (state : AArch64MachineState) :
    (instruction.step state).fault = state.fault := by
  cases instruction <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_terminated (instruction : Instruction) (state : AArch64MachineState) :
    (instruction.step state).terminated = state.terminated := by
  cases instruction <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private theorem step_gpr (instruction : Instruction) (state : AArch64MachineState)
    (register : Gpr) (notClobbered : register ∉ instruction.clobberedGprs) :
    (instruction.step state).gprs register = state.gprs register := by
  cases instruction <;>
    simp only [Instruction.clobberedGprs, List.mem_singleton] at notClobbered <;>
    simp [Instruction.step, AArch64Instruction.step, movReg64, movz64, movk64,
      addReg64, subReg64, andReg64, getReg64_reg64OfFin31,
      setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
      AArch64MachineState.advancePc, notClobbered]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- Fold the selected target instruction steps in list order. This is local instruction evidence
    only. It does not perform fetch/lookup, stop on faults, consume fuel, invoke host interceptors,
    establish termination/admissibility, or connect code to an artifact. -/
def runLocalSteps : List Instruction → AArch64MachineState → AArch64MachineState
  | [], state => state
  | instruction :: rest, state =>
      runLocalSteps rest (instruction.step state)

private theorem runLocalSteps_eq_generic (code : List Instruction) (state : AArch64MachineState) :
    runLocalSteps code state =
      Gasm.Proof.LocalExecution.runSteps Instruction.step code state := by
  induction code generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      change runLocalSteps rest (instruction.step state) =
        Gasm.Proof.LocalExecution.runSteps Instruction.step rest (instruction.step state)
      exact ih _

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def localCodeSize : List Instruction → UInt64
  | [] => 0
  | _ :: rest => 4 + localCodeSize rest

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_append (xs ys : List Instruction) (state : AArch64MachineState) :
    runLocalSteps (xs ++ ys) state = runLocalSteps ys (runLocalSteps xs state) := by
  simpa only [runLocalSteps_eq_generic] using
    Gasm.Proof.LocalExecution.runSteps_append Instruction.step xs ys state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_pc (code : List Instruction) (state : AArch64MachineState) :
    (runLocalSteps code state).pc = state.pc + localCodeSize code := by
  induction code generalizing state with
  | nil => simp [runLocalSteps, localCodeSize]
  | cons instruction rest ih =>
      rw [runLocalSteps, ih, step_pc]
      simp [localCodeSize, UInt64.add_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_preservesMemory (code : List Instruction) (state : AArch64MachineState) :
    (runLocalSteps code state).memory = state.memory := by
  rw [runLocalSteps_eq_generic]
  exact Gasm.Proof.LocalExecution.runSteps_preserves Instruction.step (·.memory)
    step_memory code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_preservesSp (code : List Instruction) (state : AArch64MachineState) :
    (runLocalSteps code state).sp = state.sp := by
  rw [runLocalSteps_eq_generic]
  exact Gasm.Proof.LocalExecution.runSteps_preserves Instruction.step (·.sp)
    step_sp code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_preservesNzcv (code : List Instruction) (state : AArch64MachineState) :
    (runLocalSteps code state).nzcv = state.nzcv := by
  rw [runLocalSteps_eq_generic]
  exact Gasm.Proof.LocalExecution.runSteps_preserves Instruction.step (·.nzcv)
    step_nzcv code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_preservesFault (code : List Instruction) (state : AArch64MachineState) :
    (runLocalSteps code state).fault = state.fault := by
  rw [runLocalSteps_eq_generic]
  exact Gasm.Proof.LocalExecution.runSteps_preserves Instruction.step (·.fault)
    step_fault code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_preservesTerminated (code : List Instruction)
    (state : AArch64MachineState) :
    (runLocalSteps code state).terminated = state.terminated := by
  rw [runLocalSteps_eq_generic]
  exact Gasm.Proof.LocalExecution.runSteps_preserves Instruction.step (·.terminated)
    step_terminated code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem runLocalSteps_preservesGpr (code : List Instruction) (state : AArch64MachineState)
    (register : Gpr) (notClobbered : register ∉ code.flatMap Instruction.clobberedGprs) :
    (runLocalSteps code state).gprs register = state.gprs register := by
  rw [runLocalSteps_eq_generic]
  exact Gasm.Proof.LocalExecution.runSteps_preservesOutside Instruction.step
    Instruction.clobberedGprs (fun machine gpr => machine.gprs gpr) step_gpr
    code state register notClobbered

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- Structural serialization of selected instructions. There is no independent byte field which
    could drift from the instruction list. -/
def serialize : List Instruction → ByteArray
  | [] => ByteArray.empty
  | instruction :: rest =>
      AArch64Instruction.encode instruction.emit ++ serialize rest

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def serializeEmitted : List AnyAArch64Instruction → ByteArray
  | [] => ByteArray.empty
  | instruction :: rest => AArch64Instruction.encode instruction ++ serializeEmitted rest

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem serialize_eq_serializeEmitted (code : List Instruction) :
    serialize code = serializeEmitted (code.map Instruction.emit) := by
  induction code with
  | nil => rfl
  | cons instruction rest ih => simp [serialize, serializeEmitted, ih]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] theorem serialize_cons (instruction : Instruction) (rest : List Instruction) :
    serialize (instruction :: rest) =
      AArch64Instruction.encode instruction.emit ++ serialize rest := rfl

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] theorem serialize_nil : serialize [] = ByteArray.empty := rfl

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem serialize_append (xs ys : List Instruction) :
    serialize (xs ++ ys) = serialize xs ++ serialize ys := by
  induction xs with
  | nil => rfl
  | cons instruction rest ih => simp [serialize, ih, ByteArray.append_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
structure Segment where
  name : String
  code : List Instruction

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def Segment.instructions (segment : Segment) : List AnyAArch64Instruction :=
  segment.code.map Instruction.emit

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def Segment.codeBytes (segment : Segment) : ByteArray := serialize segment.code

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.codeBytes_exact (segment : Segment) :
    segment.codeBytes = serializeEmitted segment.instructions := by
  exact serialize_eq_serializeEmitted segment.code

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def Segment.clobberedGprs (segment : Segment) : List Gpr :=
  segment.code.flatMap Instruction.clobberedGprs

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def Segment.then (first second : Segment) : Segment where
  name := first.name ++ "; " ++ second.name
  code := first.code ++ second.code

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] theorem Segment.codeBytes_then (first second : Segment) :
    (first.then second).codeBytes = first.codeBytes ++ second.codeBytes := by
  simp [Segment.then, Segment.codeBytes, serialize_append]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] theorem Segment.clobberedGprs_then (first second : Segment) :
    (first.then second).clobberedGprs = first.clobberedGprs ++ second.clobberedGprs := by
  simp [Segment.then, Segment.clobberedGprs]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] theorem Segment.instructions_then (first second : Segment) :
    (first.then second).instructions = first.instructions ++ second.instructions := by
  simp [Segment.then, Segment.instructions]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.controlFlowFree (segment : Segment) (instruction : AnyAArch64Instruction)
    (member : instruction ∈ segment.instructions) : ControlFlowFree instruction := by
  simp only [Segment.instructions, List.mem_map] at member
  obtain ⟨selected, _, rfl⟩ := member
  exact selected.controlFlowFree

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.pcAdvance (segment : Segment) (state : AArch64MachineState) :
    (runLocalSteps segment.code state).pc = state.pc + localCodeSize segment.code :=
  runLocalSteps_pc segment.code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.preservesMemory (segment : Segment) (state : AArch64MachineState) :
    (runLocalSteps segment.code state).memory = state.memory :=
  runLocalSteps_preservesMemory segment.code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.preservesSp (segment : Segment) (state : AArch64MachineState) :
    (runLocalSteps segment.code state).sp = state.sp :=
  runLocalSteps_preservesSp segment.code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.preservesNzcv (segment : Segment) (state : AArch64MachineState) :
    (runLocalSteps segment.code state).nzcv = state.nzcv :=
  runLocalSteps_preservesNzcv segment.code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.preservesFault (segment : Segment) (state : AArch64MachineState) :
    (runLocalSteps segment.code state).fault = state.fault :=
  runLocalSteps_preservesFault segment.code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.preservesTerminated (segment : Segment) (state : AArch64MachineState) :
    (runLocalSteps segment.code state).terminated = state.terminated :=
  runLocalSteps_preservesTerminated segment.code state

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem Segment.preservesGpr (segment : Segment) (state : AArch64MachineState)
    (register : Gpr) (notClobbered : register ∉ segment.clobberedGprs) :
    (runLocalSteps segment.code state).gprs register = state.gprs register :=
  runLocalSteps_preservesGpr segment.code state register notClobbered

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def mov (dst src : Gpr) : Segment := { name := "mov", code := [.movReg dst src] }

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def movz (dst : Gpr) (imm : UInt16) (lane : MovWideLane) : Segment :=
  { name := "movz", code := [.movz dst imm lane] }

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def movk (dst : Gpr) (imm : UInt16) (lane : MovWideLane) : Segment :=
  { name := "movk", code := [.movk dst imm lane] }

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def add (dst lhs rhs : Gpr) : Segment := { name := "add", code := [.add dst lhs rhs] }

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def sub (dst lhs rhs : Gpr) : Segment := { name := "sub", code := [.sub dst lhs rhs] }

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
def and (dst lhs rhs : Gpr) : Segment := { name := "and", code := [.bitAnd dst lhs rhs] }

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem mov_result (dst src : Gpr) (state : AArch64MachineState) :
    (runLocalSteps (mov dst src).code state).gprs dst = state.gprs src := by
  simp [mov, runLocalSteps, Instruction.step, AArch64Instruction.step, movReg64,
    getReg64_reg64OfFin31, setReg64_reg64OfFin31,
    AArch64MachineState.getGpr64, AArch64MachineState.setGpr64,
    AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem movz_result (dst : Gpr) (imm : UInt16) (lane : MovWideLane)
    (state : AArch64MachineState) :
    (runLocalSteps (movz dst imm lane).code state).gprs dst =
      imm.toUInt64 <<< ((lane.encoding.toUInt64 &&& 3) * 16) := by
  simp [movz, runLocalSteps, Instruction.step, AArch64Instruction.step, movz64,
    setReg64_reg64OfFin31, AArch64MachineState.setGpr64,
    AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem movk_result (dst : Gpr) (imm : UInt16) (lane : MovWideLane)
    (state : AArch64MachineState) :
    (runLocalSteps (movk dst imm lane).code state).gprs dst =
      (state.gprs dst &&& ~~~((0xFFFF : UInt64) <<<
        ((lane.encoding.toUInt64 &&& 3) * 16))) |||
      (imm.toUInt64 <<< ((lane.encoding.toUInt64 &&& 3) * 16)) := by
  simp [movk, runLocalSteps, Instruction.step, AArch64Instruction.step, movk64,
    getReg64_reg64OfFin31, setReg64_reg64OfFin31,
    AArch64MachineState.getGpr64, AArch64MachineState.setGpr64,
    AArch64MachineState.advancePc]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem add_result (dst lhs rhs : Gpr) (state : AArch64MachineState) :
    (runLocalSteps (add dst lhs rhs).code state).gprs dst =
      state.gprs lhs + state.gprs rhs := by
  simp [add, runLocalSteps, Instruction.step, AArch64Instruction.step, addReg64,
    getReg64_reg64OfFin31, setReg64_reg64OfFin31,
    AArch64MachineState.getGpr64, AArch64MachineState.setGpr64,
    AArch64MachineState.advancePc, ShiftType.apply]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem sub_result (dst lhs rhs : Gpr) (state : AArch64MachineState) :
    (runLocalSteps (sub dst lhs rhs).code state).gprs dst =
      state.gprs lhs - state.gprs rhs := by
  simp [sub, runLocalSteps, Instruction.step, AArch64Instruction.step, subReg64,
    getReg64_reg64OfFin31, setReg64_reg64OfFin31,
    AArch64MachineState.getGpr64, AArch64MachineState.setGpr64,
    AArch64MachineState.advancePc, ShiftType.apply]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
theorem and_result (dst lhs rhs : Gpr) (state : AArch64MachineState) :
    (runLocalSteps (and dst lhs rhs).code state).gprs dst =
      state.gprs lhs &&& state.gprs rhs := by
  simp [and, runLocalSteps, Instruction.step, AArch64Instruction.step, andReg64,
    getReg64_reg64OfFin31, setReg64_reg64OfFin31,
    AArch64MachineState.getGpr64, AArch64MachineState.setGpr64,
    AArch64MachineState.advancePc, ShiftType.apply]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private def lane0 : MovWideLane := ⟨0, by decide⟩
/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private def lane1 : MovWideLane := ⟨1, by decide⟩
/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private def lane2 : MovWideLane := ⟨2, by decide⟩
/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
private def lane3 : MovWideLane := ⟨3, by decide⟩

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] private theorem lane0_encoding : lane0.encoding = 0 := rfl
/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] private theorem lane1_encoding : lane1.encoding = 1 := rfl
/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] private theorem lane2_encoding : lane2.encoding = 2 := rfl
/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] private theorem lane3_encoding : lane3.encoding = 3 := rfl

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
/-- Total, deliberately unoptimized 64-bit constant materialization: zero the low lane, then keep
    and replace lanes 1--3. Omitting zero lanes is reserved for a later differential certificate. -/
def loadImm (dst : Gpr) (value : UInt64) : Segment where
  name := "movz; movk; movk; movk"
  code := [
    .movz dst value.toUInt16 lane0,
    .movk dst (value >>> 16).toUInt16 lane1,
    .movk dst (value >>> 32).toUInt16 lane2,
    .movk dst (value >>> 48).toUInt16 lane3
  ]

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-macro-segments -/
@[simp] theorem loadImm_clobberedGprs (dst : Gpr) (value : UInt64) :
    (loadImm dst value).clobberedGprs = [dst, dst, dst, dst] := rfl

end Gasm.Targets.AArch64.MacroAssembler

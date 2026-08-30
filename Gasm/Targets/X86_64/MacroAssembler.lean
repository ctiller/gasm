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

import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Proof.LocalExecution

namespace Gasm.Targets.X86_64.MacroAssembler

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
/-- Fold concrete instruction-step functions in list order. This is local instruction evidence only:
    it does not model fetch, fault stopping, fuel, or termination and cannot by itself discharge a
    platform execution/admissibility premise. -/
def runLocalSteps : List X86_64Instr → X86_64MachineState → X86_64MachineState
  | [], s => s
  | i :: rest, s => runLocalSteps rest (X86_64Instruction.step i s)

private theorem runLocalSteps_eq_generic (code : List X86_64Instr) (s : X86_64MachineState) :
    runLocalSteps code s =
      Gasm.Proof.LocalExecution.runSteps X86_64Instruction.step code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
      change runLocalSteps rest (X86_64Instruction.step i s) =
        Gasm.Proof.LocalExecution.runSteps X86_64Instruction.step rest
          (X86_64Instruction.step i s)
      exact ih _

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
theorem runLocalSteps_append (xs ys : List X86_64Instr) (s : X86_64MachineState) :
    runLocalSteps (xs ++ ys) s = runLocalSteps ys (runLocalSteps xs s) := by
  simpa only [runLocalSteps_eq_generic] using
    Gasm.Proof.LocalExecution.runSteps_append X86_64Instruction.step xs ys s

/- REF: docs/MACRO_ASSEMBLER.md#explicit-footprints -/
/-- What a contract promises about a non-register part of machine state. `unspecified` means
    clients must not rely on that component after the segment. -/
inductive FieldEffect where
  | preserved
  | unspecified
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
/-- A Hoare-style contract and an explicit machine-state footprint for a reusable fragment. -/
structure Contract where
  requires : X86_64MachineState → Prop := fun _ => True
  ensures : X86_64MachineState → X86_64MachineState → Prop
  clobberedGprs : List Reg64
  flags : FieldEffect
  memory : FieldEffect
  rip : FieldEffect

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
/-- Target-owned classification of instruction forms admitted to straight-line macro segments.
    This is constructor-derived, so a CALL/JMP cannot become ordinary merely because its dynamic
    target happens to equal fallthrough. New forms require an explicit target-side constructor. -/
inductive ControlFlowFree : X86_64Instr → Prop where
  | mov (dst src : Reg64) : ControlFlowFree (mov_r64 dst src)
  | loadImm (dst : Reg64) (value : UInt64) : ControlFlowFree (mov_r64_imm64 dst value)
  | add (dst src : Reg64) : ControlFlowFree (add_r64 dst src)
  | sub (dst src : Reg64) : ControlFlowFree (sub_r64 dst src)
  | bitAnd (dst src : Reg64) : ControlFlowFree (and_r64 dst src)

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
/-- Constructor-closed target classification of instruction families that never encode control
    transfer. State-conditionally faulting families remain admitted here; their safety is a
    separate block-invariant obligation. -/
inductive NonControlFlowEncoding : X86_64Instr → Prop where
  | mov (dst src : Reg64) : NonControlFlowEncoding (mov_r64 dst src)
  | loadImm (dst : Reg64) (value : UInt64) : NonControlFlowEncoding (mov_r64_imm64 dst value)
  | mov32 (dst : Reg32) (value : UInt32) : NonControlFlowEncoding (mov_r32 dst value)
  | movRspByte (disp value : UInt8) : NonControlFlowEncoding (mov_rsp_byte disp value)
  | movRsp64 (disp : UInt8) (value : UInt32) : NonControlFlowEncoding (mov_rsp64 disp value)
  | movMem8 (dst src : Reg64) : NonControlFlowEncoding (mov_mem8 dst src)
  | add (dst src : Reg64) : NonControlFlowEncoding (add_r64 dst src)
  | addImm8 (dst : Reg64) (value : UInt8) : NonControlFlowEncoding (add_r64_imm8 dst value)
  | addImm32 (dst : Reg64) (value : UInt32) : NonControlFlowEncoding (add_r64_imm32 dst value)
  | sub (dst src : Reg64) : NonControlFlowEncoding (sub_r64 dst src)
  | subImm8 (dst : Reg64) (value : UInt8) : NonControlFlowEncoding (sub_r64_imm8 dst value)
  /-- The compact ABI stack-frame subtraction is an ordinary fallthrough instruction. -/
  | subRsp8 (value : UInt8) : NonControlFlowEncoding (sub_rsp value)
  | subRsp32 (value : UInt32) : NonControlFlowEncoding (sub_rsp32 value)
  | bitAnd (dst src : Reg64) : NonControlFlowEncoding (and_r64 dst src)
  | bitAndImm8 (dst : Reg64) (value : UInt8) : NonControlFlowEncoding (and_r64_imm8 dst value)
  | xor32 (dst src : Reg32) : NonControlFlowEncoding (xor_r32 dst src)
  | compare (left right : Reg64) : NonControlFlowEncoding (cmp_r64 left right)
  | compareImm8 (dst : Reg64) (value : UInt8) : NonControlFlowEncoding (cmp_r64_imm8 dst value)
  /-- The full-width Linux errno-range comparison is an ordinary instruction.  This admits only
      the selected `CMP r64, imm32` form; it does not classify a following branch. -/
  | compareImm32 (dst : Reg64) (value : UInt32) : NonControlFlowEncoding (cmp_r64_imm32 dst value)
  | leaRsp (dst : Reg64) (disp : UInt8) : NonControlFlowEncoding (lea_rsp dst disp)
  | movMem64Disp (base : Reg64) (disp : UInt8) (src : Reg64) :
      NonControlFlowEncoding (mov_mem64_disp base disp src)
  | movMem64DispImm (base : Reg64) (disp : UInt8) (value : UInt32) :
      NonControlFlowEncoding (mov_mem64_disp_imm base disp value)
  | movReg64Mem64Disp (dst base : Reg64) (disp : UInt8) :
      NonControlFlowEncoding (mov_reg64_mem64_disp dst base disp)
  | push (src : Reg64) : NonControlFlowEncoding (push_r64 src)
  | pop (dst : Reg64) : NonControlFlowEncoding (pop_r64 dst)
  | div (divisor : Reg64) : NonControlFlowEncoding (div_r64 divisor)

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
/-- Exact target-semantic evidence that a constructor-classified non-control instruction has
    ordinary fallthrough whenever its concrete step is safe. -/
structure SequentialInstruction (instruction : X86_64Instr) : Prop where
  encoding : NonControlFlowEncoding instruction
  safeFallthrough : ∀ state : X86_64MachineState,
    (X86_64Instruction.step instruction state).fault = none →
      (X86_64Instruction.step instruction state).rip =
        state.rip + (X86_64Instruction.encode instruction).size.toUInt64

/- REF: docs/MACRO_ASSEMBLER.md#execution-and-contracts -/
/-- A reusable instruction fragment whose contract is proved against the concrete x86 semantics. -/
structure Segment where
  name : String
  code : List X86_64Instr
  contract : Contract
  localSound : ∀ s, contract.requires s → contract.ensures s (runLocalSteps code s)
  preservesGpr : ∀ s r, r ∉ contract.clobberedGprs →
    (runLocalSteps code s).gprs r = s.gprs r
  preservesMemory : contract.memory = .preserved → ∀ s,
    (runLocalSteps code s).memory = s.memory
  preservesFlags : contract.flags = .preserved → ∀ s,
    (runLocalSteps code s).flags = s.flags
  preservesRip : contract.rip = .preserved → ∀ s,
    (runLocalSteps code s).rip = s.rip
  controlFlowFree : ∀ i ∈ code, ControlFlowFree i

/- REF: docs/MACRO_ASSEMBLER.md#composition -/
/-- Sequential composition. Its postcondition exposes the intermediate state, so facts proved by
    the left fragment are available when proving facts about the right fragment. -/
def Segment.then (first second : Segment) : Segment where
  name := first.name ++ "; " ++ second.name
  code := first.code ++ second.code
  contract := {
    requires := fun s => first.contract.requires s ∧
      ∀ mid, first.contract.ensures s mid → second.contract.requires mid
    ensures := fun s out => ∃ mid,
      first.contract.ensures s mid ∧ second.contract.ensures mid out
    clobberedGprs := first.contract.clobberedGprs ++ second.contract.clobberedGprs
    flags := if second.contract.flags = .preserved then first.contract.flags else second.contract.flags
    memory := if first.contract.memory = .preserved ∧ second.contract.memory = .preserved then
      .preserved else .unspecified
    rip := .unspecified
  }
  localSound := by
    intro s h
    rw [runLocalSteps_append]
    exact ⟨runLocalSteps first.code s, first.localSound s h.1,
      second.localSound _ (h.2 _ (first.localSound s h.1))⟩
  preservesGpr := by
    intro s r h
    rw [runLocalSteps_append]
    exact Gasm.Proof.LocalExecution.preservesOutside_comp_append
      (runLocalSteps first.code) (runLocalSteps second.code) (fun state register => state.gprs register)
      first.contract.clobberedGprs second.contract.clobberedGprs first.preservesGpr
      second.preservesGpr s r h
  preservesMemory := by
    intro h s
    simp only at h
    split at h <;> try contradiction
    rename_i hp
    rw [runLocalSteps_append]
    exact Gasm.Proof.LocalExecution.preserves_comp
      (runLocalSteps first.code) (runLocalSteps second.code) (·.memory)
      (first.preservesMemory hp.1) (second.preservesMemory hp.2) s
  preservesFlags := by
    intro h s
    simp only at h
    split at h
    · rename_i hp
      rw [runLocalSteps_append]
      exact Gasm.Proof.LocalExecution.preserves_comp
        (runLocalSteps first.code) (runLocalSteps second.code) (·.flags)
        (first.preservesFlags h) (second.preservesFlags hp) s
    · contradiction
  preservesRip := by simp
  controlFlowFree := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact first.controlFlowFree i hi
    · exact second.controlFlowFree i hi

/- REF: docs/MACRO_ASSEMBLER.md#building-blocks -/
/-- Move one register to another. Flags and memory are proved preserved. -/
def mov (dst src : Reg64) : Segment where
  name := s!"mov {dst}, {src}"
  code := [mov_r64 dst src]
  contract := {
    ensures := fun before after => after.gprs dst = before.gprs src
    clobberedGprs := [dst]
    flags := .preserved
    memory := .preserved
    rip := .unspecified
  }
  localSound := by
    intro s _
    change (s.setGpr64 dst (s.gprs src)).gprs dst = s.gprs src
    simp [X86_64MachineState.setGpr64]
  preservesGpr := by
    intro s r h
    simp only [List.mem_singleton] at h
    change (s.setGpr64 dst (s.gprs src)).gprs r = s.gprs r
    simp [X86_64MachineState.setGpr64, h]
  preservesMemory := by
    intro _ s
    change (s.setGpr64 dst (s.gprs src)).memory = s.memory
    rfl
  preservesFlags := by
    intro _ s
    change (s.setGpr64 dst (s.gprs src)).flags = s.flags
    rfl
  preservesRip := by simp
  controlFlowFree := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .mov dst src

/- REF: docs/MACRO_ASSEMBLER.md#building-blocks -/
/-- Load a 64-bit constant. Flags and memory are proved preserved. -/
def loadImm (dst : Reg64) (value : UInt64) : Segment where
  name := s!"mov {dst}, {value}"
  code := [mov_r64_imm64 dst value]
  contract := {
    ensures := fun _ after => after.gprs dst = value
    clobberedGprs := [dst]
    flags := .preserved
    memory := .preserved
    rip := .unspecified
  }
  localSound := by
    intro s _
    change (s.setGpr64 dst value).gprs dst = value
    simp [X86_64MachineState.setGpr64]
  preservesGpr := by
    intro s r h
    simp only [List.mem_singleton] at h
    change (s.setGpr64 dst value).gprs r = s.gprs r
    simp [X86_64MachineState.setGpr64, h]
  preservesMemory := by
    intro _ s
    change (s.setGpr64 dst value).memory = s.memory
    rfl
  preservesFlags := by
    intro _ s
    change (s.setGpr64 dst value).flags = s.flags
    rfl
  preservesRip := by simp
  controlFlowFree := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .loadImm dst value

/- REF: docs/MACRO_ASSEMBLER.md#building-blocks -/
private def binary (name : String) (op : UInt64 → UInt64 → UInt64)
    (mk : Reg64 → Reg64 → X86_64Instr)
    (dst src : Reg64)
    (stepResult : ∀ s, (X86_64Instruction.step (mk dst src) s).gprs dst =
      op (s.gprs dst) (s.gprs src))
    (preserve : ∀ s r, r ≠ dst →
      (X86_64Instruction.step (mk dst src) s).gprs r = s.gprs r)
    (memoryPreserved : ∀ s,
      (X86_64Instruction.step (mk dst src) s).memory = s.memory)
    (flowFree : ControlFlowFree (mk dst src)) : Segment where
  name := name
  code := [mk dst src]
  contract := {
    ensures := fun before after => after.gprs dst = op (before.gprs dst) (before.gprs src)
    clobberedGprs := [dst]
    flags := .unspecified
    memory := .preserved
    rip := .unspecified
  }
  localSound := by intro s _; simpa [runLocalSteps] using stepResult s
  preservesGpr := by
    intro s r h
    simp only [runLocalSteps, List.mem_singleton] at h ⊢
    exact preserve s r h
  preservesMemory := by
    intro _ s
    simpa [runLocalSteps] using memoryPreserved s
  preservesFlags := by simp
  preservesRip := by simp
  controlFlowFree := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact flowFree

/- REF: docs/MACRO_ASSEMBLER.md#building-blocks -/
def add (dst src : Reg64) : Segment :=
  binary s!"add {dst}, {src}" (· + ·) add_r64 dst src
    (by
      intro s
      change ((s.setGpr64 dst (s.gprs dst + s.gprs src)).setFlagsAdd64
        (s.gprs dst) (s.gprs src)).gprs dst = _
      simp [X86_64MachineState.setFlagsAdd64, X86_64MachineState.setGpr64])
    (by
      intro s r h
      change ((s.setGpr64 dst (s.gprs dst + s.gprs src)).setFlagsAdd64
        (s.gprs dst) (s.gprs src)).gprs r = _
      simp [X86_64MachineState.setFlagsAdd64, X86_64MachineState.setGpr64, h])
    (by
      intro s
      change ((s.setGpr64 dst (s.gprs dst + s.gprs src)).setFlagsAdd64
        (s.gprs dst) (s.gprs src)).memory = _
      rfl)
    (.add dst src)

/- REF: docs/MACRO_ASSEMBLER.md#building-blocks -/
def sub (dst src : Reg64) : Segment :=
  binary s!"sub {dst}, {src}" (· - ·) sub_r64 dst src
    (by
      intro s
      change ((s.setGpr64 dst (s.gprs dst - s.gprs src)).setFlagsSub64
        (s.gprs dst) (s.gprs src)).gprs dst = _
      simp [X86_64MachineState.setFlagsSub64, X86_64MachineState.setFlagsCmp64,
        X86_64MachineState.setGpr64])
    (by
      intro s r h
      change ((s.setGpr64 dst (s.gprs dst - s.gprs src)).setFlagsSub64
        (s.gprs dst) (s.gprs src)).gprs r = _
      simp [X86_64MachineState.setFlagsSub64, X86_64MachineState.setFlagsCmp64,
        X86_64MachineState.setGpr64, h])
    (by
      intro s
      change ((s.setGpr64 dst (s.gprs dst - s.gprs src)).setFlagsSub64
        (s.gprs dst) (s.gprs src)).memory = _
      rfl)
    (.sub dst src)

/- REF: docs/MACRO_ASSEMBLER.md#building-blocks -/
def and (dst src : Reg64) : Segment :=
  binary s!"and {dst}, {src}" (· &&& ·) and_r64 dst src
    (by
      intro s
      change ((s.setGpr64 dst (s.gprs dst &&& s.gprs src)).setFlagsLogic64
        (s.gprs dst &&& s.gprs src)).gprs dst = _
      simp [X86_64MachineState.setFlagsLogic64, X86_64MachineState.setFlagsLogic,
        X86_64MachineState.setGpr64])
    (by
      intro s r h
      change ((s.setGpr64 dst (s.gprs dst &&& s.gprs src)).setFlagsLogic64
        (s.gprs dst &&& s.gprs src)).gprs r = _
      simp [X86_64MachineState.setFlagsLogic64, X86_64MachineState.setFlagsLogic,
        X86_64MachineState.setGpr64, h])
    (by
      intro s
      change ((s.setGpr64 dst (s.gprs dst &&& s.gprs src)).setFlagsLogic64
        (s.gprs dst &&& s.gprs src)).memory = _
      rfl)
    (.bitAnd dst src)

/- REF: docs/MACRO_ASSEMBLER.md#macro-programs -/
abbrev Program := List Segment

/- REF: docs/MACRO_ASSEMBLER.md#macro-programs -/
/-- Expand proved fragments to ordinary instructions. Hand-written instructions can still be
    inserted with a separately proved `Segment`. -/
def assemble (program : Program) : List X86_64Instr :=
  program.flatMap (·.code)

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
/-- Control-flow exclusion is derived from every selected segment's law, rather than recorded as
    disconnected metadata on each compiled program. -/
theorem assemble_controlFlowFree (program : Program) (i : X86_64Instr)
    (hi : i ∈ assemble program) : ControlFlowFree i := by
  induction program with
  | nil => simp [assemble] at hi
  | cons segment rest ih =>
    simp only [assemble, List.flatMap_cons, List.mem_append] at hi
    rcases hi with hi | hi
    · exact segment.controlFlowFree i hi
    · exact ih hi

end Gasm.Targets.X86_64.MacroAssembler

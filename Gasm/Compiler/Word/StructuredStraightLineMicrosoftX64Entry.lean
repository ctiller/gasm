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

import Gasm.Compiler.Word.StructuredStraightLine
import Gasm.Compiler.Word.MicrosoftX64
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge

namespace Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry

open Gasm.Compiler.Word
open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

/-- This backend is for a PE process entry body, not an ABI-callable function. Its selected
    temporary registers include Microsoft-x64 nonvolatile registers; the final entry proof must
    close or exclude fallthrough, return, unwind, callbacks/reentrancy, exception or fault
    continuation, teardown observers, and any caller continuation that could observe those
    clobbers. This module supplies none of that process-entry authority. -/

def resultRegister : Reg64 := .rax
def lhsScratch : Reg64 := .r10
def rhsScratch : Reg64 := .r11
def maxTemporaries : Nat := 7

/-- Stable creation-order allocation. Every selected register is nonvolatile under Microsoft x64;
    this fact is exposed, never hidden behind a callable-ABI claim. -/
def tempRegister : Fin maxTemporaries → Reg64
  | ⟨0, _⟩ => .rbx
  | ⟨1, _⟩ => .rsi
  | ⟨2, _⟩ => .rdi
  | ⟨3, _⟩ => .r12
  | ⟨4, _⟩ => .r13
  | ⟨5, _⟩ => .r14
  | ⟨6, _⟩ => .r15

def nonvolatileTempClobbers : List Reg64 :=
  [.rbx, .rsi, .rdi, .r12, .r13, .r14, .r15]

def allowedClobbers : List Reg64 :=
  [resultRegister, lhsScratch, rhsScratch] ++ nonvolatileTempClobbers

private theorem tempRegister_mem_nonvolatile (index : Fin maxTemporaries) :
    tempRegister index ∈ nonvolatileTempClobbers := by
  rcases index with ⟨index, bound⟩
  simp only [maxTemporaries] at bound
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tempRegister, nonvolatileTempClobbers]

private theorem tempRegister_notInput (index : Fin maxTemporaries) :
    tempRegister index ≠ .rcx ∧ tempRegister index ≠ .rdx ∧
      tempRegister index ≠ .r8 ∧ tempRegister index ≠ .r9 := by
  rcases index with ⟨index, bound⟩
  simp only [maxTemporaries] at bound
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tempRegister]

private theorem tempRegister_notScratch (index : Fin maxTemporaries) :
    tempRegister index ≠ lhsScratch ∧ tempRegister index ≠ rhsScratch := by
  rcases index with ⟨index, bound⟩
  simp only [maxTemporaries] at bound
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tempRegister, lhsScratch, rhsScratch]

namespace Allocation

def deBruijnIndex : TempRef temps value → Nat
  | .newest => 0
  | .older ref => deBruijnIndex ref + 1

theorem deBruijnIndex_lt (ref : TempRef temps value) :
    deBruijnIndex ref < temps.length := by
  induction ref with
  | newest => simp [deBruijnIndex]
  | older ref ih => simp only [deBruijnIndex, List.length_cons]; omega

def creationIndex (ref : TempRef temps value) : Nat :=
  temps.length - 1 - deBruijnIndex ref

theorem creationIndex_lt (ref : TempRef temps value) :
    creationIndex ref < temps.length := by
  have := deBruijnIndex_lt ref
  simp only [creationIndex]
  omega

@[simp] theorem creationIndex_older (newer : Args → UInt64)
    (ref : TempRef temps value) :
    creationIndex (temps := newer :: temps) (TempRef.older ref) = creationIndex ref := by
  simp only [creationIndex, deBruijnIndex, List.length_cons]
  have := deBruijnIndex_lt ref
  omega

end Allocation

def Fits (code : Code temps result) : Prop :=
  temps.length + code.instructionCount ≤ maxTemporaries

private def tempOfRef (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) : Reg64 :=
  tempRegister ⟨Allocation.creationIndex ref,
    Nat.lt_of_lt_of_le (Allocation.creationIndex_lt ref) fits⟩

def argsOfState (state : X86_64MachineState) : Args :=
  MicrosoftX64.argsOfState state

private def ArgsMatch (args : Args) (state : X86_64MachineState) : Prop :=
  argsOfState state = args

private def TempsSound {temps : List (Args → UInt64)}
    (fits : temps.length ≤ maxTemporaries) (args : Args)
    (state : X86_64MachineState) : Prop :=
  ∀ {value} (ref : TempRef temps value), state.gprs (tempOfRef fits ref) = value args

private def lowerOperand (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) : Operand temps value → Segment
  | .a0 => mov destination .rcx
  | .a1 => mov destination .rdx
  | .a2 => mov destination .r8
  | .a3 => mov destination .r9
  | .constant value => loadImm destination value
  | .temp ref => mov destination (tempOfRef fits ref)

private theorem lowerOperand_clobbers (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) (operand : Operand temps value) :
    (lowerOperand destination fits operand).contract.clobberedGprs = [destination] := by
  cases operand <;> rfl

private theorem lowerOperand_correct (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) (operand : Operand temps value)
    (args : Args) (state : X86_64MachineState) (argsMatch : ArgsMatch args state)
    (tempsSound : TempsSound fits args state) :
    (runLocalSteps (lowerOperand destination fits operand).code state).gprs destination =
      value args := by
  cases operand with
  | a0 =>
      exact ((mov destination .rcx).localSound state trivial).trans
        (congrArg Args.a0 argsMatch)
  | a1 =>
      exact ((mov destination .rdx).localSound state trivial).trans
        (congrArg Args.a1 argsMatch)
  | a2 =>
      exact ((mov destination .r8).localSound state trivial).trans
        (congrArg Args.a2 argsMatch)
  | a3 =>
      exact ((mov destination .r9).localSound state trivial).trans
        (congrArg Args.a3 argsMatch)
  | constant constant => exact (loadImm destination constant).localSound state trivial
  | temp ref =>
      exact ((mov destination (tempOfRef fits ref)).localSound state trivial).trans
        (tempsSound ref)

private theorem lowerOperand_preservesGpr (destination register : Reg64)
    (different : register ≠ destination) (fits : temps.length ≤ maxTemporaries)
    (operand : Operand temps value) (state : X86_64MachineState) :
    (runLocalSteps (lowerOperand destination fits operand).code state).gprs register =
      state.gprs register := by
  apply (lowerOperand destination fits operand).preservesGpr
  rw [lowerOperand_clobbers]
  simpa using different

private theorem lowerOperand_preservesArgs (destination : Reg64)
    (notInput : destination ≠ .rcx ∧ destination ≠ .rdx ∧
      destination ≠ .r8 ∧ destination ≠ .r9)
    (fits : temps.length ≤ maxTemporaries) (operand : Operand temps value)
    (args : Args) (state : X86_64MachineState) (argsMatch : ArgsMatch args state) :
    ArgsMatch args (runLocalSteps (lowerOperand destination fits operand).code state) := by
  apply Args.ext
  · change (runLocalSteps (lowerOperand destination fits operand).code state).gprs .rcx = args.a0
    rw [lowerOperand_preservesGpr destination .rcx (Ne.symm notInput.1)]
    exact congrArg Args.a0 argsMatch
  · change (runLocalSteps (lowerOperand destination fits operand).code state).gprs .rdx = args.a1
    rw [lowerOperand_preservesGpr destination .rdx (Ne.symm notInput.2.1)]
    exact congrArg Args.a1 argsMatch
  · change (runLocalSteps (lowerOperand destination fits operand).code state).gprs .r8 = args.a2
    rw [lowerOperand_preservesGpr destination .r8 (Ne.symm notInput.2.2.1)]
    exact congrArg Args.a2 argsMatch
  · change (runLocalSteps (lowerOperand destination fits operand).code state).gprs .r9 = args.a3
    rw [lowerOperand_preservesGpr destination .r9 (Ne.symm notInput.2.2.2)]
    exact congrArg Args.a3 argsMatch

private theorem lowerOperand_preservesTemps (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries)
    (different : ∀ {value} (ref : TempRef temps value), tempOfRef fits ref ≠ destination)
    (operand : Operand temps operandValue) (args : Args) (state : X86_64MachineState)
    (sound : TempsSound fits args state) :
    TempsSound fits args (runLocalSteps (lowerOperand destination fits operand).code state) := by
  intro value ref
  rw [lowerOperand_preservesGpr destination (tempOfRef fits ref) (different ref)]
  exact sound ref

private theorem tempOfRef_notScratch (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) :
    tempOfRef fits ref ≠ lhsScratch ∧ tempOfRef fits ref ≠ rhsScratch :=
  tempRegister_notScratch _

private theorem tempOfRef_notInput (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) :
    tempOfRef fits ref ≠ .rcx ∧ tempOfRef fits ref ≠ .rdx ∧
      tempOfRef fits ref ≠ .r8 ∧ tempOfRef fits ref ≠ .r9 :=
  tempRegister_notInput _

private def lowerInstruction (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) : Instruction temps value → Segment
  | .add lhs rhs =>
      (lowerOperand lhsScratch fits lhs).then
        ((lowerOperand rhsScratch fits rhs).then
          ((mov destination lhsScratch).then (add destination rhsScratch)))
  | .sub lhs rhs =>
      (lowerOperand lhsScratch fits lhs).then
        ((lowerOperand rhsScratch fits rhs).then
          ((mov destination lhsScratch).then (sub destination rhsScratch)))
  | .bitAnd lhs rhs =>
      (lowerOperand lhsScratch fits lhs).then
        ((lowerOperand rhsScratch fits rhs).then
          ((mov destination lhsScratch).then (MacroAssembler.and destination rhsScratch)))

private theorem lowerInstruction_correct (destination : Reg64)
    (notScratch : destination ≠ lhsScratch ∧ destination ≠ rhsScratch)
    (fits : temps.length ≤ maxTemporaries) (instruction : Instruction temps value)
    (args : Args) (state : X86_64MachineState) (argsMatch : ArgsMatch args state)
    (tempsSound : TempsSound fits args state) :
    (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs destination =
      value args := by
  cases instruction with
  | add lhs rhs =>
      let afterLhs := runLocalSteps (lowerOperand lhsScratch fits lhs).code state
      have argsAfterLhs : ArgsMatch args afterLhs :=
        lowerOperand_preservesArgs lhsScratch (by decide) fits lhs args state argsMatch
      have tempsAfterLhs : TempsSound fits args afterLhs :=
        lowerOperand_preservesTemps lhsScratch fits
          (fun ref => (tempOfRef_notScratch fits ref).1) lhs args state tempsSound
      have lhsValue := lowerOperand_correct lhsScratch fits lhs args state argsMatch tempsSound
      have rhsValue := lowerOperand_correct rhsScratch fits rhs args afterLhs argsAfterLhs
        tempsAfterLhs
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(add destination rhsScratch).localSound _ trivial]
      rw [(mov destination lhsScratch).localSound _ trivial]
      rw [(mov destination lhsScratch).preservesGpr _ rhsScratch (by
        change rhsScratch ∉ [destination]
        simpa using Ne.symm notScratch.2)]
      rw [rhsValue]
      rw [lowerOperand_preservesGpr rhsScratch lhsScratch (by decide)]
      rw [lhsValue]
  | sub lhs rhs =>
      let afterLhs := runLocalSteps (lowerOperand lhsScratch fits lhs).code state
      have argsAfterLhs : ArgsMatch args afterLhs :=
        lowerOperand_preservesArgs lhsScratch (by decide) fits lhs args state argsMatch
      have tempsAfterLhs : TempsSound fits args afterLhs :=
        lowerOperand_preservesTemps lhsScratch fits
          (fun ref => (tempOfRef_notScratch fits ref).1) lhs args state tempsSound
      have lhsValue := lowerOperand_correct lhsScratch fits lhs args state argsMatch tempsSound
      have rhsValue := lowerOperand_correct rhsScratch fits rhs args afterLhs argsAfterLhs
        tempsAfterLhs
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(sub destination rhsScratch).localSound _ trivial]
      rw [(mov destination lhsScratch).localSound _ trivial]
      rw [(mov destination lhsScratch).preservesGpr _ rhsScratch (by
        change rhsScratch ∉ [destination]
        simpa using Ne.symm notScratch.2)]
      rw [rhsValue]
      rw [lowerOperand_preservesGpr rhsScratch lhsScratch (by decide)]
      rw [lhsValue]
  | bitAnd lhs rhs =>
      let afterLhs := runLocalSteps (lowerOperand lhsScratch fits lhs).code state
      have argsAfterLhs : ArgsMatch args afterLhs :=
        lowerOperand_preservesArgs lhsScratch (by decide) fits lhs args state argsMatch
      have tempsAfterLhs : TempsSound fits args afterLhs :=
        lowerOperand_preservesTemps lhsScratch fits
          (fun ref => (tempOfRef_notScratch fits ref).1) lhs args state tempsSound
      have lhsValue := lowerOperand_correct lhsScratch fits lhs args state argsMatch tempsSound
      have rhsValue := lowerOperand_correct rhsScratch fits rhs args afterLhs argsAfterLhs
        tempsAfterLhs
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(MacroAssembler.and destination rhsScratch).localSound _ trivial]
      rw [(mov destination lhsScratch).localSound _ trivial]
      rw [(mov destination lhsScratch).preservesGpr _ rhsScratch (by
        change rhsScratch ∉ [destination]
        simpa using Ne.symm notScratch.2)]
      rw [rhsValue]
      rw [lowerOperand_preservesGpr rhsScratch lhsScratch (by decide)]
      rw [lhsValue]

private theorem lowerInstruction_preservesGpr (destination register : Reg64)
    (notDestination : register ≠ destination) (notLhs : register ≠ lhsScratch)
    (notRhs : register ≠ rhsScratch) (fits : temps.length ≤ maxTemporaries)
    (instruction : Instruction temps value) (state : X86_64MachineState) :
    (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs register =
      state.gprs register := by
  cases instruction with
  | add lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(add destination rhsScratch).preservesGpr _ register (by
        change register ∉ [destination]
        simpa using notDestination)]
      rw [(mov destination lhsScratch).preservesGpr _ register (by
        change register ∉ [destination]
        simpa using notDestination)]
      rw [lowerOperand_preservesGpr rhsScratch register notRhs]
      exact lowerOperand_preservesGpr lhsScratch register notLhs fits lhs state
  | sub lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(sub destination rhsScratch).preservesGpr _ register (by
        change register ∉ [destination]
        simpa using notDestination)]
      rw [(mov destination lhsScratch).preservesGpr _ register (by
        change register ∉ [destination]
        simpa using notDestination)]
      rw [lowerOperand_preservesGpr rhsScratch register notRhs]
      exact lowerOperand_preservesGpr lhsScratch register notLhs fits lhs state
  | bitAnd lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(MacroAssembler.and destination rhsScratch).preservesGpr _ register (by
        change register ∉ [destination]
        simpa using notDestination)]
      rw [(mov destination lhsScratch).preservesGpr _ register (by
        change register ∉ [destination]
        simpa using notDestination)]
      rw [lowerOperand_preservesGpr rhsScratch register notRhs]
      exact lowerOperand_preservesGpr lhsScratch register notLhs fits lhs state

private theorem lowerInstruction_preservesArgs (destination : Reg64)
    (notInput : destination ≠ .rcx ∧ destination ≠ .rdx ∧
      destination ≠ .r8 ∧ destination ≠ .r9)
    (fits : temps.length ≤ maxTemporaries) (instruction : Instruction temps value)
    (args : Args) (state : X86_64MachineState) (argsMatch : ArgsMatch args state) :
    ArgsMatch args (runLocalSteps (lowerInstruction destination fits instruction).code state) := by
  apply Args.ext
  · change (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs .rcx =
      args.a0
    rw [lowerInstruction_preservesGpr destination .rcx (Ne.symm notInput.1) (by decide)
      (by decide)]
    exact congrArg Args.a0 argsMatch
  · change (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs .rdx =
      args.a1
    rw [lowerInstruction_preservesGpr destination .rdx (Ne.symm notInput.2.1) (by decide)
      (by decide)]
    exact congrArg Args.a1 argsMatch
  · change (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs .r8 =
      args.a2
    rw [lowerInstruction_preservesGpr destination .r8 (Ne.symm notInput.2.2.1) (by decide)
      (by decide)]
    exact congrArg Args.a2 argsMatch
  · change (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs .r9 =
      args.a3
    rw [lowerInstruction_preservesGpr destination .r9 (Ne.symm notInput.2.2.2) (by decide)
      (by decide)]
    exact congrArg Args.a3 argsMatch

private def nextTempRegister {temps : List (Args → UInt64)}
    (available : temps.length < maxTemporaries) : Reg64 :=
  tempRegister ⟨temps.length, available⟩

private theorem tempRegister_injective : Function.Injective tempRegister := by
  intro left right equal
  rcases left with ⟨left, leftBound⟩
  rcases right with ⟨right, rightBound⟩
  simp only [maxTemporaries] at leftBound rightBound
  have leftCases : left = 0 ∨ left = 1 ∨ left = 2 ∨ left = 3 ∨
      left = 4 ∨ left = 5 ∨ left = 6 := by omega
  have rightCases : right = 0 ∨ right = 1 ∨ right = 2 ∨ right = 3 ∨
      right = 4 ∨ right = 5 ∨ right = 6 := by omega
  rcases leftCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases rightCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [tempRegister] at equal ⊢

private theorem nextTempRegister_notInput (available : temps.length < maxTemporaries) :
    nextTempRegister (temps := temps) available ≠ .rcx ∧
      nextTempRegister (temps := temps) available ≠ .rdx ∧
      nextTempRegister (temps := temps) available ≠ .r8 ∧
      nextTempRegister (temps := temps) available ≠ .r9 :=
  tempRegister_notInput _

private theorem nextTempRegister_notScratch (available : temps.length < maxTemporaries) :
    nextTempRegister (temps := temps) available ≠ lhsScratch ∧
      nextTempRegister (temps := temps) available ≠ rhsScratch :=
  tempRegister_notScratch _

private theorem tempOfRef_ne_next (fits : temps.length ≤ maxTemporaries)
    (available : temps.length < maxTemporaries) (ref : TempRef temps value) :
    tempOfRef fits ref ≠ nextTempRegister available := by
  intro equal
  have indexEqual : Allocation.creationIndex ref = temps.length := by
    exact congrArg Fin.val (tempRegister_injective equal)
  exact (Nat.ne_of_lt (Allocation.creationIndex_lt ref)) indexEqual

private theorem tempOfRef_newest (restFits : (value :: temps).length ≤ maxTemporaries)
    (available : temps.length < maxTemporaries) :
    tempOfRef restFits (TempRef.newest : TempRef (value :: temps) value) =
      nextTempRegister available := by
  simp [tempOfRef, nextTempRegister, Allocation.creationIndex, Allocation.deBruijnIndex]

private theorem tempOfRef_older (fits : temps.length ≤ maxTemporaries)
    (restFits : (newer :: temps).length ≤ maxTemporaries) (ref : TempRef temps value) :
    tempOfRef restFits (TempRef.older ref) = tempOfRef fits ref := by
  simp [tempOfRef, Allocation.creationIndex_older]

private theorem TempsSound.afterInstruction (fits : temps.length ≤ maxTemporaries)
    (restFits : (newValue :: temps).length ≤ maxTemporaries)
    (available : temps.length < maxTemporaries) (instruction : Instruction temps newValue)
    (args : Args) (state : X86_64MachineState) (argsMatch : ArgsMatch args state)
    (sound : TempsSound fits args state) :
    TempsSound restFits args
      (runLocalSteps (lowerInstruction (nextTempRegister available) fits instruction).code state) := by
  intro value ref
  cases ref with
  | newest =>
      rw [tempOfRef_newest restFits available]
      exact lowerInstruction_correct (nextTempRegister available)
        (nextTempRegister_notScratch available) fits instruction args state argsMatch sound
  | older ref =>
      rw [tempOfRef_older fits restFits ref]
      rw [lowerInstruction_preservesGpr (nextTempRegister available) (tempOfRef fits ref)
        (tempOfRef_ne_next fits available ref)
        (tempOfRef_notScratch fits ref).1 (tempOfRef_notScratch fits ref).2]
      exact sound ref
private def resultSegment (fits : temps.length ≤ maxTemporaries)
    (result : Operand temps value) : Segment :=
  lowerOperand resultRegister fits result

def lowerSegments (code : Code temps result) (fits : Fits code) : List Segment :=
  match code with
  | .done operand => [resultSegment (by
      simp only [Fits, Code.instructionCount, Nat.add_zero] at fits
      exact fits) operand]
  | .emit instruction rest =>
      let currentFits : temps.length ≤ maxTemporaries := by
        simp only [Fits, Code.instructionCount] at fits
        omega
      let destination := tempRegister ⟨temps.length, by
        simp only [Fits, Code.instructionCount] at fits
        omega⟩
      lowerInstruction destination currentFits instruction ::
        lowerSegments rest (by
          simp only [Fits, Code.instructionCount, List.length_cons] at fits ⊢
          omega)

def lowerInstructions (code : Code temps result) (fits : Fits code) : List X86_64Instr :=
  (lowerSegments code fits).flatMap Segment.code

def lowerBytes (code : Code temps result) (fits : Fits code) : ByteArray :=
  Gasm.Targets.X86_64.Assembler.serializeInstructions (lowerInstructions code fits)

private theorem lowerSegments_correct (code : Code temps result) (fits : Fits code)
    (args : Args) (state : X86_64MachineState) (argsMatch : ArgsMatch args state)
    (tempsSound : TempsSound (temps := temps) (by
      have total := fits
      simp only [Fits] at total
      omega) args state) :
    (runLocalSteps ((lowerSegments code fits).flatMap Segment.code) state).gprs resultRegister =
      result args := by
  induction code generalizing state args with
  | @done operandTemps operandValue operand =>
      simp only [lowerSegments, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        resultSegment, resultRegister]
      exact lowerOperand_correct .rax (by
        simp only [Fits, Code.instructionCount, Nat.add_zero] at fits
        exact fits) operand args state argsMatch tempsSound
  | @emit temps instructionValue result instruction rest ih =>
      have currentFits : temps.length ≤ maxTemporaries := by
        simp only [Fits, Code.instructionCount] at fits
        omega
      have available : temps.length < maxTemporaries := by
        simp only [Fits, Code.instructionCount] at fits
        omega
      have restFits : Fits rest := by
        simp only [Fits, Code.instructionCount, List.length_cons] at fits ⊢
        omega
      let destination := nextTempRegister available
      let after := runLocalSteps (lowerInstruction destination currentFits instruction).code state
      have afterArgs : ArgsMatch args after :=
        lowerInstruction_preservesArgs destination (nextTempRegister_notInput available)
          currentFits instruction args state argsMatch
      have afterTemps : TempsSound (temps := instructionValue :: temps) (by
          simp only [Fits] at restFits
          omega) args after := by
        intro value ref
        exact (TempsSound.afterInstruction currentFits (by
            simp only [Fits] at restFits
            omega) available instruction args state argsMatch tempsSound) ref
      simp only [lowerSegments, List.flatMap_cons, runLocalSteps_append]
      change
        (runLocalSteps ((lowerSegments rest restFits).flatMap Segment.code) after).gprs
            resultRegister = result args
      exact ih restFits args after afterArgs afterTemps

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-process-entry-backend -/
/-- Exact local functional realization of every bounded portable straight-line plan. This is an
    instruction-fold theorem, not platform execution or process-entry authority. -/
theorem lowerInstructions_correct (code : Code [] result) (fits : Fits code)
    (state : X86_64MachineState) :
    (runLocalSteps (lowerInstructions code fits) state).gprs resultRegister =
      result (argsOfState state) := by
  apply lowerSegments_correct code fits (argsOfState state) state rfl
  intro value ref
  cases ref

theorem lowerInstructions_controlFlowFree (code : Code temps result) (fits : Fits code)
    (instruction : X86_64Instr) (member : instruction ∈ lowerInstructions code fits) :
    ControlFlowFree instruction := by
  simp only [lowerInstructions, List.mem_flatMap] at member
  obtain ⟨segment, segmentMember, instructionMember⟩ := member
  exact segment.controlFlowFree instruction instructionMember

theorem lowerBytes_exact (code : Code temps result) (fits : Fits code) :
    lowerBytes code fits =
      Gasm.Targets.X86_64.Assembler.serializeInstructions (lowerInstructions code fits) := rfl

private theorem lowerOperand_memory (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) (operand : Operand temps value) :
    (lowerOperand destination fits operand).contract.memory = .preserved := by
  cases operand <;> rfl

private theorem lowerInstruction_memory (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) (instruction : Instruction temps value) :
    (lowerInstruction destination fits instruction).contract.memory = .preserved := by
  cases instruction <;>
    simp [lowerInstruction, Segment.then, lowerOperand_memory] <;> exact ⟨rfl, rfl⟩

private theorem lowerInstruction_clobbers (destination : Reg64)
    (fits : temps.length ≤ maxTemporaries) (instruction : Instruction temps value) :
    (lowerInstruction destination fits instruction).contract.clobberedGprs =
      [lhsScratch, rhsScratch, destination, destination] := by
  cases instruction <;>
    simp only [lowerInstruction, Segment.then, lowerOperand_clobbers] <;> rfl

private theorem lowerSegments_clobbersWithin (code : Code temps result) (fits : Fits code) :
    ∀ segment ∈ lowerSegments code fits, ∀ register ∈ segment.contract.clobberedGprs,
      register ∈ allowedClobbers := by
  induction code with
  | @done operandTemps operandValue operand =>
      intro segment segmentMember register registerMember
      simp only [lowerSegments, List.mem_singleton] at segmentMember
      subst segment
      have operandFits : operandTemps.length ≤ maxTemporaries := by
        simpa only [Fits, Code.instructionCount, Nat.add_zero] using fits
      change register ∈
        (lowerOperand resultRegister operandFits operand).contract.clobberedGprs at registerMember
      rw [lowerOperand_clobbers] at registerMember
      simp only [List.mem_singleton] at registerMember
      subst register
      simp [allowedClobbers, resultRegister]
  | @emit temps value result instruction rest ih =>
      intro segment segmentMember register registerMember
      simp only [lowerSegments, List.mem_cons] at segmentMember
      rcases segmentMember with rfl | segmentMember
      · rw [lowerInstruction_clobbers] at registerMember
        simp at registerMember
        rcases registerMember with rfl | rfl | rfl
        · simp [allowedClobbers]
        · simp [allowedClobbers]
        · simp only [allowedClobbers, List.mem_append, List.mem_cons]
          right
          exact tempRegister_mem_nonvolatile _
      · exact ih _ segment segmentMember register registerMember

private theorem lowerSegments_memory (code : Code temps result) (fits : Fits code) :
    ∀ segment ∈ lowerSegments code fits, segment.contract.memory = .preserved := by
  induction code with
  | done operand =>
      intro segment member
      simp only [lowerSegments, List.mem_singleton] at member
      subst segment
      exact lowerOperand_memory resultRegister _ operand
  | @emit temps value result instruction rest ih =>
      intro segment member
      simp only [lowerSegments, List.mem_cons] at member
      rcases member with rfl | member
      · exact lowerInstruction_memory _ _ instruction
      · exact ih _ segment member

private theorem runSegments_preservesMemory (segments : List Segment)
    (preserved : ∀ segment ∈ segments, segment.contract.memory = .preserved)
    (state : X86_64MachineState) :
    (runLocalSteps (segments.flatMap Segment.code) state).memory = state.memory := by
  induction segments generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons, runLocalSteps_append]
      rw [ih (fun segment member => preserved segment (by simp [member]))]
      exact first.preservesMemory (preserved first (by simp)) state

private theorem runSegments_preservesGpr (segments : List Segment)
    (state : X86_64MachineState) (register : Reg64)
    (preserved : register ∉ segments.flatMap (fun segment => segment.contract.clobberedGprs)) :
    (runLocalSteps (segments.flatMap Segment.code) state).gprs register = state.gprs register := by
  induction segments generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at preserved
      simp only [List.flatMap_cons, runLocalSteps_append]
      rw [ih _ preserved.2]
      exact first.preservesGpr state register preserved.1

private theorem lowerSegments_preservesArgs (code : Code temps result) (fits : Fits code)
    (args : Args) (state : X86_64MachineState) (matchArgs : ArgsMatch args state) :
    ArgsMatch args (runLocalSteps ((lowerSegments code fits).flatMap Segment.code) state) := by
  induction code generalizing state args with
  | done operand =>
      simp only [lowerSegments, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        resultSegment]
      exact lowerOperand_preservesArgs resultRegister (by decide) _ operand args state matchArgs
  | @emit temps value result instruction rest ih =>
      have currentFits : temps.length ≤ maxTemporaries := by
        simp only [Fits, Code.instructionCount] at fits
        omega
      have available : temps.length < maxTemporaries := by
        simp only [Fits, Code.instructionCount] at fits
        omega
      have restFits : Fits rest := by
        simp only [Fits, Code.instructionCount, List.length_cons] at fits ⊢
        omega
      let destination := nextTempRegister available
      let after := runLocalSteps (lowerInstruction destination currentFits instruction).code state
      have afterArgs : ArgsMatch args after :=
        lowerInstruction_preservesArgs destination (nextTempRegister_notInput available)
          currentFits instruction args state matchArgs
      simp only [lowerSegments, List.flatMap_cons, runLocalSteps_append]
      change ArgsMatch args
        (runLocalSteps ((lowerSegments rest restFits).flatMap Segment.code) after)
      exact ih restFits args after afterArgs

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-process-entry-backend -/
/-- Proof-producing output for the bounded Microsoft-x64 process-entry body. It certifies only
    source-to-local-instruction semantics and frame facts. It is neither callable ABI evidence nor
    platform execution, PE placement, fallthrough/return exclusion, unwind, callback/reentrancy,
    exception or fault continuation, teardown, ExitProcess, artifact, export, or `VerifiedProgram`
    authority. Non-callability is represented by the absence of a callable certificate and the
    exact exposed nonvolatile clobbers, not by self-asserted metadata. -/
structure LocalCertificate (source : Structured.WordFunction)
    (selected : WordOnly (source := source.body)) (fits : Fits (compile selected)) where
  portableCode : Code [] (fun args => source.body.eval (Structured.InputContext.env args))
  segments : List Segment
  instructions : List X86_64Instr
  codeBytes : ByteArray
  portableCode_eq : portableCode = compile selected
  segments_eq : segments = lowerSegments portableCode (portableCode_eq ▸ fits)
  instructions_eq : instructions = segments.flatMap Segment.code
  codeBytes_eq : codeBytes =
    Gasm.Targets.X86_64.Assembler.serializeInstructions instructions
  localResult : ∀ state,
    (runLocalSteps instructions state).gprs resultRegister = source.fn (argsOfState state)
  preservesInputs : ∀ state,
    argsOfState (runLocalSteps instructions state) = argsOfState state
  preservesMemory : ∀ state,
    (runLocalSteps instructions state).memory = state.memory
  preservesFault : ∀ state,
    (runLocalSteps instructions state).fault = state.fault
  ripAdvance : ∀ state,
    (runLocalSteps instructions state).rip = state.rip + instructionSpan instructions
  clobberedGprs : List Reg64
  clobberedGprs_eq :
    clobberedGprs = segments.flatMap (fun segment => segment.contract.clobberedGprs)
  clobbersWithin : ∀ register ∈ clobberedGprs, register ∈ allowedClobbers
  preservesGpr : ∀ state register, register ∉ clobberedGprs →
    (runLocalSteps instructions state).gprs register = state.gprs register
  flags : FieldEffect
  flags_eq : flags = .unspecified
  controlFlowFree : ∀ instruction ∈ instructions, ControlFlowFree instruction
  nonvolatileTempClobbers_eq : nonvolatileTempClobbers =
    [.rbx, .rsi, .rdi, .r12, .r13, .r14, .r15]

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-process-entry-backend -/
/-- Generate all feature-applicable local evidence. A target-owned adapter must still establish
    the non-callable process-entry boundary and connect the exact body to the final artifact. -/
def lowerFunction (source : Structured.WordFunction)
    (selected : WordOnly (source := source.body)) (fits : Fits (compile selected)) :
    LocalCertificate source selected fits where
  portableCode := compile selected
  segments := lowerSegments (compile selected) fits
  instructions := lowerInstructions (compile selected) fits
  codeBytes := lowerBytes (compile selected) fits
  portableCode_eq := rfl
  segments_eq := rfl
  instructions_eq := rfl
  codeBytes_eq := rfl
  localResult := by
    intro state
    rw [lowerInstructions_correct]
    exact (source.implements (argsOfState state)).symm
  preservesInputs := by
    intro state
    exact lowerSegments_preservesArgs (compile selected) fits (argsOfState state) state rfl
  preservesMemory := runSegments_preservesMemory _ (lowerSegments_memory _ fits)
  preservesFault := runLocalSteps_fault_eq _ (lowerInstructions_controlFlowFree _ fits)
  ripAdvance := runLocalSteps_rip_eq _ (lowerInstructions_controlFlowFree _ fits)
  clobberedGprs := (lowerSegments (compile selected) fits).flatMap
    (fun segment => segment.contract.clobberedGprs)
  clobberedGprs_eq := rfl
  clobbersWithin := by
    intro register member
    simp only [List.mem_flatMap] at member
    obtain ⟨segment, segmentMember, registerMember⟩ := member
    exact lowerSegments_clobbersWithin _ fits segment segmentMember register registerMember
  preservesGpr := by
    intro state register preserved
    exact runSegments_preservesGpr _ state register preserved
  flags := .unspecified
  flags_eq := rfl
  controlFlowFree := lowerInstructions_controlFlowFree _ fits
  nonvolatileTempClobbers_eq := rfl

end Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry

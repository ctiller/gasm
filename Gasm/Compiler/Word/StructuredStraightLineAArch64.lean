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
import Gasm.Compiler.Word.AArch64AAPCS64

namespace Gasm.Compiler.Word.StructuredStraightLineAArch64

open Gasm.Compiler.Word
open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.MacroAssembler

private def gpr (value : Nat) (valid : value < 31 := by omega) : Gpr :=
  ⟨value, valid⟩

def x0 : Gpr := gpr 0
def x1 : Gpr := gpr 1
def x2 : Gpr := gpr 2
def x3 : Gpr := gpr 3
def lhsScratch : Gpr := gpr 16
def rhsScratch : Gpr := gpr 17

def maxTemporaries : Nat := 7

/- REF: docs/MACRO_ASSEMBLER.md#structured-aarch64-bounded-backend -/
/-- The fixed temporary register selected by creation order. Only X9--X15 are admitted. -/
def tempRegister (index : Fin maxTemporaries) : Gpr :=
  gpr (9 + index.val) (by
    have bound := index.isLt
    simp only [maxTemporaries] at bound
    omega)

namespace Allocation

def deBruijnIndex : TempRef temps value → Nat
  | .newest => 0
  | .older ref => deBruijnIndex ref + 1

theorem deBruijnIndex_lt (ref : TempRef temps value) : deBruijnIndex ref < temps.length := by
  induction ref with
  | newest => simp [deBruijnIndex]
  | older ref ih => simp only [deBruijnIndex, List.length_cons]; omega

/-- Absolute creation order. Unlike the de Bruijn index, this is stable when a newer temporary is
    introduced. -/
def creationIndex (ref : TempRef temps value) : Nat :=
  temps.length - 1 - deBruijnIndex ref

theorem creationIndex_lt (ref : TempRef temps value) : creationIndex ref < temps.length := by
  have := deBruijnIndex_lt ref
  simp only [creationIndex]
  omega

@[simp] theorem creationIndex_older (newer : Args → UInt64) (ref : TempRef temps value) :
    creationIndex (temps := newer :: temps) (TempRef.older ref) = creationIndex ref := by
  simp only [creationIndex, deBruijnIndex, List.length_cons]
  have := deBruijnIndex_lt ref
  omega

end Allocation

/- REF: docs/MACRO_ASSEMBLER.md#structured-aarch64-bounded-backend -/
/-- Structural resource premise for the first backend. It conservatively assigns one register to
    every emitted temporary; liveness reuse and spilling are deliberately later passes. -/
def Fits (code : Code temps result) : Prop :=
  temps.length + code.instructionCount ≤ maxTemporaries

private def tempOfRef (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) : Gpr :=
  tempRegister ⟨Allocation.creationIndex ref,
    Nat.lt_of_lt_of_le (Allocation.creationIndex_lt ref) fits⟩

def inputRegister : Fin 4 → Gpr
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3

private def lowerOperand (destination : Gpr) (fits : temps.length ≤ maxTemporaries) :
    Operand temps value → Segment
  | .a0 => mov destination x0
  | .a1 => mov destination x1
  | .a2 => mov destination x2
  | .a3 => mov destination x3
  | .constant value => loadImm destination value
  | .temp ref => mov destination (tempOfRef fits ref)

def argsOfState (state : AArch64MachineState) : Args where
  a0 := state.gprs x0
  a1 := state.gprs x1
  a2 := state.gprs x2
  a3 := state.gprs x3

private def ArgsMatch (args : Args) (state : AArch64MachineState) : Prop :=
  argsOfState state = args

private def TempsSound {temps : List (Args → UInt64)}
    (fits : temps.length ≤ maxTemporaries) (args : Args)
    (state : AArch64MachineState) : Prop :=
  ∀ {value} (ref : TempRef temps value), state.gprs (tempOfRef fits ref) = value args

private theorem tempOfRef_bounds (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) :
    9 ≤ (tempOfRef fits ref).val ∧ (tempOfRef fits ref).val ≤ 15 := by
  simp only [tempOfRef, tempRegister, gpr]
  have bound := (Allocation.creationIndex_lt ref)
  have selected := Nat.lt_of_lt_of_le bound fits
  simp only [maxTemporaries] at selected
  omega

private theorem tempOfRef_ne_input (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) :
    tempOfRef fits ref ≠ x0 ∧ tempOfRef fits ref ≠ x1 ∧
      tempOfRef fits ref ≠ x2 ∧ tempOfRef fits ref ≠ x3 := by
  have bounds := tempOfRef_bounds fits ref
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    simp only [x0, gpr] at values
    omega
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    simp only [x1, gpr] at values
    omega
  constructor <;> intro equal
  · have values := congrArg Fin.val equal
    simp only [x2, gpr] at values
    omega
  · have values := congrArg Fin.val equal
    simp only [x3, gpr] at values
    omega

private theorem tempOfRef_ne_lhsScratch (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) : tempOfRef fits ref ≠ lhsScratch := by
  have bounds := tempOfRef_bounds fits ref
  intro equal
  have values := congrArg Fin.val equal
  simp only [lhsScratch, gpr] at values
  omega

private theorem tempOfRef_ne_rhsScratch (fits : temps.length ≤ maxTemporaries)
    (ref : TempRef temps value) : tempOfRef fits ref ≠ rhsScratch := by
  have bounds := tempOfRef_bounds fits ref
  intro equal
  have values := congrArg Fin.val equal
  simp only [rhsScratch, gpr] at values
  omega

private theorem lowerOperand_correct (destination : Gpr)
    (fits : temps.length ≤ maxTemporaries) (operand : Operand temps value)
    (args : Args) (state : AArch64MachineState) (argsMatch : ArgsMatch args state)
    (tempsSound : TempsSound fits args state) :
    (runLocalSteps (lowerOperand destination fits operand).code state).gprs destination =
      value args := by
  cases operand with
  | a0 =>
      have component := congrArg Args.a0 argsMatch
      exact (mov_result destination x0 state).trans component
  | a1 =>
      have component := congrArg Args.a1 argsMatch
      exact (mov_result destination x1 state).trans component
  | a2 =>
      have component := congrArg Args.a2 argsMatch
      exact (mov_result destination x2 state).trans component
  | a3 =>
      have component := congrArg Args.a3 argsMatch
      exact (mov_result destination x3 state).trans component
  | constant constant =>
      simpa [lowerOperand, AArch64AAPCS64.lowerAtom, Atom.eval] using
        AArch64AAPCS64.lowerAtom_correct destination (.const constant) state
  | temp ref =>
      exact (mov_result destination (tempOfRef fits ref) state).trans (tempsSound ref)

private theorem lowerOperand_preservesGpr (destination register : Gpr)
    (different : register ≠ destination) (fits : temps.length ≤ maxTemporaries)
    (operand : Operand temps value) (state : AArch64MachineState) :
    (runLocalSteps (lowerOperand destination fits operand).code state).gprs register =
      state.gprs register := by
  cases operand with
  | a0 | a1 | a2 | a3 =>
      apply (lowerOperand destination fits _).preservesGpr
      change register ∉ [destination]
      simpa using different
  | constant constant =>
      simpa [lowerOperand, AArch64AAPCS64.lowerAtom] using
        AArch64AAPCS64.lowerAtom_preservesGpr destination register different
          (.const constant) state
  | temp ref =>
      apply (lowerOperand destination fits (.temp ref)).preservesGpr
      change register ∉ [destination]
      simpa using different

private theorem lowerOperand_preservesArgs (destination : Gpr)
    (notInput : destination ≠ x0 ∧ destination ≠ x1 ∧ destination ≠ x2 ∧ destination ≠ x3)
    (fits : temps.length ≤ maxTemporaries) (operand : Operand temps value)
    (args : Args) (state : AArch64MachineState) (argsMatch : ArgsMatch args state) :
    ArgsMatch args (runLocalSteps (lowerOperand destination fits operand).code state) := by
  apply Args.ext <;>
    simp only [ArgsMatch, argsOfState] at argsMatch ⊢
  · rw [lowerOperand_preservesGpr destination x0 (Ne.symm notInput.1)]
    exact congrArg Args.a0 argsMatch
  · rw [lowerOperand_preservesGpr destination x1 (Ne.symm notInput.2.1)]
    exact congrArg Args.a1 argsMatch
  · rw [lowerOperand_preservesGpr destination x2 (Ne.symm notInput.2.2.1)]
    exact congrArg Args.a2 argsMatch
  · rw [lowerOperand_preservesGpr destination x3 (Ne.symm notInput.2.2.2)]
    exact congrArg Args.a3 argsMatch

private theorem lowerOperand_preservesTemps (destination : Gpr)
    (fits : temps.length ≤ maxTemporaries)
    (different : ∀ {value} (ref : TempRef temps value), tempOfRef fits ref ≠ destination)
    (operand : Operand temps operandValue)
    (args : Args) (state : AArch64MachineState) (sound : TempsSound fits args state) :
    TempsSound fits args (runLocalSteps (lowerOperand destination fits operand).code state) := by
  intro value ref
  rw [lowerOperand_preservesGpr destination (tempOfRef fits ref) (different ref)]
  exact sound ref

private def lowerInstruction (destination : Gpr) (fits : temps.length ≤ maxTemporaries) :
    Instruction temps value → Segment
  | .add lhs rhs =>
      (lowerOperand lhsScratch fits lhs).then
        ((lowerOperand rhsScratch fits rhs).then (add destination lhsScratch rhsScratch))
  | .sub lhs rhs =>
      (lowerOperand lhsScratch fits lhs).then
        ((lowerOperand rhsScratch fits rhs).then (sub destination lhsScratch rhsScratch))
  | .bitAnd lhs rhs =>
      (lowerOperand lhsScratch fits lhs).then
        ((lowerOperand rhsScratch fits rhs).then (and destination lhsScratch rhsScratch))

private theorem lowerInstruction_correct (destination : Gpr)
    (fits : temps.length ≤ maxTemporaries) (instruction : Instruction temps value)
    (args : Args) (state : AArch64MachineState) (argsMatch : ArgsMatch args state)
    (tempsSound : TempsSound fits args state) :
    (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs destination =
      value args := by
  cases instruction with
  | add lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [add_result]
      let afterLhs := runLocalSteps (lowerOperand lhsScratch fits lhs).code state
      have argsAfterLhs : ArgsMatch args afterLhs :=
        lowerOperand_preservesArgs lhsScratch (by decide) fits lhs args state argsMatch
      have tempsAfterLhs : TempsSound fits args afterLhs :=
        lowerOperand_preservesTemps lhsScratch fits
          (fun ref => tempOfRef_ne_lhsScratch fits ref) lhs args state tempsSound
      rw [lowerOperand_correct rhsScratch fits rhs args afterLhs argsAfterLhs tempsAfterLhs]
      rw [lowerOperand_preservesGpr rhsScratch lhsScratch (by decide)]
      rw [lowerOperand_correct lhsScratch fits lhs args state argsMatch tempsSound]
  | sub lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [sub_result]
      let afterLhs := runLocalSteps (lowerOperand lhsScratch fits lhs).code state
      have argsAfterLhs : ArgsMatch args afterLhs :=
        lowerOperand_preservesArgs lhsScratch (by decide) fits lhs args state argsMatch
      have tempsAfterLhs : TempsSound fits args afterLhs :=
        lowerOperand_preservesTemps lhsScratch fits
          (fun ref => tempOfRef_ne_lhsScratch fits ref) lhs args state tempsSound
      rw [lowerOperand_correct rhsScratch fits rhs args afterLhs argsAfterLhs tempsAfterLhs]
      rw [lowerOperand_preservesGpr rhsScratch lhsScratch (by decide)]
      rw [lowerOperand_correct lhsScratch fits lhs args state argsMatch tempsSound]
  | bitAnd lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [and_result]
      let afterLhs := runLocalSteps (lowerOperand lhsScratch fits lhs).code state
      have argsAfterLhs : ArgsMatch args afterLhs :=
        lowerOperand_preservesArgs lhsScratch (by decide) fits lhs args state argsMatch
      have tempsAfterLhs : TempsSound fits args afterLhs :=
        lowerOperand_preservesTemps lhsScratch fits
          (fun ref => tempOfRef_ne_lhsScratch fits ref) lhs args state tempsSound
      rw [lowerOperand_correct rhsScratch fits rhs args afterLhs argsAfterLhs tempsAfterLhs]
      rw [lowerOperand_preservesGpr rhsScratch lhsScratch (by decide)]
      rw [lowerOperand_correct lhsScratch fits lhs args state argsMatch tempsSound]

private theorem lowerInstruction_preservesGpr (destination register : Gpr)
    (notDestination : register ≠ destination) (notLhs : register ≠ lhsScratch)
    (notRhs : register ≠ rhsScratch) (fits : temps.length ≤ maxTemporaries)
    (instruction : Instruction temps value) (state : AArch64MachineState) :
    (runLocalSteps (lowerInstruction destination fits instruction).code state).gprs register =
      state.gprs register := by
  cases instruction with
  | add lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(add destination lhsScratch rhsScratch).preservesGpr _ register (by
        simp [add, Segment.clobberedGprs, Instruction.clobberedGprs, notDestination])]
      rw [lowerOperand_preservesGpr rhsScratch register notRhs]
      exact lowerOperand_preservesGpr lhsScratch register notLhs fits lhs state
  | sub lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(sub destination lhsScratch rhsScratch).preservesGpr _ register (by
        simp [sub, Segment.clobberedGprs, Instruction.clobberedGprs, notDestination])]
      rw [lowerOperand_preservesGpr rhsScratch register notRhs]
      exact lowerOperand_preservesGpr lhsScratch register notLhs fits lhs state
  | bitAnd lhs rhs =>
      simp only [lowerInstruction, Segment.then, runLocalSteps_append]
      rw [(MacroAssembler.and destination lhsScratch rhsScratch).preservesGpr _ register (by
        simp [MacroAssembler.and, Segment.clobberedGprs, Instruction.clobberedGprs,
          notDestination])]
      rw [lowerOperand_preservesGpr rhsScratch register notRhs]
      exact lowerOperand_preservesGpr lhsScratch register notLhs fits lhs state

private theorem lowerInstruction_preservesArgs (destination : Gpr)
    (notInput : destination ≠ x0 ∧ destination ≠ x1 ∧ destination ≠ x2 ∧ destination ≠ x3)
    (fits : temps.length ≤ maxTemporaries) (instruction : Instruction temps value)
    (args : Args) (state : AArch64MachineState) (argsMatch : ArgsMatch args state) :
    ArgsMatch args (runLocalSteps (lowerInstruction destination fits instruction).code state) := by
  apply Args.ext <;> simp only [ArgsMatch, argsOfState] at argsMatch ⊢
  · rw [lowerInstruction_preservesGpr destination x0 (Ne.symm notInput.1) (by decide)
      (by decide)]
    exact congrArg Args.a0 argsMatch
  · rw [lowerInstruction_preservesGpr destination x1 (Ne.symm notInput.2.1) (by decide)
      (by decide)]
    exact congrArg Args.a1 argsMatch
  · rw [lowerInstruction_preservesGpr destination x2 (Ne.symm notInput.2.2.1) (by decide)
      (by decide)]
    exact congrArg Args.a2 argsMatch
  · rw [lowerInstruction_preservesGpr destination x3 (Ne.symm notInput.2.2.2) (by decide)
      (by decide)]
    exact congrArg Args.a3 argsMatch

private def nextTempRegister {temps : List (Args → UInt64)}
    (available : temps.length < maxTemporaries) : Gpr :=
  tempRegister ⟨temps.length, available⟩

private theorem nextTempRegister_ne_input (available : temps.length < maxTemporaries) :
    nextTempRegister (temps := temps) available ≠ x0 ∧
      nextTempRegister (temps := temps) available ≠ x1 ∧
      nextTempRegister (temps := temps) available ≠ x2 ∧
      nextTempRegister (temps := temps) available ≠ x3 := by
  simp only [maxTemporaries] at available
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    simp only [nextTempRegister, tempRegister, x0, gpr] at values
    omega
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    simp only [nextTempRegister, tempRegister, x1, gpr] at values
    omega
  constructor <;> intro equal
  · have values := congrArg Fin.val equal
    simp only [nextTempRegister, tempRegister, x2, gpr] at values
    omega
  · have values := congrArg Fin.val equal
    simp only [nextTempRegister, tempRegister, x3, gpr] at values
    omega

private theorem nextTempRegister_ne_lhsScratch (available : temps.length < maxTemporaries) :
    nextTempRegister (temps := temps) available ≠ lhsScratch := by
  intro equal
  have values := congrArg Fin.val equal
  simp only [nextTempRegister, tempRegister, lhsScratch, gpr] at values
  simp only [maxTemporaries] at available
  omega

private theorem nextTempRegister_ne_rhsScratch (available : temps.length < maxTemporaries) :
    nextTempRegister (temps := temps) available ≠ rhsScratch := by
  intro equal
  have values := congrArg Fin.val equal
  simp only [nextTempRegister, tempRegister, rhsScratch, gpr] at values
  simp only [maxTemporaries] at available
  omega

private theorem tempOfRef_ne_next (fits : temps.length ≤ maxTemporaries)
    (available : temps.length < maxTemporaries) (ref : TempRef temps value) :
    tempOfRef fits ref ≠ nextTempRegister available := by
  intro equal
  have values := congrArg Fin.val equal
  simp only [tempOfRef, nextTempRegister, tempRegister, gpr] at values
  have prior := Allocation.creationIndex_lt ref
  omega

private theorem tempOfRef_newest (restFits : (value :: temps).length ≤ maxTemporaries)
    (available : temps.length < maxTemporaries) :
    tempOfRef restFits (TempRef.newest : TempRef (value :: temps) value) =
      nextTempRegister available := by
  apply Fin.ext
  simp [tempOfRef, nextTempRegister, tempRegister, Allocation.creationIndex,
    Allocation.deBruijnIndex]

private theorem tempOfRef_older (fits : temps.length ≤ maxTemporaries)
    (restFits : (newer :: temps).length ≤ maxTemporaries) (ref : TempRef temps value) :
    tempOfRef restFits (TempRef.older ref) = tempOfRef fits ref := by
  apply Fin.ext
  simp [tempOfRef, tempRegister, Allocation.creationIndex_older]

private theorem TempsSound.afterInstruction (fits : temps.length ≤ maxTemporaries)
    (restFits : (newValue :: temps).length ≤ maxTemporaries)
    (available : temps.length < maxTemporaries) (instruction : Instruction temps newValue)
    (args : Args) (state : AArch64MachineState) (argsMatch : ArgsMatch args state)
    (sound : TempsSound fits args state) :
    TempsSound restFits args
      (runLocalSteps (lowerInstruction (nextTempRegister available) fits instruction).code state) := by
  intro value ref
  cases ref with
  | newest =>
      rw [tempOfRef_newest restFits available]
      exact lowerInstruction_correct (nextTempRegister available) fits instruction args state
        argsMatch sound
  | older ref =>
      rw [tempOfRef_older fits restFits ref]
      rw [lowerInstruction_preservesGpr (nextTempRegister available) (tempOfRef fits ref)
        (tempOfRef_ne_next fits available ref)
        (tempOfRef_ne_lhsScratch fits ref) (tempOfRef_ne_rhsScratch fits ref)]
      exact sound ref

private def resultSegment (fits : temps.length ≤ maxTemporaries)
    (result : Operand temps value) : Segment :=
  lowerOperand x0 fits result

/- REF: docs/MACRO_ASSEMBLER.md#structured-aarch64-bounded-backend -/
/-- Total lowering under an explicit finite-register proof. -/
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

def lowerCode (code : Code temps result) (fits : Fits code) : List Instruction :=
  (lowerSegments code fits).flatMap Segment.code

def lowerInstructions (code : Code temps result) (fits : Fits code) :
    List AnyAArch64Instruction :=
  (lowerCode code fits).map Instruction.emit

def lowerBytes (code : Code temps result) (fits : Fits code) : ByteArray :=
  serialize (lowerCode code fits)

private theorem lowerSegments_correct (code : Code temps result) (fits : Fits code)
    (args : Args) (state : AArch64MachineState) (argsMatch : ArgsMatch args state)
    (tempsSound : TempsSound (temps := temps) (by
      have total := fits
      simp only [Fits] at total
      omega) args state) :
    (runLocalSteps ((lowerSegments code fits).flatMap Segment.code) state).gprs x0 =
      result args := by
  induction code generalizing state args with
  | done operand =>
      simp only [lowerSegments, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact lowerOperand_correct x0 (by
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
        lowerInstruction_preservesArgs destination (nextTempRegister_ne_input available)
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
        (runLocalSteps ((lowerSegments rest restFits).flatMap Segment.code) after).gprs x0 =
          result args
      exact ih restFits args after afterArgs afterTemps

/- REF: docs/MACRO_ASSEMBLER.md#structured-aarch64-bounded-backend -/
/-- Exact local functional realization of every bounded portable plan. This theorem concerns the
    target instruction fold only; the spike-level production runner and final artifact remain
    separate authority-bearing layers. -/
theorem lowerCode_correct (code : Code [] result) (fits : Fits code)
    (state : AArch64MachineState) :
    (runLocalSteps (lowerCode code fits) state).gprs x0 = result (argsOfState state) := by
  apply lowerSegments_correct code fits (argsOfState state) state rfl
  intro value ref
  cases ref

theorem lowerInstructions_controlFlowFree (code : Code temps result) (fits : Fits code)
    (instruction : AnyAArch64Instruction) (member : instruction ∈ lowerInstructions code fits) :
    ControlFlowFree instruction := by
  simp only [lowerInstructions, List.mem_map] at member
  obtain ⟨selected, _, rfl⟩ := member
  exact selected.controlFlowFree

theorem lowerBytes_exact (code : Code temps result) (fits : Fits code) :
    lowerBytes code fits = serializeEmitted (lowerInstructions code fits) := by
  exact serialize_eq_serializeEmitted (lowerCode code fits)

/- REF: docs/MACRO_ASSEMBLER.md#structured-aarch64-bounded-backend -/
/-- Exact proof-producing frontend result for one selected, bounded structured function. This is a
    local target realization, not yet the spike's production execution or whole-program authority. -/
structure LocalCertificate (source : Structured.WordFunction)
    (selected : WordOnly (source := source.body)) (fits : Fits (compile selected)) where
  portableCode : Code [] (fun args => source.body.eval (Structured.InputContext.env args))
  code : List Instruction
  instructions : List AnyAArch64Instruction
  codeBytes : ByteArray
  portableCode_eq : portableCode = compile selected
  code_eq : code = lowerCode portableCode (portableCode_eq ▸ fits)
  instructions_eq : instructions = code.map Instruction.emit
  codeBytes_eq : codeBytes = serialize code
  emittedBytes_eq : codeBytes = serializeEmitted instructions
  localResult : ∀ state,
    (runLocalSteps code state).gprs x0 = source.fn (argsOfState state)
  preservesMemory : ∀ state, (runLocalSteps code state).memory = state.memory
  preservesSp : ∀ state, (runLocalSteps code state).sp = state.sp
  preservesNzcv : ∀ state, (runLocalSteps code state).nzcv = state.nzcv
  preservesFault : ∀ state, (runLocalSteps code state).fault = state.fault
  preservesTerminated : ∀ state,
    (runLocalSteps code state).terminated = state.terminated
  pcAdvance : ∀ state,
    (runLocalSteps code state).pc = state.pc + localCodeSize code
  clobberedGprs : List Gpr
  clobberedGprs_eq : clobberedGprs = code.flatMap Instruction.clobberedGprs
  preservesGpr : ∀ state register, register ∉ clobberedGprs →
    (runLocalSteps code state).gprs register = state.gprs register
  controlFlowFree : ∀ instruction ∈ instructions, ControlFlowFree instruction

/- REF: docs/MACRO_ASSEMBLER.md#structured-aarch64-bounded-backend -/
def lowerFunction (source : Structured.WordFunction)
    (selected : WordOnly (source := source.body)) (fits : Fits (compile selected)) :
    LocalCertificate source selected fits where
  portableCode := compile selected
  code := lowerCode (compile selected) fits
  instructions := lowerInstructions (compile selected) fits
  codeBytes := lowerBytes (compile selected) fits
  portableCode_eq := rfl
  code_eq := rfl
  instructions_eq := rfl
  codeBytes_eq := rfl
  emittedBytes_eq := lowerBytes_exact (compile selected) fits
  localResult := by
    intro state
    rw [lowerCode_correct]
    exact (source.implements (argsOfState state)).symm
  preservesMemory := runLocalSteps_preservesMemory _
  preservesSp := runLocalSteps_preservesSp _
  preservesNzcv := runLocalSteps_preservesNzcv _
  preservesFault := runLocalSteps_preservesFault _
  preservesTerminated := runLocalSteps_preservesTerminated _
  pcAdvance := runLocalSteps_pc _
  clobberedGprs := (lowerCode (compile selected) fits).flatMap Instruction.clobberedGprs
  clobberedGprs_eq := rfl
  preservesGpr := by
    intro state register preserved
    exact runLocalSteps_preservesGpr _ state register preserved
  controlFlowFree := lowerInstructions_controlFlowFree (compile selected) fits

end Gasm.Compiler.Word.StructuredStraightLineAArch64

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

import Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
import Gasm.Targets.X86_64.MacroAssembler.Condition

namespace Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry

open Gasm.Compiler.Word
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
/-- The deliberately first condition subset: equality or unsigned less-than between two of the
    four input variables, optionally negated once. Operations, literals, lets, nested negation, and
    other Boolean forms are rejected rather than normalized into this grammar. -/
inductive Selected : (source : Structured.Expr InputContext .bool) → Type where
  | eq (left right : Var InputContext .word) :
      Selected (.eq (.var left) (.var right))
  | ult (left right : Var InputContext .word) :
      Selected (.ult (.var left) (.var right))
  | notEq (left right : Var InputContext .word) :
      Selected (.not (.eq (.var left) (.var right)))
  | notUlt (left right : Var InputContext .word) :
      Selected (.not (.ult (.var left) (.var right)))

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
/-- Structural recognition only; no reduction or helper unfolding occurs here. -/
def select : (source : Structured.Expr InputContext .bool) → Option (Selected source)
  | .eq (.var left) (.var right) => some (.eq left right)
  | .ult (.var left) (.var right) => some (.ult left right)
  | .not (.eq (.var left) (.var right)) => some (.notEq left right)
  | .not (.ult (.var left) (.var right)) => some (.notUlt left right)
  | _ => none

def inputRegister : Var InputContext .word → Reg64
  | .zero => .rcx
  | .succ .zero => .rdx
  | .succ (.succ .zero) => .r8
  | .succ (.succ (.succ .zero)) => .r9

private theorem inputRegister_value (ref : Var InputContext .word)
    (state : X86_64MachineState) :
    state.gprs (inputRegister ref) = InputContext.env (argsOfState state) ref := by
  cases ref with
  | zero => rfl
  | succ ref =>
      cases ref with
      | zero => rfl
      | succ ref =>
          cases ref with
          | zero => rfl
          | succ ref =>
              cases ref with
              | zero => rfl
              | succ ref => cases ref

def Selected.left : Selected source → Var InputContext .word
  | .eq left _ | .ult left _ | .notEq left _ | .notUlt left _ => left

def Selected.right : Selected source → Var InputContext .word
  | .eq _ right | .ult _ right | .notEq _ right | .notUlt _ right => right

def Selected.kind : Selected source → X86BranchCondition
  | .eq .. => .equal
  | .ult .. => .below
  | .notEq .. => .notEqual
  | .notUlt .. => .aboveOrEqual

def Selected.segment (selected : Selected source) : Segment :=
  Condition.compare (inputRegister selected.left) (inputRegister selected.right)

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
/-- Local proof-producing output for one selected portable condition. This supplies exact CMP
    instructions/bytes and portable-Bool agreement only; it is not a typed edge, branch encoding,
    layout, execution, artifact, or `VerifiedProgram` certificate. -/
structure LoweredCondition (source : Structured.Expr InputContext .bool) where
  selected : Selected source
  segment : Segment
  kind : X86BranchCondition
  instructions : List X86_64Instr
  codeBytes : ByteArray
  segment_eq : segment = selected.segment
  kind_eq : kind = selected.kind
  instructions_eq : instructions = segment.code
  codeBytes_eq : codeBytes =
    Gasm.Targets.X86_64.Assembler.serializeInstructions instructions
  semanticAgreement : ∀ state,
    kind.holds (runLocalSteps instructions state) ↔
      source.eval (InputContext.env (argsOfState state)) = true
  preservesInputs : ∀ state,
    argsOfState (runLocalSteps instructions state) = argsOfState state
  preservesMemory : ∀ state,
    (runLocalSteps instructions state).memory = state.memory
  preservesFault : ∀ state,
    (runLocalSteps instructions state).fault = state.fault
  ripAdvance : ∀ state,
    (runLocalSteps instructions state).rip = state.rip + instructionSpan instructions
  controlFlowFree : ∀ instruction ∈ instructions, ControlFlowFree instruction

private theorem Selected.semanticAgreement (selected : Selected source)
    (state : X86_64MachineState) :
    selected.kind.holds (runLocalSteps selected.segment.code state) ↔
      source.eval (InputContext.env (argsOfState state)) = true := by
  cases selected with
  | eq left right =>
      simp only [Selected.kind, Selected.segment, Selected.left, Selected.right]
      rw [Condition.compare_equal]
      simp [Structured.Expr.eval, inputRegister_value]
  | ult left right =>
      simp only [Selected.kind, Selected.segment, Selected.left, Selected.right]
      rw [Condition.compare_below]
      simp only [Structured.Expr.eval, inputRegister_value]
      constructor
      · exact decide_eq_true
      · exact of_decide_eq_true
  | notEq left right =>
      simp only [Selected.kind, Selected.segment, Selected.left, Selected.right]
      rw [show X86BranchCondition.notEqual.holds
          (runLocalSteps (Condition.compare (inputRegister left) (inputRegister right)).code state) ↔
          ¬X86BranchCondition.equal.holds
            (runLocalSteps (Condition.compare (inputRegister left) (inputRegister right)).code state) by
        simp [X86BranchCondition.holds]]
      rw [Condition.compare_equal]
      simp [Structured.Expr.eval, inputRegister_value]
  | notUlt left right =>
      simp only [Selected.kind, Selected.segment, Selected.left, Selected.right]
      rw [show X86BranchCondition.aboveOrEqual.holds
          (runLocalSteps (Condition.compare (inputRegister left) (inputRegister right)).code state) ↔
          ¬X86BranchCondition.below.holds
            (runLocalSteps (Condition.compare (inputRegister left) (inputRegister right)).code state) by
        simp [X86BranchCondition.holds]]
      rw [Condition.compare_below]
      change
        (¬state.gprs (inputRegister left) < state.gprs (inputRegister right)) ↔
          (!decide (InputContext.env (argsOfState state) left <
            InputContext.env (argsOfState state) right)) = true
      rw [inputRegister_value, inputRegister_value]
      by_cases less : InputContext.env (argsOfState state) left <
          InputContext.env (argsOfState state) right
      · rw [decide_eq_true less]
        simp [less]
      · rw [decide_eq_false less]
        simp [less]

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-conditions -/
def lower {source : Structured.Expr InputContext .bool}
    (selected : Selected source) : LoweredCondition source where
  selected := selected
  segment := selected.segment
  kind := selected.kind
  instructions := selected.segment.code
  codeBytes := Gasm.Targets.X86_64.Assembler.serializeInstructions selected.segment.code
  segment_eq := rfl
  kind_eq := rfl
  instructions_eq := rfl
  codeBytes_eq := rfl
  semanticAgreement := selected.semanticAgreement
  preservesInputs := by
    intro state
    apply Args.ext <;>
      apply selected.segment.preservesGpr <;>
      simp [Selected.segment, Condition.compare]
  preservesMemory := selected.segment.preservesMemory rfl
  preservesFault := runLocalSteps_fault_eq _ selected.segment.controlFlowFree
  ripAdvance := runLocalSteps_rip_eq _ selected.segment.controlFlowFree
  controlFlowFree := selected.segment.controlFlowFree

end Gasm.Compiler.Word.StructuredConditionMicrosoftX64Entry

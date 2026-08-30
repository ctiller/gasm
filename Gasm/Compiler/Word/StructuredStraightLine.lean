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

import Gasm.Compiler.Word.Structured

namespace Gasm.Compiler.Word.StructuredStraightLine

open Gasm.Compiler.Word
open Gasm.Compiler.Word.Structured

set_option linter.unusedVariables false in
/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- The first bulk straight-line subset. Every local binding is a Word binding; Boolean terms,
    comparisons, conditionals, effects, and recursion are deliberately absent. -/
inductive WordOnly : {context : List ValueSort} →
    {source : Structured.Expr context .word} → Type where
  | var (ref : Var context .word) : WordOnly (source := .var ref)
  | wordLit (value : UInt64) : WordOnly (source := .wordLit value)
  | add : WordOnly (source := lhs) → WordOnly (source := rhs) →
      WordOnly (source := .add lhs rhs)
  | sub : WordOnly (source := lhs) → WordOnly (source := rhs) →
      WordOnly (source := .sub lhs rhs)
  | bitAnd : WordOnly (source := lhs) → WordOnly (source := rhs) →
      WordOnly (source := .bitAnd lhs rhs)
  | letE : WordOnly (source := value) → WordOnly (source := body) →
      WordOnly (source := .letE value body)

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
structure Selected {context : List ValueSort} (source : Structured.Expr context .word) where
  proof : WordOnly (source := source)

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Structural recognition only: unsupported terms are rejected rather than normalized. -/
def select : (source : Structured.Expr context .word) → Option (Selected source)
  | .var ref => some ⟨.var ref⟩
  | .wordLit value => some ⟨.wordLit value⟩
  | .add lhs rhs =>
      match select lhs, select rhs with
      | some lhsSelected, some rhsSelected =>
          some ⟨.add lhsSelected.proof rhsSelected.proof⟩
      | _, _ => none
  | .sub lhs rhs =>
      match select lhs, select rhs with
      | some lhsSelected, some rhsSelected =>
          some ⟨.sub lhsSelected.proof rhsSelected.proof⟩
      | _, _ => none
  | .bitAnd lhs rhs =>
      match select lhs, select rhs with
      | some lhsSelected, some rhsSelected =>
          some ⟨.bitAnd lhsSelected.proof rhsSelected.proof⟩
      | _, _ => none
  | .letE (bound := .word) value body =>
      match select value, select body with
      | some valueSelected, some bodySelected =>
          some ⟨.letE valueSelected.proof bodySelected.proof⟩
      | _, _ => none
  | .letE (bound := .bool) _ _ => none
  | .ite _ _ _ => none

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- A temporary is indexed by the exact semantic value it denotes. The newest temporary is at
    index zero; `older` is the only way to refer through a later definition. -/
inductive TempRef : List (Args → UInt64) → (Args → UInt64) → Type where
  | newest : TempRef (value :: older) value
  | older : TempRef older value → TempRef (newer :: older) value

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Inputs, exact constants, and already-defined structurally scoped temporaries. -/
inductive Operand (temps : List (Args → UInt64)) : (Args → UInt64) → Type where
  | a0 : Operand temps (fun args => args.a0)
  | a1 : Operand temps (fun args => args.a1)
  | a2 : Operand temps (fun args => args.a2)
  | a3 : Operand temps (fun args => args.a3)
  | constant (value : UInt64) : Operand temps (fun _ => value)
  | temp (ref : TempRef temps value) : Operand temps value

namespace Operand

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
def weaken (operand : Operand temps value) : Operand (newer :: temps) value :=
  match operand with
  | .a0 => .a0
  | .a1 => .a1
  | .a2 => .a2
  | .a3 => .a3
  | .constant value => .constant value
  | .temp ref => .temp (.older ref)

end Operand

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- One portable operation. Its result index states the exact wrapping UInt64 function computed
    from its operands. -/
inductive Instruction (temps : List (Args → UInt64)) : (Args → UInt64) → Type where
  | add (lhs : Operand temps lhsValue) (rhs : Operand temps rhsValue) :
      Instruction temps (fun args => lhsValue args + rhsValue args)
  | sub (lhs : Operand temps lhsValue) (rhs : Operand temps rhsValue) :
      Instruction temps (fun args => lhsValue args - rhsValue args)
  | bitAnd (lhs : Operand temps lhsValue) (rhs : Operand temps rhsValue) :
      Instruction temps (fun args => lhsValue args &&& rhsValue args)

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- A forward straight-line plan. `emit` extends the temporary scope before the remainder, making
    dangling and forward temporary references unconstructible. -/
inductive Code : (temps : List (Args → UInt64)) → (Args → UInt64) → Type where
  | done (result : Operand temps value) : Code temps value
  | emit (instruction : Instruction temps value) (rest : Code (value :: temps) result) :
      Code temps result

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
def Code.instructionCount : Code temps result → Nat
  | .done _ => 0
  | .emit _ rest => rest.instructionCount + 1

private abbrev SourceSemantics (context : List ValueSort) :=
  {kind : ValueSort} → Var context kind → Args → kind.Denote

private def sourceEnv (semantics : SourceSemantics context) (args : Args) : Env context
  | _, ref => semantics ref args

private abbrev SourceOperands (semantics : SourceSemantics context)
    (temps : List (Args → UInt64)) :=
  (ref : Var context .word) → Operand temps (semantics ref)

private def SourceOperands.weaken
    (operands : SourceOperands semantics temps) : SourceOperands semantics (newer :: temps) :=
  fun ref => (operands ref).weaken

private def SourceSemantics.consWord (value : Args → UInt64)
    (semantics : SourceSemantics context) : SourceSemantics (.word :: context)
  | _, .zero => value
  | _, .succ ref => semantics ref

private def SourceOperands.consWord
    (value : Operand temps valueSemantics) (operands : SourceOperands semantics temps) :
    SourceOperands (SourceSemantics.consWord valueSemantics semantics) temps
  | .zero => value
  | .succ ref => operands ref

private def SourceOperands.tailWord
    (operands : SourceOperands (SourceSemantics.consWord value semantics) temps) :
    SourceOperands semantics temps :=
  fun ref => operands (.succ ref)

private abbrev OperandMap (sourceTemps targetTemps : List (Args → UInt64)) :=
  {value : Args → UInt64} → Operand sourceTemps value → Operand targetTemps value

private def OperandMap.identity : OperandMap temps temps := fun operand => operand

private def OperandMap.then (first : OperandMap start middle) (second : OperandMap middle finish) :
    OperandMap start finish := fun operand => second (first operand)

private def OperandMap.afterEmit (map : OperandMap start finish) :
    OperandMap start (newer :: finish) := fun operand => (map operand).weaken

private theorem sourceEnv_consWord (semantics : SourceSemantics context)
    (value : Args → UInt64) (args : Args) :
    (sourceEnv (semantics.consWord value) args : Env (.word :: context)) =
      (Env.cons (value args) (sourceEnv semantics args) : Env (.word :: context)) := by
  funext kind ref
  cases ref <;> rfl

private def compileCps {context : List ValueSort}
    {source : Structured.Expr context .word} (selected : WordOnly (source := source))
    (semantics : SourceSemantics context) (operands : SourceOperands semantics temps)
    (continuation : ∀ {currentTemps},
      OperandMap temps currentTemps →
      SourceOperands semantics currentTemps →
      Operand currentTemps (fun args => source.eval (sourceEnv semantics args)) →
      Code currentTemps result) : Code temps result :=
  match selected with
  | .var ref => continuation OperandMap.identity operands (operands ref)
  | .wordLit value => continuation OperandMap.identity operands (.constant value)
  | .add lhsSelected rhsSelected =>
      compileCps lhsSelected semantics operands (fun lhsMap lhsOperands lhs =>
        compileCps rhsSelected semantics lhsOperands (fun rhsMap rhsOperands rhs =>
          .emit (.add (rhsMap lhs) rhs)
            (continuation (OperandMap.afterEmit (OperandMap.then lhsMap rhsMap)) rhsOperands.weaken
              (.temp .newest))))
  | .sub lhsSelected rhsSelected =>
      compileCps lhsSelected semantics operands (fun lhsMap lhsOperands lhs =>
        compileCps rhsSelected semantics lhsOperands (fun rhsMap rhsOperands rhs =>
          .emit (.sub (rhsMap lhs) rhs)
            (continuation (OperandMap.afterEmit (OperandMap.then lhsMap rhsMap)) rhsOperands.weaken
              (.temp .newest))))
  | .bitAnd lhsSelected rhsSelected =>
      compileCps lhsSelected semantics operands (fun lhsMap lhsOperands lhs =>
        compileCps rhsSelected semantics lhsOperands (fun rhsMap rhsOperands rhs =>
          .emit (.bitAnd (rhsMap lhs) rhs)
            (continuation (OperandMap.afterEmit (OperandMap.then lhsMap rhsMap)) rhsOperands.weaken
              (.temp .newest))))
  | .letE valueSelected bodySelected =>
      compileCps valueSelected semantics operands (fun valueMap valueOperands value =>
        compileCps bodySelected (semantics.consWord _) (valueOperands.consWord value)
          (fun bodyMap bodyOperands resultOperand => by
            apply continuation (valueMap.then bodyMap) bodyOperands.tailWord
            simpa only [Structured.Expr.eval, sourceEnv_consWord] using resultOperand))

private def inputSemantics : SourceSemantics InputContext :=
  fun ref args => InputContext.env args ref

private def inputOperands : SourceOperands inputSemantics []
  | .zero => .a0
  | .succ .zero => .a1
  | .succ (.succ .zero) => .a2
  | .succ (.succ (.succ .zero)) => .a3

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Compile a selected source into a temporary-safe portable plan. The result semantic function is
    definitionally tied to the original source evaluator. -/
def compile {source : Structured.Expr InputContext .word}
    (selected : WordOnly (source := source)) :
    Code [] (fun args => source.eval (InputContext.env args)) :=
  compileCps selected inputSemantics inputOperands (fun _ _ result => .done result)

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
def compile? (source : Structured.Expr InputContext .word) :
    Option (Code [] (fun args => source.eval (InputContext.env args))) :=
  (select source).map (fun selected => compile selected.proof)

private abbrev RuntimeTemps (temps : List (Args → UInt64)) :=
  {value : Args → UInt64} → TempRef temps value → UInt64

private def RuntimeTemps.cons (value : UInt64) (older : RuntimeTemps temps) :
    RuntimeTemps (semantics :: temps)
  | _, .newest => value
  | _, .older ref => older ref

private def Operand.run (operand : Operand temps value) (args : Args)
    (runtime : RuntimeTemps temps) : UInt64 :=
  match operand with
  | .a0 => args.a0
  | .a1 => args.a1
  | .a2 => args.a2
  | .a3 => args.a3
  | .constant value => value
  | .temp ref => runtime ref

private def Instruction.run (instruction : Instruction temps value) (args : Args)
    (runtime : RuntimeTemps temps) : UInt64 :=
  match instruction with
  | .add lhs rhs => lhs.run args runtime + rhs.run args runtime
  | .sub lhs rhs => lhs.run args runtime - rhs.run args runtime
  | .bitAnd lhs rhs => lhs.run args runtime &&& rhs.run args runtime

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Total local interpreter for a portable plan. This is source/IR semantics, not target execution. -/
def Code.run (code : Code temps result) (args : Args) (runtime : RuntimeTemps temps) : UInt64 :=
  match code with
  | .done operand => operand.run args runtime
  | .emit instruction rest =>
      rest.run args (RuntimeTemps.cons (instruction.run args runtime) runtime)

private def RuntimeTemps.Sound (args : Args) (runtime : RuntimeTemps temps) : Prop :=
  ∀ {value} (ref : TempRef temps value), runtime ref = value args

private theorem Operand.run_eq (operand : Operand temps value) (args : Args)
    (runtime : RuntimeTemps temps) (sound : runtime.Sound args) :
    operand.run args runtime = value args := by
  cases operand <;> simp [Operand.run]
  case temp ref => exact sound ref

private theorem Instruction.run_eq (instruction : Instruction temps value) (args : Args)
    (runtime : RuntimeTemps temps) (sound : runtime.Sound args) :
    instruction.run args runtime = value args := by
  cases instruction <;> simp [Instruction.run, Operand.run_eq _ args runtime sound]

private theorem RuntimeTemps.sound_cons (args : Args) (runtime : RuntimeTemps temps)
    (sound : runtime.Sound args) (value : UInt64) (exact : value = semantics args) :
    RuntimeTemps.Sound args (RuntimeTemps.cons (semantics := semantics) value runtime) := by
  intro denotation ref
  cases ref with
  | newest => exact exact
  | older ref => exact sound ref

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
theorem Code.run_eq {result : Args → UInt64} (code : Code temps result) (args : Args)
    (runtime : RuntimeTemps temps)
    (sound : runtime.Sound args) : code.run args runtime = result args :=
  match code with
  | .done operand => operand.run_eq args runtime sound
  | .emit instruction rest =>
      rest.run_eq args (RuntimeTemps.cons (instruction.run args runtime) runtime)
        (RuntimeTemps.sound_cons args runtime sound _
          (instruction.run_eq args runtime sound))

private def emptyRuntime : RuntimeTemps [] := by
  intro value ref
  cases ref

private theorem emptyRuntime_sound (args : Args) : emptyRuntime.Sound args := by
  intro value ref
  cases ref

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Interpret a closed generated plan from its intrinsically empty temporary scope. -/
def Code.runClosed (code : Code [] result) (args : Args) : UInt64 :=
  code.run args emptyRuntime

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Every generated or handwritten well-typed closed plan computes its semantic result index. -/
theorem Code.runClosed_eq (code : Code [] result) (args : Args) :
    code.runClosed args = result args :=
  code.run_eq args emptyRuntime (emptyRuntime_sound args)

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Kernel-checked semantic refinement from every generated plan to its exact structured source. -/
theorem compile_correct {source : Structured.Expr InputContext .word}
    (selected : WordOnly (source := source)) (args : Args) :
    (compile selected).runClosed args = source.eval (InputContext.env args) :=
  (compile selected).runClosed_eq args

/- REF: docs/MACRO_ASSEMBLER.md#structured-straight-line-plans -/
/-- Compose portable lowering with the existing kernel-checked reifier contract. This connects the
    plan to the exact Lean function named by `source.fn`, without adding target authority. -/
theorem compileFunction_correct (source : Structured.WordFunction)
    (selected : WordOnly (source := source.body)) (args : Args) :
    (compile selected).runClosed args = source.fn args := by
  rw [compile_correct, ← source.implements]

end Gasm.Compiler.Word.StructuredStraightLine

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

import Gasm.Compiler.Word

namespace Gasm.Compiler.Word.Structured

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- The semantic types selected by the first structured Word source language. -/
inductive ValueSort where
  | word
  | bool
  deriving DecidableEq, Repr

namespace ValueSort

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Total host interpretation of a structured source sort. -/
abbrev Denote : ValueSort → Type
  | .word => UInt64
  | .bool => Bool

end ValueSort

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Intrinsically typed de Bruijn membership in a local source context. -/
inductive Var : List ValueSort → ValueSort → Type
  | zero : Var (kind :: context) kind
  | succ : Var context kind → Var (head :: context) kind
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- A total typed environment for every variable in a source context. -/
abbrev Env (context : List ValueSort) := {kind : ValueSort} → Var context kind → kind.Denote

namespace Env

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Extend a typed environment for the body of a `letE`. -/
def cons {context : List ValueSort} {kind : ValueSort} (value : kind.Denote) (env : Env context) :
    Env (kind :: context)
  | _, .zero => value
  | _, .succ ref => env ref

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem cons_zero {context : List ValueSort} {kind : ValueSort}
    (value : kind.Denote) (env : Env context) :
    cons value env (.zero : Var (kind :: context) kind) = value := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem cons_succ {context : List ValueSort} {kind head : ValueSort}
    (value : head.Denote) (env : Env context) (ref : Var context kind) :
    cons value env (.succ ref : Var (head :: context) kind) = env ref := rfl

end Env

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Intrinsically typed and scoped structured Word expressions. Boolean conjunction/disjunction,
    signed interpretations, effects, and recursion are intentionally absent. -/
inductive Expr : List ValueSort → ValueSort → Type where
  | var (ref : Var context kind) : Expr context kind
  | wordLit (value : UInt64) : Expr context .word
  | boolLit (value : Bool) : Expr context .bool
  | add (lhs rhs : Expr context .word) : Expr context .word
  | sub (lhs rhs : Expr context .word) : Expr context .word
  | bitAnd (lhs rhs : Expr context .word) : Expr context .word
  | eq (lhs rhs : Expr context .word) : Expr context .bool
  | ult (lhs rhs : Expr context .word) : Expr context .bool
  | not (value : Expr context .bool) : Expr context .bool
  | letE (value : Expr context bound) (body : Expr (bound :: context) result) :
      Expr context result
  | ite (condition : Expr context .bool) (ifTrue ifFalse : Expr context result) :
      Expr context result
  deriving DecidableEq, Repr

namespace Expr

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Total structural semantics. `letE` extends the typed environment; `ite` evaluates only its
    selected branch. -/
def eval {context : List ValueSort} {kind : ValueSort} (expression : Expr context kind)
    (env : Env context) : kind.Denote :=
  match expression with
  | .var ref => env ref
  | .wordLit value => value
  | .boolLit value => value
  | .add lhs rhs => lhs.eval env + rhs.eval env
  | .sub lhs rhs => lhs.eval env - rhs.eval env
  | .bitAnd lhs rhs => lhs.eval env &&& rhs.eval env
  | .eq lhs rhs => lhs.eval env == rhs.eval env
  | .ult lhs rhs => decide (lhs.eval env < rhs.eval env)
  | .not value => !value.eval env
  | .letE value body => body.eval (Env.cons (value.eval env) env)
  | .ite condition ifTrue ifFalse =>
      if condition.eval env then ifTrue.eval env else ifFalse.eval env

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_var (ref : Var context kind) (env : Env context) :
    (Expr.var ref).eval env = env ref := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_wordLit (value : UInt64) (env : Env context) :
    (Expr.wordLit value).eval env = value := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_boolLit (value : Bool) (env : Env context) :
    (Expr.boolLit value).eval env = value := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_add (lhs rhs : Expr context .word) (env : Env context) :
    (Expr.add lhs rhs).eval env = lhs.eval env + rhs.eval env := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_sub (lhs rhs : Expr context .word) (env : Env context) :
    (Expr.sub lhs rhs).eval env = lhs.eval env - rhs.eval env := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_bitAnd (lhs rhs : Expr context .word) (env : Env context) :
    (Expr.bitAnd lhs rhs).eval env = (lhs.eval env &&& rhs.eval env) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_eq (lhs rhs : Expr context .word) (env : Env context) :
    (Expr.eq lhs rhs).eval env = (lhs.eval env == rhs.eval env) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_ult (lhs rhs : Expr context .word) (env : Env context) :
    (Expr.ult lhs rhs).eval env = decide (lhs.eval env < rhs.eval env) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_not (value : Expr context .bool) (env : Env context) :
    (Expr.not value).eval env = !value.eval env := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_letE (value : Expr context bound)
    (body : Expr (bound :: context) result) (env : Env context) :
    (Expr.letE value body).eval env = body.eval (Env.cons (value.eval env) env) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_ite (condition : Expr context .bool)
    (ifTrue ifFalse : Expr context result) (env : Env context) :
    (Expr.ite condition ifTrue ifFalse).eval env =
      if condition.eval env then ifTrue.eval env else ifFalse.eval env := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Word inequality is derived from equality and Boolean negation. -/
def ne (lhs rhs : Expr context .word) : Expr context .bool :=
  .not (.eq lhs rhs)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Unsigned less-than-or-equal is derived by reversing and negating unsigned less-than. -/
def ule (lhs rhs : Expr context .word) : Expr context .bool :=
  .not (.ult rhs lhs)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Unsigned greater-than is reversed unsigned less-than. -/
def ugt (lhs rhs : Expr context .word) : Expr context .bool :=
  .ult rhs lhs

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Unsigned greater-than-or-equal is negated unsigned less-than. -/
def uge (lhs rhs : Expr context .word) : Expr context .bool :=
  .not (.ult lhs rhs)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_ne (lhs rhs : Expr context .word) (env : Env context) :
    (ne lhs rhs).eval env = !(lhs.eval env == rhs.eval env) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_ule (lhs rhs : Expr context .word) (env : Env context) :
    (ule lhs rhs).eval env = !(decide (rhs.eval env < lhs.eval env)) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_ugt (lhs rhs : Expr context .word) (env : Env context) :
    (ugt lhs rhs).eval env = decide (rhs.eval env < lhs.eval env) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem eval_uge (lhs rhs : Expr context .word) (env : Env context) :
    (uge lhs rhs).eval env = !(decide (lhs.eval env < rhs.eval env)) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
theorem eval_ne_eq_true_iff (lhs rhs : Expr context .word) (env : Env context) :
    (ne lhs rhs).eval env = true ↔ lhs.eval env ≠ rhs.eval env := by
  simp

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
theorem eval_ule_eq_true_iff (lhs rhs : Expr context .word) (env : Env context) :
    (ule lhs rhs).eval env = true ↔ lhs.eval env ≤ rhs.eval env := by
  simp [ule, eval]

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
theorem eval_ugt_eq_true_iff (lhs rhs : Expr context .word) (env : Env context) :
    (ugt lhs rhs).eval env = true ↔ rhs.eval env < lhs.eval env := by
  simp

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
theorem eval_uge_eq_true_iff (lhs rhs : Expr context .word) (env : Env context) :
    (uge lhs rhs).eval env = true ↔ rhs.eval env ≤ lhs.eval env := by
  simp [uge, eval]

end Expr

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- The current structured frontend starts with exactly the same four Word arguments as the
    straight-line leaf compiler. Local bindings extend this context intrinsically. -/
abbrev InputContext : List ValueSort := [.word, .word, .word, .word]

namespace InputContext

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def a0 : Var InputContext .word := .zero

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def a1 : Var InputContext .word := .succ .zero

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def a2 : Var InputContext .word := .succ (.succ .zero)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def a3 : Var InputContext .word := .succ (.succ (.succ .zero))

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Interpret the fixed source context from the existing portable argument record. -/
def env (args : Args) : Env InputContext
  | _, .zero => args.a0
  | _, .succ .zero => args.a1
  | _, .succ (.succ .zero) => args.a2
  | _, .succ (.succ (.succ .zero)) => args.a3

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem env_a0 (args : Args) : env args a0 = args.a0 := rfl
/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem env_a1 (args : Args) : env args a1 = args.a1 := rfl
/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem env_a2 (args : Args) : env args a2 = args.a2 := rfl
/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
@[simp] theorem env_a3 (args : Args) : env args a3 = args.a3 := rfl

end InputContext

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- A Lean function tied to intrinsically typed structured source by a kernel-checked extensional
    equality. Current machine backends consume the separate straight-line `Word.Function`; they do
    not yet consume either structured result alias. -/
structure Function (result : ValueSort) where
  fn : Args → result.Denote
  body : Expr InputContext result
  implements : ∀ args, fn args = body.eval (InputContext.env args)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- The structured result selected for a future proved lowering into certified leaf payloads and
    typed control flow. -/
abbrev WordFunction := Function .word

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Boolean-result functions can specify branch conditions but are not callable/exportable through
    the current machine backends. -/
abbrev BoolFunction := Function .bool

end Gasm.Compiler.Word.Structured

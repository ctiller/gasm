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

namespace Gasm.Compiler.Word

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
/-- The portable calling-convention-independent input to the initial compiler subset. -/
structure Args where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
@[ext] theorem Args.ext {x y : Args}
    (h0 : x.a0 = y.a0) (h1 : x.a1 = y.a1)
    (h2 : x.a2 = y.a2) (h3 : x.a3 = y.a3) : x = y := by
  cases x; cases y; simp_all

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
inductive Arg where
  | a0 | a1 | a2 | a3
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
def Args.get (args : Args) : Arg → UInt64
  | .a0 => args.a0
  | .a1 => args.a1
  | .a2 => args.a2
  | .a3 => args.a3

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
inductive Atom where
  | arg (index : Arg)
  | const (value : UInt64)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
def Atom.eval (atom : Atom) (args : Args) : UInt64 :=
  match atom with
  | .arg index => args.get index
  | .const value => value

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
inductive BinOp where
  | add | sub | bitAnd
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
def BinOp.eval : BinOp → UInt64 → UInt64 → UInt64
  | .add => (· + ·)
  | .sub => (· - ·)
  | .bitAnd => (· &&& ·)

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
/-- A deliberately small, total source language: atoms and one binary word operation. This is the
    supported reifiable subset; adding let-bindings and control flow can extend it without changing
    the backend interface. -/
inductive Expr where
  | atom (value : Atom)
  | binary (op : BinOp) (lhs rhs : Atom)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#portable-source-language -/
def Expr.eval : Expr → Args → UInt64
  | .atom value, args => value.eval args
  | .binary op lhs rhs, args => op.eval (lhs.eval args) (rhs.eval args)

/- REF: docs/MACRO_ASSEMBLER.md#lean-functions -/
/-- A real Lean function accompanied by reifiable source and a proof that the two agree. This
    avoids claiming that Lean can inspect an arbitrary opaque function after elaboration. -/
structure Function where
  fn : Args → UInt64
  body : Expr
  implements : ∀ args, fn args = body.eval args

/- REF: docs/MACRO_ASSEMBLER.md#lean-functions -/
def Function.ofExpr (body : Expr) : Function where
  fn := body.eval
  body := body
  implements := by intro; rfl

/- REF: docs/MACRO_ASSEMBLER.md#portable-macro-ir -/
inductive Op where
  | load (value : Atom)
  | combine (op : BinOp) (rhs : Atom)
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MACRO_ASSEMBLER.md#portable-macro-ir -/
def Op.eval (op : Op) (args : Args) (acc : UInt64) : UInt64 :=
  match op with
  | .load value => value.eval args
  | .combine kind rhs => kind.eval acc (rhs.eval args)

/- REF: docs/MACRO_ASSEMBLER.md#portable-macro-ir -/
def run (program : List Op) (args : Args) : UInt64 :=
  program.foldl (fun acc op => op.eval args acc) 0

/- REF: docs/MACRO_ASSEMBLER.md#portable-macro-ir -/
/-- Bulk compilation to portable macros, before any register or ISA choice is made. -/
def compileExpr : Expr → List Op
  | .atom value => [.load value]
  | .binary op lhs rhs => [.load lhs, .combine op rhs]

/- REF: docs/MACRO_ASSEMBLER.md#portable-macro-ir -/
theorem compileExpr_correct (expr : Expr) (args : Args) :
    run (compileExpr expr) args = expr.eval args := by
  cases expr <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#portable-macro-ir -/
theorem compileFunction_correct (f : Function) (args : Args) :
    run (compileExpr f.body) args = f.fn args := by
  rw [compileExpr_correct, f.implements]

end Gasm.Compiler.Word

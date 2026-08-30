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
import Gasm.Compiler.Word

namespace Gasm.Compiler.Word.LeanReify

open Lean Elab Command Meta

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
/-- The syntax produced for a supported atom. The elaborator remains outside the trusted proof
    boundary: the generated `Function.implements` term must still pass the kernel. -/
private structure ReifiedAtom where
  term : Term

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
/-- The syntax and kernel proof syntax generated for one supported declaration body. -/
private structure ReifiedBody where
  term : Term
  proof : Term

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def uint64Type : Lean.Expr := mkConst ``UInt64

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def sameFVar (candidate expected : Lean.Expr) : Bool :=
  match candidate.fvarId?, expected.fvarId? with
  | some candidateId, some expectedId => candidateId == expectedId
  | _, _ => false

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def argSyntax (index : Nat) : MetaM Term :=
  match index with
  | 0 => `(Gasm.Compiler.Word.Atom.arg .a0)
  | 1 => `(Gasm.Compiler.Word.Atom.arg .a1)
  | 2 => `(Gasm.Compiler.Word.Atom.arg .a2)
  | 3 => `(Gasm.Compiler.Word.Atom.arg .a3)
  | _ => throwError "internal Word reifier error: argument index {index} is outside Fin 4"

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def literalSyntax? (expression : Lean.Expr) : Option Term := do
  guard expression.isApp
  guard (expression.getAppFn.isConstOf ``OfNat.ofNat = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 3)
  guard (arguments[0]!.isConstOf ``UInt64 = true)
  guard (arguments[2]!.isAppOf ``UInt64.instOfNat = true)
  let .lit (.natVal value) := arguments[1]! | none
  some ⟨Syntax.mkNumLit value.repr⟩

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def reifyAtom (expression : Lean.Expr) (arguments : Array Lean.Expr) : MetaM ReifiedAtom := do
  for index in [:arguments.size] do
    if sameFVar expression arguments[index]! then
      return ⟨← argSyntax index⟩
  if let some literal := literalSyntax? expression then
    return ⟨← `(Gasm.Compiler.Word.Atom.const $literal)⟩
  let rendered ← ppExpr expression
  throwError "unsupported Word atom `{rendered}`; expected one of the four arguments or a UInt64 literal"

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def binaryKind? (expression : Lean.Expr) : Option (Term × Lean.Expr × Lean.Expr) := do
  guard expression.isApp
  let head := expression.getAppFn
  let arguments := expression.getAppArgs
  guard (arguments.size == 6)
  guard (arguments[0]!.isConstOf ``UInt64 = true)
  guard (arguments[1]!.isConstOf ``UInt64 = true)
  guard (arguments[2]!.isConstOf ``UInt64 = true)
  if head.isConstOf ``HAdd.hAdd then
    let instanceArguments := arguments[3]!.getAppArgs
    guard (arguments[3]!.isAppOf ``instHAdd = true)
    guard (instanceArguments.size == 2)
    guard (instanceArguments[0]!.isConstOf ``UInt64 = true)
    guard (instanceArguments[1]!.isConstOf ``instAddUInt64 = true)
    some (⟨mkIdent ``Gasm.Compiler.Word.BinOp.add⟩, arguments[4]!, arguments[5]!)
  else if head.isConstOf ``HSub.hSub then
    let instanceArguments := arguments[3]!.getAppArgs
    guard (arguments[3]!.isAppOf ``instHSub = true)
    guard (instanceArguments.size == 2)
    guard (instanceArguments[0]!.isConstOf ``UInt64 = true)
    guard (instanceArguments[1]!.isConstOf ``instSubUInt64 = true)
    some (⟨mkIdent ``Gasm.Compiler.Word.BinOp.sub⟩, arguments[4]!, arguments[5]!)
  else if head.isConstOf ``HAnd.hAnd then
    let instanceArguments := arguments[3]!.getAppArgs
    guard (arguments[3]!.isAppOf ``instHAndOfAndOp = true)
    guard (instanceArguments.size == 2)
    guard (instanceArguments[0]!.isConstOf ``UInt64 = true)
    guard (instanceArguments[1]!.isConstOf ``instAndOpUInt64 = true)
    some (⟨mkIdent ``Gasm.Compiler.Word.BinOp.bitAnd⟩, arguments[4]!, arguments[5]!)
  else
    none

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def reifyBody (expression : Lean.Expr) (arguments : Array Lean.Expr) : MetaM ReifiedBody := do
  let bodySyntax ←
    if let some (kind, lhs, rhs) := binaryKind? expression then
      let lhs ← reifyAtom lhs arguments
      let rhs ← reifyAtom rhs arguments
      `(Gasm.Compiler.Word.Expr.binary $kind $(lhs.term) $(rhs.term))
    else
      let atom ← reifyAtom expression arguments
      `(Gasm.Compiler.Word.Expr.atom $(atom.term))
  let proof ← `(by intro args; rfl)
  pure { term := bodySyntax, proof := proof }

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def checkArgumentType (argument : Lean.Expr) : MetaM Unit := do
  let type ← inferType argument
  unless ← isDefEq type uint64Type do
    throwError "Word reification requires every argument to have type UInt64, but found `{← ppExpr type}`"

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
private def reifyDeclaration (declaration : Name) : MetaM ReifiedBody := do
  let info ← getConstInfo declaration
  let some value := info.value? |
    throwError "Word reification requires a reducible declaration with a kernel-visible body"
  lambdaTelescope value fun arguments body => do
    unless arguments.size == 4 do
      throwError "Word reification requires exactly four explicit UInt64 arguments; found {arguments.size}"
    for argument in arguments do
      let declaration ← argument.fvarId!.getDecl
      unless declaration.binderInfo == .default do
        throwError "Word reification requires four explicit arguments; `{declaration.userName}` is not explicit"
      checkArgumentType argument
    let resultType ← inferType body
    unless ← isDefEq resultType uint64Type do
      throwError "Word reification requires a UInt64 result, but found `{← ppExpr resultType}`"
    reifyBody body arguments

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
syntax (name := wordReifyCmd) "#word_reify " ident " as " ident : command

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
elab_rules : command
  | `(command| #word_reify $original:ident as $generated:ident) => do
      let declaration ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo original
      let reified ← liftTermElabM <| reifyDeclaration declaration
      let originalName := mkIdent declaration
      let command ← `(def $generated : Gasm.Compiler.Word.Function where
        fn := fun args => $originalName args.a0 args.a1 args.a2 args.a3
        body := $(reified.term)
        implements := $(reified.proof))
      withRef original <| elabCommand command

end Gasm.Compiler.Word.LeanReify

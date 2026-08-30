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
import Gasm.Compiler.Word.Structured

namespace Gasm.Compiler.Word.StructuredLeanReify

open Lean Elab Command Meta

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private inductive SourceSort where
  | word
  | bool
  deriving BEq

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private structure Local where
  expression : Lean.Expr
  sort : SourceSort

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def typeExpression : SourceSort → Lean.Expr
  | .word => mkConst ``UInt64
  | .bool => mkConst ``Bool

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def sameExpression (lhs rhs : Lean.Expr) : Bool := lhs == rhs

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def sameFVar (candidate expected : Lean.Expr) : Bool :=
  match candidate.fvarId?, expected.fvarId? with
  | some candidateId, some expectedId => candidateId == expectedId
  | _, _ => false

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def ensureType (expression : Lean.Expr) (expected : SourceSort) : MetaM Unit := do
  let actual ← inferType expression
  unless actual.isConstOf (typeExpression expected).constName! do
    throwError "structured Word reification expected `{← ppExpr (typeExpression expected)}` but term \
      `{← ppExpr expression}` has inferred type `{← ppExpr actual}`"

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def unsupported (expression : Lean.Expr) : MetaM α := do
  let type ← inferType expression
  throwError "unsupported structured Word term `{← ppExpr expression}` with inferred type \
    `{← ppExpr type}`"

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def varSyntax : Nat → MetaM Term
  | 0 => `(Gasm.Compiler.Word.Structured.Var.zero)
  | index + 1 => do
      let previous ← varSyntax index
      `(Gasm.Compiler.Word.Structured.Var.succ $previous)

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def variableSyntax? (expression : Lean.Expr) (expected : SourceSort)
    (locals : Array Local) : MetaM (Option Term) := do
  for index in [:locals.size] do
    let some boundLocal := locals[index]? |
      throwError "internal structured Word reifier local index {index} is out of bounds"
    if sameFVar expression boundLocal.expression then
      unless boundLocal.sort == expected do
        throwError "internal structured Word reifier sort mismatch for `{← ppExpr expression}`"
      let ref ← varSyntax index
      return some (← `(Gasm.Compiler.Word.Structured.Expr.var $ref))
  pure none

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def uint64LiteralSyntax? (expression : Lean.Expr) : Option Term := do
  guard expression.isApp
  guard (expression.getAppFn.isConstOf ``OfNat.ofNat = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 3)
  guard (arguments[0]!.isConstOf ``UInt64 = true)
  guard (arguments[2]!.isAppOf ``UInt64.instOfNat = true)
  let .lit (.natVal value) := arguments[1]! | none
  some ⟨Syntax.mkNumLit value.repr⟩

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def uint64Binary? (expression : Lean.Expr) : Option (Name × Lean.Expr × Lean.Expr) := do
  guard expression.isApp
  let head := expression.getAppFn
  let arguments := expression.getAppArgs
  guard (arguments.size == 6)
  guard (arguments[0]!.isConstOf ``UInt64 = true)
  guard (arguments[1]!.isConstOf ``UInt64 = true)
  guard (arguments[2]!.isConstOf ``UInt64 = true)
  let operationInstance := arguments[3]!
  let instanceArguments := operationInstance.getAppArgs
  guard (instanceArguments.size == 2)
  guard (instanceArguments[0]!.isConstOf ``UInt64 = true)
  if head.isConstOf ``HAdd.hAdd && operationInstance.isAppOf ``instHAdd &&
      instanceArguments[1]!.isConstOf ``instAddUInt64 then
    some (``Gasm.Compiler.Word.Structured.Expr.add, arguments[4]!, arguments[5]!)
  else if head.isConstOf ``HSub.hSub && operationInstance.isAppOf ``instHSub &&
      instanceArguments[1]!.isConstOf ``instSubUInt64 then
    some (``Gasm.Compiler.Word.Structured.Expr.sub, arguments[4]!, arguments[5]!)
  else if head.isConstOf ``HAnd.hAnd && operationInstance.isAppOf ``instHAndOfAndOp &&
      instanceArguments[1]!.isConstOf ``instAndOpUInt64 then
    some (``Gasm.Compiler.Word.Structured.Expr.bitAnd, arguments[4]!, arguments[5]!)
  else
    none

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def uint64Eq? (expression : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  guard (expression.isAppOf ``BEq.beq = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 4)
  guard (arguments[0]!.isConstOf ``UInt64 = true)
  let equalityInstance := arguments[1]!
  guard (equalityInstance.isAppOf ``instBEqOfDecidableEq = true)
  let instanceArguments := equalityInstance.getAppArgs
  guard (instanceArguments.size == 2)
  guard (instanceArguments[0]!.isConstOf ``UInt64 = true)
  guard (instanceArguments[1]!.isConstOf ``instDecidableEqUInt64 = true)
  some (arguments[2]!, arguments[3]!)

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def uint64LtProp? (expression : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  guard (expression.isAppOf ``LT.lt = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 4)
  guard (arguments[0]!.isConstOf ``UInt64 = true)
  guard (arguments[1]!.isConstOf ``instLTUInt64 = true)
  some (arguments[2]!, arguments[3]!)

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def uint64Ult? (expression : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  guard (expression.isAppOf ``Decidable.decide = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 2)
  let some (lhs, rhs) := uint64LtProp? arguments[0]! | none
  let decision := arguments[1]!
  guard (decision.isAppOf ``UInt64.decLt = true)
  let decisionArguments := decision.getAppArgs
  guard (decisionArguments.size == 2)
  guard (sameExpression decisionArguments[0]! lhs)
  guard (sameExpression decisionArguments[1]! rhs)
  some (lhs, rhs)

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def boolNot? (expression : Lean.Expr) : Option Lean.Expr := do
  guard (expression.isAppOf ``Bool.not = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 1)
  some arguments[0]!

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def boolCondition? (proposition decision : Lean.Expr) : Option Lean.Expr := do
  guard (proposition.isAppOf ``Eq = true)
  let arguments := proposition.getAppArgs
  guard (arguments.size == 3)
  guard (arguments[0]!.isConstOf ``Bool = true)
  guard (arguments[2]!.isConstOf ``Bool.true = true)
  guard (decision.isAppOf ``instDecidableEqBool = true)
  let decisionArguments := decision.getAppArgs
  guard (decisionArguments.size == 2)
  guard (sameExpression decisionArguments[0]! arguments[1]!)
  guard (decisionArguments[1]!.isConstOf ``Bool.true = true)
  some arguments[1]!

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def iteParts? (expression : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) := do
  guard (expression.isAppOf ``ite = true)
  let arguments := expression.getAppArgs
  guard (arguments.size == 5)
  let some condition := boolCondition? arguments[1]! arguments[2]! | none
  some (condition, arguments[3]!, arguments[4]!)

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def expressionSize : Lean.Expr → Nat
  | .app fn argument => expressionSize fn + expressionSize argument + 1
  | .lam _ type body _ => expressionSize type + expressionSize body + 1
  | .forallE _ type body _ => expressionSize type + expressionSize body + 1
  | .letE _ type value body _ =>
      expressionSize type + expressionSize value + expressionSize body + 1
  | .mdata _ body => expressionSize body + 1
  | .proj _ _ body => expressionSize body + 1
  | _ => 1

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def reifyWithFuel : Nat → Lean.Expr → SourceSort → Array Local → MetaM Term
  | 0, expression, _, _ => unsupported expression
  | fuel + 1, expression, expected, locals => do
      ensureType expression expected
      if let some variableTerm ← variableSyntax? expression expected locals then
        return variableTerm
      match expression with
      | .letE name type value body _ =>
          let boundSort ←
            if type.isConstOf ``UInt64 then pure SourceSort.word
            else if type.isConstOf ``Bool then pure SourceSort.bool
            else unsupported value
          let valueSyntax ← reifyWithFuel fuel value boundSort locals
          withLocalDecl name .default type fun boundLocal => do
            let bodySyntax ← reifyWithFuel fuel (body.instantiate1 boundLocal) expected
              (#[⟨boundLocal, boundSort⟩] ++ locals)
            `(Gasm.Compiler.Word.Structured.Expr.letE $valueSyntax $bodySyntax)
      | _ =>
          match expected with
          | .word => do
              if let some literal := uint64LiteralSyntax? expression then
                return ← `(Gasm.Compiler.Word.Structured.Expr.wordLit $literal)
              if let some (constructor, lhs, rhs) := uint64Binary? expression then
                let lhsSyntax ← reifyWithFuel fuel lhs .word locals
                let rhsSyntax ← reifyWithFuel fuel rhs .word locals
                if constructor == ``Gasm.Compiler.Word.Structured.Expr.add then
                  return ← `(Gasm.Compiler.Word.Structured.Expr.add $lhsSyntax $rhsSyntax)
                else if constructor == ``Gasm.Compiler.Word.Structured.Expr.sub then
                  return ← `(Gasm.Compiler.Word.Structured.Expr.sub $lhsSyntax $rhsSyntax)
                else
                  return ← `(Gasm.Compiler.Word.Structured.Expr.bitAnd $lhsSyntax $rhsSyntax)
              if let some (condition, ifTrue, ifFalse) := iteParts? expression then
                let conditionSyntax ← reifyWithFuel fuel condition .bool locals
                let trueSyntax ← reifyWithFuel fuel ifTrue .word locals
                let falseSyntax ← reifyWithFuel fuel ifFalse .word locals
                return ← `(Gasm.Compiler.Word.Structured.Expr.ite
                  $conditionSyntax $trueSyntax $falseSyntax)
              unsupported expression
          | .bool => do
              if let some (lhs, rhs) := uint64Eq? expression then
                let lhsSyntax ← reifyWithFuel fuel lhs .word locals
                let rhsSyntax ← reifyWithFuel fuel rhs .word locals
                return ← `(Gasm.Compiler.Word.Structured.Expr.eq $lhsSyntax $rhsSyntax)
              if let some (lhs, rhs) := uint64Ult? expression then
                let lhsSyntax ← reifyWithFuel fuel lhs .word locals
                let rhsSyntax ← reifyWithFuel fuel rhs .word locals
                return ← `(Gasm.Compiler.Word.Structured.Expr.ult $lhsSyntax $rhsSyntax)
              if let some value := boolNot? expression then
                let valueSyntax ← reifyWithFuel fuel value .bool locals
                return ← `(Gasm.Compiler.Word.Structured.Expr.not $valueSyntax)
              if let some (condition, ifTrue, ifFalse) := iteParts? expression then
                let conditionSyntax ← reifyWithFuel fuel condition .bool locals
                let trueSyntax ← reifyWithFuel fuel ifTrue .bool locals
                let falseSyntax ← reifyWithFuel fuel ifFalse .bool locals
                return ← `(Gasm.Compiler.Word.Structured.Expr.ite
                  $conditionSyntax $trueSyntax $falseSyntax)
              unsupported expression

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def reify (expression : Lean.Expr) (expected : SourceSort)
    (locals : Array Local) : MetaM Term :=
  reifyWithFuel (expressionSize expression + 1) expression expected locals

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def reifyDeclaration (declaration : Name) : MetaM Term := do
  let info ← getConstInfo declaration
  let some value := info.value? |
    throwError "structured Word reification requires a declaration with a kernel-visible body"
  lambdaTelescope value fun arguments body => do
    unless arguments.size == 4 do
      throwError "structured Word reification requires exactly four explicit UInt64 arguments; \
        found {arguments.size}"
    for argument in arguments do
      let declaration ← argument.fvarId!.getDecl
      unless declaration.binderInfo == .default do
        throwError "structured Word reification requires four explicit arguments; \
          `{declaration.userName}` is not explicit"
      ensureType argument .word
    ensureType body .word
    let locals := arguments.map fun argument => Local.mk argument .word
    reify body .word locals

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
syntax (name := structuredWordReifyCmd)
  "#structured_word_reify " ident " as " ident : command

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
elab_rules : command
  | `(command| #structured_word_reify $original:ident as $generated:ident) => do
      let declaration ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo original
      let body ← liftTermElabM <| reifyDeclaration declaration
      -- Preserve the already-resolved declaration identity. A plain `mkIdent` would be resolved
      -- again relative to the namespace containing the generated definition.
      let originalName := mkCIdentFrom original declaration
      let command ← `(def $generated : Gasm.Compiler.Word.Structured.WordFunction where
        fn := fun args => $originalName args.a0 args.a1 args.a2 args.a3
        body := $body
        implements := by intro args; rfl)
      withRef original <| elabCommand command

end Gasm.Compiler.Word.StructuredLeanReify

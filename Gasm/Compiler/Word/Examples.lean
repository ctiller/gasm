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

import Gasm.Compiler.Word.MicrosoftX64
import Gasm.Compiler.Word.AArch64AAPCS64
import Gasm.Compiler.Word.LeanReify
import Gasm.Compiler.Word.Structured
import Gasm.Compiler.Word.StructuredCFG
import Gasm.Compiler.Word.StructuredLeanReify

namespace Gasm.Compiler.Word.Examples

/- REF: docs/MACRO_ASSEMBLER.md#choosing-the-authoring-level -/
/-- A normal Lean function, plus the small expression the compiler may inspect and its certificate. -/
def addFirstTwo : Function where
  fn := fun args => args.a0 + args.a1
  body := .binary .add (.arg .a0) (.arg .a1)
  implements := by intro; rfl

/- REF: docs/MACRO_ASSEMBLER.md#choosing-the-authoring-level -/
/-- The portable intermediate form is available when a client wants to transform or inspect it. -/
def addFirstTwoPortable : List Op := compileExpr addFirstTwo.body

/- REF: docs/MACRO_ASSEMBLER.md#choosing-the-authoring-level -/
/-- The proved macro list is available when a client wants to compose generated and custom macros. -/
def addFirstTwoMacros : Gasm.Targets.X86_64.MacroAssembler.Program :=
  MicrosoftX64.compileMacros addFirstTwo

/- REF: docs/MACRO_ASSEMBLER.md#choosing-the-authoring-level -/
/-- Or bulk compilation can directly produce the ordinary instruction list accepted elsewhere. -/
def addFirstTwoAssembly : List Gasm.Targets.X86_64.X86_64Instr :=
  MicrosoftX64.compileAssembly addFirstTwo

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
/-- The preferred bulk-compiler result: code plus generic compiler correctness certificates. -/
def addFirstTwoCompiled : MicrosoftX64.LocalCertificate addFirstTwo :=
  MicrosoftX64.lower addFirstTwo

/- REF: docs/MACRO_ASSEMBLER.md#choosing-the-authoring-level -/
example (s : Gasm.Targets.X86_64.X86_64MachineState) :
    (Gasm.Targets.X86_64.MacroAssembler.runLocalSteps addFirstTwoAssembly s).gprs .rax =
      s.gprs .rcx + s.gprs .rdx := by
  simpa [addFirstTwoAssembly, addFirstTwo, MicrosoftX64.argsOfState] using
    MicrosoftX64.compileAssembly_correct addFirstTwo s

/- REF: docs/MACRO_ASSEMBLER.md#frontend-certificates -/
/-- The generic compiler certifies this concrete body's local instruction-step result. A separate
    platform refinement is required before claiming whole-function execution correctness. -/
example (s : Gasm.Targets.X86_64.X86_64MachineState) :
    (Gasm.Targets.X86_64.MacroAssembler.runLocalSteps addFirstTwoCompiled.instructions s).gprs .rax =
      addFirstTwo.fn (MicrosoftX64.argsOfState s) :=
  addFirstTwoCompiled.localResult s

#guard addFirstTwoPortable.length == 2
#guard addFirstTwoMacros.length == 3
#guard addFirstTwoAssembly.length == 3

namespace LeanReify

open Gasm.Compiler.Word.LeanReify

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def firstArgument (a _b _c _d : UInt64) : UInt64 := a
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify firstArgument as firstArgumentWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def secondArgument (_a b _c _d : UInt64) : UInt64 := b
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify secondArgument as secondArgumentWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def thirdArgument (_a _b c _d : UInt64) : UInt64 := c
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify thirdArgument as thirdArgumentWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def fourthArgument (_a _b _c d : UInt64) : UInt64 := d
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify fourthArgument as fourthArgumentWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def repeatedArgument (a _b _c _d : UInt64) : UInt64 := a + a
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify repeatedArgument as repeatedArgumentWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def zeroConstant (_a _b _c _d : UInt64) : UInt64 := 0
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify zeroConstant as zeroConstantWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def maxConstant (_a _b _c _d : UInt64) : UInt64 := 18446744073709551615
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify maxConstant as maxConstantWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def wrapAdd (a _b _c _d : UInt64) : UInt64 := a + 18446744073709551615
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify wrapAdd as wrapAddWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def orderedSub (a b _c _d : UInt64) : UInt64 := a - b
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify orderedSub as orderedSubWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def wrapSub (a _b _c _d : UInt64) : UInt64 := a - 18446744073709551615
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify wrapSub as wrapSubWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def orderedAnd (a b _c _d : UInt64) : UInt64 := a &&& b
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
#word_reify orderedAnd as orderedAndWord

example : orderedSubWord.body = .binary .sub (.arg .a0) (.arg .a1) := rfl
example : orderedAndWord.body = .binary .bitAnd (.arg .a0) (.arg .a1) := rfl
example : wrapAddWord.body =
    .binary .add (.arg .a0) (.const (18446744073709551615 : UInt64)) := rfl
example : wrapSubWord.body =
    .binary .sub (.arg .a0) (.const (18446744073709551615 : UInt64)) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
/-- Both existing backends consume the generated portable function without a special path. -/
def generatedMicrosoftX64 : MicrosoftX64.LocalCertificate orderedSubWord :=
  MicrosoftX64.lower orderedSubWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
/-- The same generated function is independently lowered by the AAPCS64 backend. -/
def generatedAArch64 : AArch64AAPCS64.LocalCertificate orderedSubWord :=
  AArch64AAPCS64.lower orderedSubWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedMul (a b _c _d : UInt64) : UInt64 := a * b
/-- error: unsupported Word atom `a * b`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedMul as unsupportedMulWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedDiv (a b _c _d : UInt64) : UInt64 := a / b
/-- error: unsupported Word atom `a / b`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedDiv as unsupportedDivWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedShift (a _b _c _d : UInt64) : UInt64 := a <<< 1
/-- error: unsupported Word atom `a <<< 1`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedShift as unsupportedShiftWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedComparison (a b _c _d : UInt64) : Bool := a == b
/-- error: Word reification requires a UInt64 result, but found `Bool` -/
#guard_msgs(error) in
#word_reify unsupportedComparison as unsupportedComparisonWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedIf (a b c _d : UInt64) : UInt64 := if a == 0 then b else c
/-- error: unsupported Word atom `if (a == 0) = true then b else c`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedIf as unsupportedIfWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedLet (a b _c _d : UInt64) : UInt64 := let x := a; x + b
/-- error: unsupported Word atom `have x := a;
x + b`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedLet as unsupportedLetWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def wrapper (value : UInt64) : UInt64 := value
/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedWrapper (a _b _c _d : UInt64) : UInt64 := wrapper a
/-- error: unsupported Word atom `wrapper a`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedWrapper as unsupportedWrapperWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def unsupportedNested (a b c _d : UInt64) : UInt64 := (a + b) + c
/-- error: unsupported Word atom `a + b`; expected one of the four arguments or a UInt64 literal -/
#guard_msgs(error) in
#word_reify unsupportedNested as unsupportedNestedWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def wrongArity (a b : UInt64) : UInt64 := a + b
/-- error: Word reification requires exactly four explicit UInt64 arguments; found 2 -/
#guard_msgs(error) in
#word_reify wrongArity as wrongArityWord

/- REF: docs/MACRO_ASSEMBLER.md#lean-word-reification -/
def wrongArgumentType (a : UInt32) (_b _c _d : UInt64) : UInt64 := a.toUInt64
/-- error: Word reification requires every argument to have type UInt64, but found `UInt32` -/
#guard_msgs(error) in
#word_reify wrongArgumentType as wrongArgumentTypeWord

end LeanReify

namespace StructuredExamples

open Gasm.Compiler.Word.Structured

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def selectIncrementedOriginal (a b _c _d : UInt64) : UInt64 :=
  let incremented := a + 1
  if incremented < b then incremented else b

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def selectIncrementedBody : Gasm.Compiler.Word.Structured.Expr InputContext .word :=
  .letE
    (.add (.var InputContext.a0) (.wordLit 1))
    (.ite
      (.ult (.var .zero) (.var (.succ InputContext.a1)))
      (.var .zero)
      (.var (.succ InputContext.a1)))

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- A typed `let` and `if` body tied extensionally to the original four-argument Lean function. -/
def selectIncremented : WordFunction where
  fn := fun args =>
    selectIncrementedOriginal args.a0 args.a1 args.a2 args.a3
  body := selectIncrementedBody
  implements := by
    intro args
    by_cases selected : args.a0 + 1 < args.a1 <;>
      simp [selectIncrementedOriginal, selectIncrementedBody, selected]

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
def firstTwoEqualOriginal (a b _c _d : UInt64) : Bool := a == b

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-source-language -/
/-- Boolean-result source functions have semantics but no current machine-backend authority. -/
def firstTwoEqual : BoolFunction where
  fn := fun args => firstTwoEqualOriginal args.a0 args.a1 args.a2 args.a3
  body := .eq (.var InputContext.a0) (.var InputContext.a1)
  implements := by intro; rfl

end StructuredExamples

namespace StructuredLeanReifyExamples

open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredLeanReify

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def orderedChoice (a b _c _d : UInt64) : UInt64 :=
  if decide (a < b) then a - b else b - a

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#structured_word_reify orderedChoice as orderedChoiceWord

example : orderedChoiceWord.body =
    .ite (.ult (.var InputContext.a0) (.var InputContext.a1))
      (.sub (.var InputContext.a0) (.var InputContext.a1))
      (.sub (.var InputContext.a1) (.var InputContext.a0)) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def equalityChoice (a b c d : UInt64) : UInt64 :=
  if a == b then c else d

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#structured_word_reify equalityChoice as equalityChoiceWord

example : equalityChoiceWord.body =
    .ite (.eq (.var InputContext.a0) (.var InputContext.a1))
      (.var InputContext.a2) (.var InputContext.a3) := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
/-- Nested dependent lets include a Bool binding and shadow a source name without changing the
    generated de Bruijn references. -/
def nestedLetChoice (a b c d : UInt64) : UInt64 :=
  let selected := a - b
  let selected := selected &&& c
  let isSmall := decide (selected < d)
  if !isSmall then selected else
    let selected := selected + b
    if selected == a then selected else d

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#structured_word_reify nestedLetChoice as nestedLetChoiceWord

example (args : Args) :
    nestedLetChoiceWord.fn args =
      nestedLetChoiceWord.body.eval (InputContext.env args) :=
  nestedLetChoiceWord.implements args

#guard orderedChoiceWord.fn ⟨1, 3, 0, 0⟩ == 18446744073709551614
#guard orderedChoiceWord.fn ⟨5, 2, 0, 0⟩ == 18446744073709551613

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def structuredHelper (value : UInt64) : UInt64 := value
/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def unsupportedStructuredHelper (a _b _c _d : UInt64) : UInt64 := structuredHelper a
/-- error: unsupported structured Word term `structuredHelper a` with inferred type `UInt64` -/
#guard_msgs(error) in
#structured_word_reify unsupportedStructuredHelper as unsupportedStructuredHelperWord

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def unsupportedBoolAnd (a b c _d : UInt64) : UInt64 :=
  if decide (a < b) && decide (b < c) then a else c
/-- error: unsupported structured Word term `decide (a < b) && decide (b < c)` with inferred type `Bool` -/
#guard_msgs(error) in
#structured_word_reify unsupportedBoolAnd as unsupportedBoolAndWord

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def wrongStructuredArity (a b : UInt64) : UInt64 := a + b
/-- error: structured Word reification requires exactly four explicit UInt64 arguments; found 2 -/
#guard_msgs(error) in
#structured_word_reify wrongStructuredArity as wrongStructuredArityWord

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def wrongStructuredResult (a b _c _d : UInt64) : Bool := a == b
/-- error: structured Word reification expected `UInt64` but term `a == b` has inferred type `Bool` -/
#guard_msgs(error) in
#structured_word_reify wrongStructuredResult as wrongStructuredResultWord

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def wrongStructuredWidth (a : UInt32) (_b _c _d : UInt64) : UInt64 := a.toUInt64
/-- error: structured Word reification expected `UInt64` but term `a` has inferred type `UInt32` -/
#guard_msgs(error) in
#structured_word_reify wrongStructuredWidth as wrongStructuredWidthWord

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def wrongStructuredSigned (a : Int64) (_b _c _d : UInt64) : UInt64 := a.toUInt64
/-- error: structured Word reification expected `UInt64` but term `a` has inferred type `Int64` -/
#guard_msgs(error) in
#structured_word_reify wrongStructuredSigned as wrongStructuredSignedWord

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
@[instance_reducible] def fakeAdd : HAdd UInt64 UInt64 UInt64 where
  hAdd := fun lhs _rhs => lhs
/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def unsupportedAddInstance (a b _c _d : UInt64) : UInt64 :=
  @HAdd.hAdd UInt64 UInt64 UInt64 fakeAdd a b
/-- error: unsupported structured Word term `a + b` with inferred type `UInt64` -/
#guard_msgs(error) in
#structured_word_reify unsupportedAddInstance as unsupportedAddInstanceWord

end StructuredLeanReifyExamples

namespace StructuredCFGExamples

open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
inductive DecisionRole where
  | root | trueLeaf | falseLeaf
  deriving DecidableEq, Repr

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def rootRole : NodeId DecisionRole := ⟨.root⟩
/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def trueRole : NodeId DecisionRole := ⟨.trueLeaf⟩
/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def falseRole : NodeId DecisionRole := ⟨.falseLeaf⟩

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def chooseCondition : Gasm.Compiler.Word.Structured.Expr InputContext .bool :=
  .ult (.var InputContext.a0) (.var InputContext.a1)

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def trueLeafPlan : Plan DecisionRole (.wordLit 1) [trueRole] trueRole :=
  .leaf trueRole .wordLit

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
def falseLeafPlan : Plan DecisionRole (.wordLit 2) [falseRole] falseRole :=
  .leaf falseRole .wordLit

/- REF: docs/MACRO_ASSEMBLER.md#structured-word-cfg-plans -/
/-- Source expression, stable roles, postorder, and polarity are fixed before blocks are assigned. -/
def symbolicChoice : Plan DecisionRole
    (.ite chooseCondition (.wordLit 1) (.wordLit 2))
    [falseRole, trueRole, rootRole] rootRole :=
  .branch rootRole (.ult .var .var) trueLeafPlan falseLeafPlan
    (by simp [falseRole, trueRole])
    (by simp [rootRole, falseRole, trueRole])

example : [falseRole, trueRole, rootRole].Nodup := symbolicChoice.uniqueRoles
example : rootRole ∈ [falseRole, trueRole, rootRole] := symbolicChoice.root_mem

end StructuredCFGExamples

end Gasm.Compiler.Word.Examples

namespace StructuredReifyIdentityRegression

namespace B

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def differing (a b _c _d : UInt64) : UInt64 := a - b
/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
def coincident (a b _c _d : UInt64) : UInt64 := a + b

end B

namespace StructuredReifyIdentityRegression.B

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
/-- This shadow has different behavior, so accidental re-resolution also breaks the generated
    kernel proof. -/
def differing (a b _c _d : UInt64) : UInt64 := b - a
/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
/-- This shadow deliberately has the same body; behavioral equality cannot detect wrong identity. -/
def coincident (a b _c _d : UInt64) : UInt64 := a + b

end StructuredReifyIdentityRegression.B

open Gasm.Compiler.Word.StructuredLeanReify

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#structured_word_reify B.differing as differingWord
/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#structured_word_reify B.coincident as coincidentWord

end StructuredReifyIdentityRegression

namespace StructuredReifyIdentityRegressionTest

open Lean Elab Command

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
private def containsConstant (target : Name) : Lean.Expr → Bool
  | .const name _ => name == target
  | .app fn argument => containsConstant target fn || containsConstant target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConstant target type || containsConstant target body
  | .letE _ type value body _ =>
      containsConstant target type || containsConstant target value || containsConstant target body
  | .mdata _ body | .proj _ _ body => containsConstant target body
  | _ => false

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
syntax (name := guardGeneratedOriginalCmd)
  "#guard_generated_original " ident " uses " ident " not " ident : command

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
elab_rules : command
  | `(command| #guard_generated_original $generated:ident uses $original:ident not $shadow:ident) => do
      let generatedName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo generated
      let originalName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo original
      let shadowName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo shadow
      let info ← getConstInfo generatedName
      let some value := info.value? |
        throwErrorAt generated "generated structured Word declaration has no inspectable value"
      unless containsConstant originalName value do
        throwErrorAt generated "generated structured Word declaration does not retain exact original `{originalName}`"
      if containsConstant shadowName value then
        throwErrorAt generated "generated structured Word declaration captured shadow `{shadowName}`"

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#guard_generated_original
  StructuredReifyIdentityRegression.differingWord uses
  StructuredReifyIdentityRegression.B.differing not
  StructuredReifyIdentityRegression.StructuredReifyIdentityRegression.B.differing

/- REF: docs/MACRO_ASSEMBLER.md#structured-lean-word-reification -/
#guard_generated_original
  StructuredReifyIdentityRegression.coincidentWord uses
  StructuredReifyIdentityRegression.B.coincident not
  StructuredReifyIdentityRegression.StructuredReifyIdentityRegression.B.coincident

end StructuredReifyIdentityRegressionTest

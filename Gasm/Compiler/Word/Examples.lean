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

end Gasm.Compiler.Word.Examples

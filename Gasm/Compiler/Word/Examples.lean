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

end Gasm.Compiler.Word.Examples

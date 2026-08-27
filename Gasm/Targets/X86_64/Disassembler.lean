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
import Gasm.Core.Types
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Decoder

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Formats a list of x86-64 instructions as a formatted Lean DSL list expression. -/
def toLeanProgramString (instrs : List X86_64Instr) : String :=
  let lines := instrs.map (fun i => "  " ++ X86_64Instruction.toLean i)
  "[\n" ++ String.intercalate ",\n" lines ++ "\n]"

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Generates a complete standalone compilable Lean 4 source code module containing the disassembled instructions. -/
def toLeanSourceModule (moduleName : String) (instrs : List X86_64Instr) : String :=
  "import Lean\n" ++
  "import Gasm.Core.Types\n" ++
  "import Gasm.Targets.X86_64.Registers\n" ++
  "import Gasm.Targets.X86_64.Instructions\n" ++
  "import Gasm.Targets.X86_64.Instructions.Add\n" ++
  "import Gasm.Targets.X86_64.Instructions.Sub\n" ++
  "import Gasm.Targets.X86_64.Instructions.Mov\n" ++
  "import Gasm.Targets.X86_64.Instructions.Lea\n" ++
  "import Gasm.Targets.X86_64.Instructions.Cmp\n" ++
  "import Gasm.Targets.X86_64.Instructions.Jcc\n" ++
  "import Gasm.Targets.X86_64.Instructions.Push\n" ++
  "import Gasm.Targets.X86_64.Instructions.Pop\n" ++
  "import Gasm.Targets.X86_64.Instructions.Div\n" ++
  "import Gasm.Targets.X86_64.Instructions.Imul\n" ++
  "import Gasm.Targets.X86_64.Instructions.And\n" ++
  "import Gasm.Targets.X86_64.Instructions.Or\n" ++
  "import Gasm.Targets.X86_64.Instructions.Xor\n" ++
  "import Gasm.Targets.X86_64.Instructions.Not\n" ++
  "import Gasm.Targets.X86_64.Instructions.Neg\n" ++
  "import Gasm.Targets.X86_64.Instructions.Shift\n" ++
  "import Gasm.Targets.X86_64.Instructions.Test\n" ++
  "import Gasm.Targets.X86_64.Instructions.Xchg\n" ++
  "import Gasm.Targets.X86_64.Instructions.Cmov\n" ++
  "import Gasm.Targets.X86_64.Instructions.Call\n" ++
  "import Gasm.Targets.X86_64.Instructions.Ret\n\n" ++
  "open Gasm.Targets.X86_64\n" ++
  "open Gasm.Targets.X86_64.Instructions\n\n" ++
  s!"def {moduleName} : List X86_64Instr := {toLeanProgramString instrs}\n"

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Disassembles raw bytes and formats them into Lean DSL list expressions. -/
def disassembleToLean (bytes : ByteArray) : Except String String :=
  match disassembleX86_64 bytes with
  | .error e => .error e
  | .ok instrs => .ok (toLeanProgramString instrs)

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- Disassembles raw bytes and formats them into a complete Lean 4 module. -/
def disassembleToLeanModule (moduleName : String) (bytes : ByteArray) : Except String String :=
  match disassembleX86_64 bytes with
  | .error e => .error e
  | .ok instrs => .ok (toLeanSourceModule moduleName instrs)

end Gasm.Targets.X86_64

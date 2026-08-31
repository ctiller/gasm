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

import Gasm.Compiler.Word.StructuredLeanReify
import Gasm.Compiler.Word.StructuredStraightLineAArch64
import Gasm.Targets.AArch64.Linux.Linker
import Gasm.Targets.AArch64.Linux.Syscall

namespace Spikes.CompilerBulk.AArch64Linux

open Gasm.Compiler.Word
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Compiler.Word.StructuredStraightLineAArch64
open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions
open Gasm.Targets.AArch64.Linux

/- REF: docs/MACRO_ASSEMBLER.md#verified-compiler-bulk-spike -/
/-- Representative Lean source: structural lets are retained by reification, while the selected
    backend compiles the branch-free word fragment around any later handwritten assembly. -/
def bulkExit (a0 _a1 _a2 _a3 : UInt64) : UInt64 :=
  let seed := a0 + 17
  let masked := seed &&& 255
  masked + 25

#structured_word_reify bulkExit as bulkExitWord

def bulkExitSelected : WordOnly (source := bulkExitWord.body) :=
  .letE (.add (.var _) (.wordLit _))
    (.letE (.bitAnd (.var _) (.wordLit _))
      (.add (.var _) (.wordLit _)))

theorem bulkExitFits : Fits (compile bulkExitSelected) := by
  change 3 ≤ 7
  omega

def compiled : LocalCertificate bulkExitWord bulkExitSelected bulkExitFits :=
  lowerFunction bulkExitWord bulkExitSelected bulkExitFits

/-- Handwritten platform tail: choose Linux `exit`, then cross the selected SVC boundary. -/
def exitWrapper : List Instructions.AnyAArch64Instruction :=
  [Instructions.AnyAArch64Instruction.mk (movz64 .x8 93),
   Instructions.AnyAArch64Instruction.mk (svcInstr 0)]

def instructions : List Instructions.AnyAArch64Instruction :=
  compiled.instructions ++ exitWrapper

def executable : AArch64LinuxExecutable where
  imageBase := 0x400000
  textBytes := serializeInstructions instructions

end Spikes.CompilerBulk.AArch64Linux

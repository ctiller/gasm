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
import Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry.Differential
import Gasm.Targets.Windows.Linker

namespace Spikes.CompilerBulk.WindowsX64

open Gasm.Compiler.Word
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
/-- Representative process-entry computation. It reads an unspecified entry register but cancels
    it algebraically, so every admitted PE entry computes the same typed exit code. -/
def bulkExit (a0 _a1 _a2 _a3 : UInt64) : UInt64 :=
  let cancelled := a0 - a0
  cancelled + 42

#structured_word_reify bulkExit as bulkExitWord

def bulkExitSelected : WordOnly (source := bulkExitWord.body) :=
  .letE (.sub (.var _) (.var _))
    (.add (.var _) (.wordLit _))

theorem bulkExitFits : Fits (compile bulkExitSelected) := by
  change 2 ≤ 7
  omega

/-- The compiler's local, non-callable process-entry body evidence. -/
def compiled : LocalCertificate bulkExitWord bulkExitSelected bulkExitFits :=
  lowerFunction bulkExitWord bulkExitSelected bulkExitFits

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
/-- A hand-selected one-instruction implementation of the same selected result contract. -/
def optimizedSegment : Gasm.Targets.X86_64.MacroAssembler.Segment :=
  Gasm.Targets.X86_64.MacroAssembler.loadImm resultRegister 42

/- REF: docs/MACRO_ASSEMBLER.md#verified-microsoft-x64-compiler-bulk-spike -/
/-- Property-relative proof that the hand-selected body preserves the compiler baseline's RAX
    result for every entry state. -/
def optimizedDelta : FunctionalDelta compiled where
  replacement := optimizedSegment
  memoryPreserved := rfl
  resultEq := by
    intro state
    calc
      (Gasm.Targets.X86_64.MacroAssembler.runLocalSteps optimizedSegment.code state).gprs
          resultRegister = 42 := optimizedSegment.localSound state trivial
      _ = (Gasm.Targets.X86_64.MacroAssembler.runLocalSteps compiled.instructions state).gprs
          resultRegister := by
        rw [compiled.localResult]
        simp [bulkExitWord, bulkExit]

/-- Exact replacement-local facts regenerated from `optimizedDelta`. -/
def optimized : BodyRealization bulkExitWord :=
  optimizedDelta.realize

/-- The selected bulk body is followed by three handwritten instructions: reserve the Microsoft
    x64 call frame, move the verified result into ExitProcess's first argument, and call the
    linker-resolved import. -/
def symbolicProgram : List SymbolicInstr :=
  optimized.instructions.map instr ++
    [instr (sub_rsp 40), instr (mov_r64 .rcx resultRegister), call_import "ExitProcess"]

def linked : LinkedWindowsProgram :=
  linkWindowsProgram symbolicProgram

def instructions : List X86_64Instr := linked.instructions

def executable : WindowsExecutable := linked.executable

end Spikes.CompilerBulk.WindowsX64

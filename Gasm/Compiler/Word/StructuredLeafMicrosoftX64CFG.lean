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

import Gasm.Compiler.Word.StructuredCFG
import Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry.Differential
import Gasm.Targets.X86_64.CFGBridge

namespace Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFG

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Compiler.Word
open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG
open Gasm.Compiler.Word.StructuredStraightLine
open Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
/-- The canonical local function for one exact leaf expression. It is an internal bridge from the
    source-indexed leaf contract to the existing bounded backend; it does not replace the root
    `WordFunction` that remains tied to the user's named Lean declaration. -/
def leafFunction (source : Structured.Expr InputContext .word) : Structured.WordFunction where
  fn := fun args => source.eval (InputContext.env args)
  body := source
  implements := fun _ => rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
/-- Exact implementation-neutral local evidence for one branch-free leaf. Generated code and a
    hand-optimized differential replacement enter the CFG through this same contract. -/
structure Body (source : Structured.Expr InputContext .word) where
  instructions : List X86_64Instr
  codeBytes : ByteArray
  codeBytes_eq : codeBytes =
    Gasm.Targets.X86_64.Assembler.serializeInstructions instructions
  localResult : ∀ state,
    (runLocalSteps instructions state).gprs resultRegister =
      source.eval (InputContext.env (argsOfState state))
  preservesMemory : ∀ state,
    (runLocalSteps instructions state).memory = state.memory
  preservesFault : ∀ state,
    (runLocalSteps instructions state).fault = state.fault
  ripAdvance : ∀ state,
    (runLocalSteps instructions state).rip = state.rip + instructionSpan instructions
  clobberedGprs : List Reg64
  preservesGpr : ∀ state register, register ∉ clobberedGprs →
    (runLocalSteps instructions state).gprs register = state.gprs register
  controlFlowFree : ∀ instruction ∈ instructions, ControlFlowFree instruction

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
def Body.ofGenerated {source : Structured.Expr InputContext .word}
    {selected : WordOnly (source := source)} {fits : Fits (compile selected)}
    (certificate : LocalCertificate (leafFunction source) selected fits) : Body source where
  instructions := certificate.instructions
  codeBytes := certificate.codeBytes
  codeBytes_eq := certificate.codeBytes_eq
  localResult := certificate.localResult
  preservesMemory := certificate.preservesMemory
  preservesFault := certificate.preservesFault
  ripAdvance := certificate.ripAdvance
  clobberedGprs := certificate.clobberedGprs
  preservesGpr := certificate.preservesGpr
  controlFlowFree := certificate.controlFlowFree

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
def Body.ofReplacement {source : Structured.Expr InputContext .word}
    (replacement : BodyRealization (leafFunction source)) : Body source where
  instructions := replacement.instructions
  codeBytes := replacement.codeBytes
  codeBytes_eq := replacement.codeBytes_eq
  localResult := replacement.localResult
  preservesMemory := replacement.preservesMemory
  preservesFault := replacement.preservesFault
  ripAdvance := replacement.ripAdvance
  clobberedGprs := replacement.clobberedGprs
  preservesGpr := replacement.preservesGpr
  controlFlowFree := replacement.controlFlowFree

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
/-- Lift the selected local body into the same API typestate and ghost world. -/
def afterBody (body : Body source)
    (state : ComposedState X86_64 State) : ComposedState X86_64 State :=
  { state with machine := runLocalSteps body.instructions state.machine }

@[simp] theorem afterBody_machine (body : Body source)
    (state : ComposedState X86_64 State) :
    (afterBody body state).machine = runLocalSteps body.instructions state.machine := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
theorem afterBody_ghostFrame (body : Body source) (state : ComposedState X86_64 State) :
    ConservativeGhostFrame state (afterBody body state) where
  sameState := rfl
  stackDepth := rfl
  api := rfl
  permissions := rfl
  obligations := rfl
  causalClock := rfl
  eventHistory := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
/-- Caller-owned logical termination for the exact local body result. The exhaustive target-free
    proof prevents a hidden JMP/JCC; emitted RET/exit/halt realization remains target/platform work. -/
structure Terminal {BlockId : Type} {source : Structured.Expr InputContext .word}
    (body : Body source) (entry : BlockEntry X86_64 BlockId) where
  terminator : ∀ (state : ComposedState X86_64 entry.State) (_accepted : entry.accepts state),
    DirectTerminator (BlockId := BlockId) (afterBody body state)
  targetFree : ∀ state accepted, TargetFree (terminator state accepted)

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
def block {BlockId : Type} {source : Structured.Expr InputContext .word}
    (body : Body source) (entry : BlockEntry X86_64 BlockId)
    (terminal : Terminal body entry) : DirectBlock X86_64 BlockId where
  entry := entry
  body := fun state accepted =>
    ⟨entry.State, afterBody body state, terminal.terminator state accepted⟩

@[simp] theorem block_entry {BlockId : Type} {source : Structured.Expr InputContext .word}
    (body : Body source) (entry : BlockEntry X86_64 BlockId)
    (terminal : Terminal body entry) : (block body entry terminal).entry = entry := rfl

/- REF: docs/MACRO_ASSEMBLER.md#structured-microsoft-x64-leaf-blocks -/
/-- Existing `StructuredCFG.RealizesLeaf` evidence for the exact generated or handwritten body. -/
def realizes {BlockId : Type} {source : Structured.Expr InputContext .word}
    (body : Body source) (entry : BlockEntry X86_64 BlockId)
    (terminal : Terminal body entry) :
    RealizesLeaf (Evidence := PUnit) (block body entry terminal) source where
  evidence := PUnit.unit
  entryRelation := fun args state => argsOfState state.machine = args
  exitRelation := fun expected _ exit => exit.machine.gprs resultRegister = expected
  realizes := by
    intro args state accepted argsExact
    change
      (runLocalSteps body.instructions state.machine).gprs resultRegister =
        source.eval (InputContext.env args)
    rw [body.localResult state.machine]
    rw [argsExact]
  targetFree := by
    intro state accepted
    exact terminal.targetFree state accepted

end Gasm.Compiler.Word.StructuredLeafMicrosoftX64CFG

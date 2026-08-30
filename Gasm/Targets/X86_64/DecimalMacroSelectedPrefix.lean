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

import Gasm.Targets.X86_64.DecimalMacro
import Gasm.Targets.X86_64.MacroAssembler.SelectedPrefixBridge

namespace Gasm.Targets.X86_64.DecimalMacro

open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule
open Gasm.Targets.X86_64.CFGLinker

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
/-- The ordinary portion of one extraction pass.  The final JNE stays explicit. -/
def extractionOrdinaryCode : List X86_64Instr := [
  xor_r32 .edx .edx,
  div_r64 .r10,
  add_r64_imm8 .rdx 0x30,
  push_r64 .rdx,
  add_r64_imm8 .rcx 1,
  cmp_r64_imm8 .rax 0
]

private theorem divCoreFallthrough (state : X86_64MachineState)
    (safe : (X86_64Instruction.step (div_r64 .r10) state).fault = none) :
    (X86_64Instruction.step (div_r64 .r10) state).rip = state.rip + 3 := by
  let core : X86_64MachineState :=
    { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).fault = none at safe
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).rip = state.rip + 3
  simp only [X86_64Instruction.step] at safe ⊢
  split at safe
  · contradiction
  · rename_i hnonzero
    split at safe
    · contradiction
    · rename_i hfits
      simp [hnonzero, hfits, core]

private theorem extractionOrdinarySequential (instruction : X86_64Instr)
    (member : instruction ∈ extractionOrdinaryCode) : SequentialInstruction instruction := by
  simp only [extractionOrdinaryCode, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.xor32 .edx .edx, by intros; rfl⟩
  · exact ⟨.div .r10, divCoreFallthrough⟩
  · exact ⟨.addImm8 .rdx 0x30, by intros; rfl⟩
  · exact ⟨.push .rdx, by intros; rfl⟩
  · exact ⟨.addImm8 .rcx 1, by intros; rfl⟩
  · exact ⟨.compareImm8 .rax 0, by intros; rfl⟩

private theorem extractionOrdinaryRun (initial : X86_64MachineState) :
    runLocalSteps extractionOrdinaryCode initial = (extractionStates initial).2.2.2.2.2 := by
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
/-- Real seven-instruction DecimalSchedule adapter: the opaque generic bridge owns the six
ordinary steps, while the final conditional branch remains explicit and the result is the exact
existing `extractionFinal`. -/
theorem ExtractionLinkedLayout.selectedPrefixViaBridge {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {text : LinkedText} {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    (layout : ExtractionLinkedLayout text indexed backDisp)
    (initial : X86_64MachineState) (entry : initial.rip = layout.address .clearHigh)
    (executionSafety : ExtractionExecutionSafety backDisp initial)
    (runtime : ExtractionRuntimeEvidence (Event := Event) selected backDisp initial)
    (branch : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2)
    (eventsRev : List Event) :
    ProductionPrefix.SelectedPrefix selected indexed 7 initial eventsRev
      (extractionFinal backDisp initial) eventsRev [] := by
  have existing := layout.toSelectedPlacement initial entry executionSafety runtime
  have evidence : ∀ before instruction suffix,
      extractionOrdinaryCode = before ++ instruction :: suffix →
      SelectedSequentialStepEvidence (Event := Event) selected indexed initial before instruction := by
    intro before instruction suffix split
    rcases before with _ | ⟨a, before⟩
    · simp only [extractionOrdinaryCode, List.nil_append, List.cons.injEq] at split
      rcases split with ⟨rfl, rfl⟩
      exact ⟨extractionOrdinarySequential _ (by simp [extractionOrdinaryCode]),
        existing.toExtractionPlacement.lookupXor, existing.selectedXor,
        existing.toExtractionPlacement.silentXor, executionSafety.xorSafe⟩
    · rcases before with _ | ⟨b, before⟩
      · simp only [extractionOrdinaryCode, List.cons_append, List.nil_append,
          List.cons.injEq] at split
        rcases split with ⟨rfl, rfl, rfl⟩
        exact ⟨extractionOrdinarySequential _ (by simp [extractionOrdinaryCode]),
          existing.toExtractionPlacement.lookupDiv, existing.selectedDiv,
          existing.toExtractionPlacement.silentDiv, executionSafety.divSafe⟩
      · rcases before with _ | ⟨c, before⟩
        · simp only [extractionOrdinaryCode, List.cons_append, List.nil_append,
            List.cons.injEq] at split
          rcases split with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨extractionOrdinarySequential _ (by simp [extractionOrdinaryCode]),
            existing.toExtractionPlacement.lookupAscii, existing.selectedAscii,
            existing.toExtractionPlacement.silentAscii, executionSafety.asciiSafe⟩
        · rcases before with _ | ⟨d, before⟩
          · simp only [extractionOrdinaryCode, List.cons_append, List.nil_append,
              List.cons.injEq] at split
            rcases split with ⟨rfl, rfl, rfl, rfl, rfl⟩
            exact ⟨extractionOrdinarySequential _ (by simp [extractionOrdinaryCode]),
              existing.toExtractionPlacement.lookupPush, existing.selectedPush,
              existing.toExtractionPlacement.silentPush, executionSafety.pushSafe⟩
          · rcases before with _ | ⟨e, before⟩
            · simp only [extractionOrdinaryCode, List.cons_append, List.nil_append,
                List.cons.injEq] at split
              rcases split with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              exact ⟨extractionOrdinarySequential _ (by simp [extractionOrdinaryCode]),
                existing.toExtractionPlacement.lookupCount, existing.selectedCount,
                existing.toExtractionPlacement.silentCount, executionSafety.countSafe⟩
            · rcases before with _ | ⟨f, before⟩
              · simp only [extractionOrdinaryCode, List.cons_append, List.nil_append,
                  List.cons.injEq] at split
                rcases split with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                exact ⟨extractionOrdinarySequential _ (by simp [extractionOrdinaryCode]),
                  existing.toExtractionPlacement.lookupCmp, existing.selectedCmp,
                  existing.toExtractionPlacement.silentCmp, executionSafety.cmpSafe⟩
              · simp [extractionOrdinaryCode] at split
  have ordinary := selectedPrefixOfSequentialEvidence selected extractionOrdinaryCode indexed
    initial evidence eventsRev
  rw [extractionOrdinaryRun] at ordinary
  rcases branch with taken | fallthrough
  · exact ordinary.append (.conditionalTaken (.jne8 backDisp) taken
      existing.toExtractionPlacement.lookupBranch runtime.selectedBranch runtime.silentBranch
      executionSafety.branchSafe (.nil _ _))
  · exact ordinary.append (.conditionalFallthrough (.jne8 backDisp) fallthrough
      existing.toExtractionPlacement.lookupBranch runtime.selectedBranch runtime.silentBranch
      executionSafety.branchSafe (.nil _ _))

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
/-- The ordinary portion of one reverse-write pass. -/
def writeOrdinaryCode : List X86_64Instr := [
  pop_r64 .rdx,
  mov_mem8 .rdi .rdx,
  add_r64_imm8 .rdi 1,
  sub_r64_imm8 .rcx 1
]

private theorem writeOrdinarySequential (instruction : X86_64Instr)
    (member : instruction ∈ writeOrdinaryCode) : SequentialInstruction instruction := by
  simp only [writeOrdinaryCode, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨.pop .rdx, by intros; rfl⟩
  · exact ⟨.movMem8 .rdi .rdx, by intros; rfl⟩
  · exact ⟨.addImm8 .rdi 1, by intros; rfl⟩
  · exact ⟨.subImm8 .rcx 1, by intros; rfl⟩

private theorem writeOrdinaryRun (initial : X86_64MachineState) :
    runLocalSteps writeOrdinaryCode initial = (writeStates initial).2.2.2 := by
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
/-- Real five-instruction DecimalSchedule adapter for the reverse-write pass. -/
theorem WriteLinkedLayout.selectedPrefixViaBridge {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {text : LinkedText} {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    (layout : WriteLinkedLayout text indexed backDisp)
    (initial : X86_64MachineState) (entry : initial.rip = layout.address .pop)
    (executionSafety : WriteExecutionSafety backDisp initial)
    (runtime : WriteRuntimeEvidence (Event := Event) selected backDisp initial)
    (branch : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2)
    (eventsRev : List Event) :
    ProductionPrefix.SelectedPrefix selected indexed 5 initial eventsRev
      (writeFinal backDisp initial) eventsRev [] := by
  have existing := layout.toSelectedPlacement initial entry runtime
  have evidence : ∀ before instruction suffix,
      writeOrdinaryCode = before ++ instruction :: suffix →
      SelectedSequentialStepEvidence (Event := Event) selected indexed initial before instruction := by
    intro before instruction suffix split
    rcases before with _ | ⟨a, before⟩
    · simp only [writeOrdinaryCode, List.nil_append, List.cons.injEq] at split
      rcases split with ⟨rfl, rfl⟩
      exact ⟨writeOrdinarySequential _ (by simp [writeOrdinaryCode]),
        existing.toWritePlacement.lookupPop, existing.selectedPop,
        existing.toWritePlacement.silentPop, executionSafety.popSafe⟩
    · rcases before with _ | ⟨b, before⟩
      · simp only [writeOrdinaryCode, List.cons_append, List.nil_append,
          List.cons.injEq] at split
        rcases split with ⟨rfl, rfl, rfl⟩
        exact ⟨writeOrdinarySequential _ (by simp [writeOrdinaryCode]),
          existing.toWritePlacement.lookupStore, existing.selectedStore,
          existing.toWritePlacement.silentStore, executionSafety.storeSafe⟩
      · rcases before with _ | ⟨c, before⟩
        · simp only [writeOrdinaryCode, List.cons_append, List.nil_append,
            List.cons.injEq] at split
          rcases split with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨writeOrdinarySequential _ (by simp [writeOrdinaryCode]),
            existing.toWritePlacement.lookupCursor, existing.selectedCursor,
            existing.toWritePlacement.silentCursor, executionSafety.cursorSafe⟩
        · rcases before with _ | ⟨d, before⟩
          · simp only [writeOrdinaryCode, List.cons_append, List.nil_append,
              List.cons.injEq] at split
            rcases split with ⟨rfl, rfl, rfl, rfl, rfl⟩
            exact ⟨writeOrdinarySequential _ (by simp [writeOrdinaryCode]),
              existing.toWritePlacement.lookupCount, existing.selectedCount,
              existing.toWritePlacement.silentCount, executionSafety.countSafe⟩
          · simp [writeOrdinaryCode] at split
  have ordinary := selectedPrefixOfSequentialEvidence selected writeOrdinaryCode indexed
    initial evidence eventsRev
  rw [writeOrdinaryRun] at ordinary
  rcases branch with taken | fallthrough
  · exact ordinary.append (.conditionalTaken (.jne8 backDisp) taken
      existing.toWritePlacement.lookupBranch runtime.selectedBranch runtime.silentBranch
      executionSafety.branchSafe (.nil _ _))
  · exact ordinary.append (.conditionalFallthrough (.jne8 backDisp) fallthrough
      existing.toWritePlacement.lookupBranch runtime.selectedBranch runtime.silentBranch
      executionSafety.branchSafe (.nil _ _))

end Gasm.Targets.X86_64.DecimalMacro

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

import Gasm.Targets.X86_64.EventfulSegment
import Gasm.Targets.Linux.OutcomeBridge
import Spikes.Spike2Fibonacci.Linux.Row6

/-!
# First linked Linux Spike 2 row

This module owns the finite, instruction-indexed certificate for the first real Fibonacci output
row.  It is deliberately split from the universal equivalence module so Lean caches the row
certificate independently of the 90-row composition.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem sequentialMovRspByte40 :
    SequentialInstruction (mov_rsp_byte 0x40 0x46) where
  encoding := .movRspByte 0x40 0x46
  safeFallthrough := by intro _ _; rfl

private theorem sequentialCmp (dst : Reg64) (value : UInt8) :
    SequentialInstruction (cmp_r64_imm8 dst value) where
  encoding := .compareImm8 dst value
  safeFallthrough := by intro _ _; rfl

private theorem divCoreFallthrough (state : X86_64MachineState)
    (safe : (X86_64Instruction.step (DivR64.mk .r10) state).fault = none) :
    (X86_64Instruction.step (DivR64.mk .r10) state).rip = state.rip + 3 := by
  simp only [X86_64Instruction.step] at safe ⊢
  split at safe
  · contradiction
  · rename_i hnonzero
    split at safe
    · contradiction
    · rename_i hfits
      simp [hnonzero, hfits]

private theorem sequentialDivR10 : SequentialInstruction (div_r64 .r10) where
  encoding := .div .r10
  safeFallthrough := by
    intro state safe
    let core : X86_64MachineState :=
      { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
      { divisor := .r10 } core).fault = none at safe
    change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
      { divisor := .r10 } core).rip = state.rip + 3
    exact divCoreFallthrough core safe

/-- The exact state after the literal `"Fib("` stores and the linked one-digit index branch. -/
def spike2Row7AfterIndexHeader : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41)
    (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
              (spike2AfterMainHeader spike2Row6AfterRecurrence))))))

/-- The real joined value-format entry reached by Row 7's one-digit index branch. -/
def spike2Row7AfterIndex : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel8 65)
    (X86_64Instruction.step (lea_rsp .rdi 0x49)
      (X86_64Instruction.step (mov_rsp_byte 0x48 0x20)
        (X86_64Instruction.step (mov_rsp_byte 0x47 0x3d)
          (X86_64Instruction.step (mov_rsp_byte 0x46 0x20)
            (X86_64Instruction.step (mov_rsp_byte 0x45 0x29)
              (X86_64Instruction.step (mov_mem8 .rdi .rax)
                (X86_64Instruction.step (lea_rsp .rdi 0x44)
                  (X86_64Instruction.step (add_r64_imm8 .rax 0x30)
                    (X86_64Instruction.step (mov_r64 .rax .r13)
                      spike2Row7AfterIndexHeader)))))))))

/-- Entry to the real decimal extraction loop for the first value, which is one. -/
def spike2Row7AfterValueSetup : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx)
    (X86_64Instruction.step (mov_r64_imm64 .r10 10)
      (X86_64Instruction.step (mov_r64 .rax .r14) spike2Row7AfterIndex))

/-- The first decimal extraction pass for Row 7's two-digit value. -/
def spike2Row7AfterExtractionFirst : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 236)
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
              (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row7AfterValueSetup))))))

/-- First decimal extraction pass for row seven's two-digit value. -/
def spike2Row7AfterExtraction : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 236)
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row7AfterExtractionFirst))))))

/-- The first decimal pop/write pass for Row 7's two digits. -/
def spike2Row7AfterWriteFirst : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 243)
    (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) spike2Row7AfterExtraction))))

/-- Second and final decimal write pass for row seven's two digits. -/
def spike2Row7AfterWrite : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 243)
    (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) spike2Row7AfterWriteFirst))))

/-- The line terminator stores are kept separate from decimal formatting so this certificate
matches the production formatter/write schedule one instruction at a time. -/
def spike2Row7AfterLineTerminator : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .rdi 1)
    (X86_64Instruction.step (mov_mem8 .rdi .rax)
      (X86_64Instruction.step (mov_r64_imm64 .rax 10)
        (X86_64Instruction.step (add_r64_imm8 .rdi 1)
          (X86_64Instruction.step (mov_mem8 .rdi .rax)
            (X86_64Instruction.step (mov_r64_imm64 .rax 13) spike2Row7AfterWrite)))))

/-- Register setup immediately before the production Linux `SYS_write` instruction. -/
def spike2Row7BeforeWriteSyscall : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .eax 1)
    (X86_64Instruction.step (mov_r32 .edi 1)
      (X86_64Instruction.step (mov_r64 .rdx .r8)
        (X86_64Instruction.step (sub_r64 .r8 .rsi)
          (X86_64Instruction.step (lea_rsp .rsi 0x40)
            (X86_64Instruction.step (mov_r64 .r8 .rdi) spike2Row7AfterLineTerminator)))))

/-- The host-resumed state after the real selected `SYS_write` call. -/
def spike2Row7AfterWriteSyscall : X86_64MachineState :=
  (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).1

/-- Reverse event accumulator after Row 7's selected write boundary. -/
def spike2Row7WriteEventsRev : List AnyEvent :=
  accumulateEvent [] (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).2

/-- The actual main-loop-header state reached after Row 7's recurrence and back edge. -/
def spike2Row7AfterRecurrence : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967027)
    (X86_64Instruction.step (add_r64_imm8 .r13 1)
      (X86_64Instruction.step (mov_r64 .r15 .r8)
        (X86_64Instruction.step (mov_r64 .r14 .r15)
          (X86_64Instruction.step (add_r64 .r8 .r15)
            (X86_64Instruction.step (mov_r64 .r8 .r14) spike2Row7AfterWriteSyscall)))))

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Six literal linked steps establish Row 7's one-digit index formatting path.  The JGE
fallthrough is checked at `r13 = 7`; each selected/silent fact is over the production index. -/
theorem spike2_row7_index_header_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      (spike2AfterMainHeader spike2Row6AfterRecurrence) ([] : List AnyEvent)
      spike2Row7AfterIndexHeader [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary sequentialMovRspByte40 ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x41 0x69
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .movRspByte 0x42 0x62
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .movRspByte 0x43 0x28
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialCmp .r13 10) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.conditionalFallthrough (.jge8 41) (by
              simp only [X86BranchCondition.holds]
              decide)
              ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · exact .nil _ _

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- The selected one-digit index formatting path is ten literal instructions and joins the
production value formatter at its real linked target. -/
theorem spike2_row7_index_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 10
      spike2Row7AfterIndexHeader ([] : List AnyEvent) spike2Row7AfterIndex [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .rax .r13).sequential
    ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .addImm8 .rax 0x30
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .leaRsp .rdi 0x44
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .movMem8 .rdi .rax
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .movRspByte 0x45 0x29
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.ordinary ({
              encoding := .movRspByte 0x46 0x20
              safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · refine ProductionPrefix.SelectedPrefix.ordinary ({
                encoding := .movRspByte 0x47 0x3d
                safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
              · rfl
              · decide
              · decide
              · rfl
              · refine ProductionPrefix.SelectedPrefix.ordinary ({
                  encoding := .movRspByte 0x48 0x20
                  safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
                · rfl
                · decide
                · decide
                · rfl
                · refine ProductionPrefix.SelectedPrefix.ordinary ({
                    encoding := .leaRsp .rdi 0x49
                    safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
                  · rfl
                  · decide
                  · decide
                  · rfl
                  · refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent)
                      (.rel8 65) ?_ ?_ ?_ ?_ ?_
                    · rfl
                    · decide
                    · decide
                    · rfl
                    · exact .nil _ _

/-- The three instructions that seed the production decimal formatter for Row 7's two-digit value. -/
theorem spike2_row7_value_setup_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 3
      spike2Row7AfterIndex ([] : List AnyEvent) spike2Row7AfterValueSetup [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .rax .r14).sequential
    ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.loadImm .r10 10).sequential
      ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .xor32 .ecx .ecx
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · exact .nil _ _

/-- Row 7's first decimal extraction pass takes the real JNE edge into the second pass.  This is
the actual seven-instruction production loop body. -/
theorem spike2_row7_extraction_first_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7
      spike2Row7AfterValueSetup ([] : List AnyEvent) spike2Row7AfterExtractionFirst [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .xor32 .edx .edx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary sequentialDivR10 ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · decide
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdx 0x30
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .push .rdx
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .addImm8 .rcx 1
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialCmp .rax 0)
              ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · refine ProductionPrefix.SelectedPrefix.conditionalTaken (.jne8 236)
                (by
                  simp only [X86BranchCondition.holds]
                  decide)
                ?_ ?_ ?_ ?_ ?_
              · rfl
              · decide
              · decide
              · rfl
              · exact .nil _ _

theorem spike2_row7_extraction_second_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7
      spike2Row7AfterExtractionFirst ([] : List AnyEvent) spike2Row7AfterExtraction [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .xor32 .edx .edx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary sequentialDivR10 ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · decide
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdx 0x30
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .push .rdx
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .addImm8 .rcx 1
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.ordinary (sequentialCmp .rax 0)
              ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · refine ProductionPrefix.SelectedPrefix.conditionalFallthrough (.jne8 236)
                (by
                  simp only [X86BranchCondition.holds]
                  decide)
                ?_ ?_ ?_ ?_ ?_
              · rfl
              · decide
              · decide
              · rfl
              · exact .nil _ _

theorem spike2_row7_extraction_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 14
      spike2Row7AfterValueSetup ([] : List AnyEvent) spike2Row7AfterExtraction [] [] := by
  have first := spike2_row7_extraction_first_selected_prefix
  have second := spike2_row7_extraction_second_selected_prefix
  simpa using ProductionPrefix.SelectedPrefix.append first second
/-- Row 7's first decimal digit is written by the actual five-instruction pop loop. -/
theorem spike2_row7_write_first_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5
      spike2Row7AfterExtraction ([] : List AnyEvent) spike2Row7AfterWriteFirst [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .pop .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movMem8 .rdi .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdi 1
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .subImm8 .rcx 1
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.conditionalTaken (.jne8 243)
            (by
              simp only [X86BranchCondition.holds]
              decide)
            ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · exact .nil _ _

theorem spike2_row7_write_second_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5
      spike2Row7AfterWriteFirst ([] : List AnyEvent) spike2Row7AfterWrite [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .pop .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movMem8 .rdi .rdx
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdi 1
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .subImm8 .rcx 1
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.conditionalFallthrough (.jne8 243)
            (by
              simp only [X86BranchCondition.holds]
              decide)
            ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · exact .nil _ _

theorem spike2_row7_write_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 10
      spike2Row7AfterExtraction ([] : List AnyEvent) spike2Row7AfterWrite [] [] := by
  have first := spike2_row7_write_first_selected_prefix
  have second := spike2_row7_write_second_selected_prefix
  simpa using ProductionPrefix.SelectedPrefix.append first second
/-- The CR/LF suffix is six concrete silent production instructions. -/
theorem spike2_row7_line_terminator_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row7AfterWrite ([] : List AnyEvent) spike2Row7AfterLineTerminator [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.loadImm .rax 13).sequential
    ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movMem8 .rdi .rax
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .addImm8 .rdi 1
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.loadImm .rax 10).sequential
          ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .movMem8 .rdi .rax
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.ordinary ({
              encoding := .addImm8 .rdi 1
              safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · exact .nil _ _

/-- Six exact register moves prepare the linked Linux write transition. -/
theorem spike2_row7_write_setup_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row7AfterLineTerminator ([] : List AnyEvent) spike2Row7BeforeWriteSyscall [] [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .r8 .rdi).sequential
    ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .leaRsp .rsi 0x40
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.sub .r8 .rsi).sequential
        ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .rdx .r8).sequential
          ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .mov32 .edi 1
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.ordinary ({
              encoding := .mov32 .eax 1
              safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · exact .nil _ _

/-- The linked `syscall` is selected as `SYS_write`, is intercepted by the production Linux
dispatcher, and resumes at the real return address with its emitted console event. -/
theorem spike2_row7_write_syscall_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      spike2Row7BeforeWriteSyscall ([] : List AnyEvent) spike2Row7AfterWriteSyscall
      (accumulateEvent [] (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).2)
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).2) := by
  have hstep : X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall =
      { (spike2Row7BeforeWriteSyscall.setGpr64 .rcx
          (spike2Row7BeforeWriteSyscall.rip + 2)).setGpr64 .r11
          spike2Row7BeforeWriteSyscall.flags with rip := linuxSyscallEntry } := rfl
  have hrax : (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).gprs .rax =
      SYS_write := by rfl
  have hstdout : (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).gprs .rdi =
      1 := by rfl
  have hrip : (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).rip =
      linuxSyscallEntry := by rw [hstep]
  have hsafe : (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).fault = none := by
    rfl
  refine ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
    (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed) (.syscall)
    (hooked := spike2Row7AfterWriteSyscall)
    (event := (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).2) ?_ ?_ ?_ ?_ ?_
  · rfl
  · change selectedNonInputPlatformCall
      (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).rip
      (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall) = true
    rw [selectedNonInputPlatformCall, hrip]
    simp [selectedNonInputLinuxCall, hrax, SYS_write, linuxSyscallEntry]
  · change (if (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).rip ==
      linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = some _
    rw [hrip]
    simp [linuxSyscallIntercept, hrax, hstdout, SYS_write, sysWriteHook, linuxSyscallEntry]
    rfl
  · unfold spike2Row7AfterWriteSyscall
    simp only [sysWriteHook, hstdout, ↓reduceIte]
    change (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall).fault = none
    exact hsafe
  · exact .nil _ _

/-- The real Fibonacci register update and linked `jmp near main_loop` complete Row 7. -/
theorem spike2_row7_recurrence_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row7AfterWriteSyscall spike2Row7WriteEventsRev spike2Row7AfterRecurrence
      spike2Row7WriteEventsRev [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .r8 .r14).sequential
    ?_ ?_ ?_ ?_ ?_
  · rfl
  · decide
  · decide
  · rfl
  · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.add .r8 .r15).sequential
      ?_ ?_ ?_ ?_ ?_
    · rfl
    · decide
    · decide
    · rfl
    · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .r14 .r15).sequential
        ?_ ?_ ?_ ?_ ?_
      · rfl
      · decide
      · decide
      · rfl
      · refine ProductionPrefix.SelectedPrefix.ordinary (ControlFlowFree.mov .r15 .r8).sequential
          ?_ ?_ ?_ ?_ ?_
        · rfl
        · decide
        · decide
        · rfl
        · refine ProductionPrefix.SelectedPrefix.ordinary ({
            encoding := .addImm8 .r13 1
            safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
          · rfl
          · decide
          · decide
          · rfl
          · refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent)
              (.rel32 4294967027) ?_ ?_ ?_ ?_ ?_
            · rfl
            · decide
            · decide
            · rfl
            · exact .nil _ _

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Eighteen actual Row 7 transitions compose from the linked main header through the one-digit
index-formatting join; no evaluator result is used as a substitute for these instructions. -/
theorem spike2_row7_opening_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 18
      spike2Row6AfterRecurrence ([] : List AnyEvent) spike2Row7AfterIndex [] [] := by
  have header := spike2_main_header_selected_prefix 6 spike2Row6AfterRecurrence ([] : List AnyEvent)
    (by omega) rfl rfl rfl
  have opening := ProductionPrefix.SelectedPrefix.append header
    spike2_row7_index_header_selected_prefix
  have joined := ProductionPrefix.SelectedPrefix.append opening spike2_row7_index_selected_prefix
  simpa using joined

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- A complete finite certificate for the seventh production Fibonacci row.  Its 64 transitions
include the linked formatter loops, selected `SYS_write` boundary, recurrence, and main-loop
back edge; it is composed only from exact production prefixes. -/
theorem spike2_row7_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 64
      spike2Row6AfterRecurrence ([] : List AnyEvent) spike2Row7AfterRecurrence spike2Row7WriteEventsRev
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row7BeforeWriteSyscall)).2) := by
  have opening := spike2_row7_opening_selected_prefix
  have valueSetup := ProductionPrefix.SelectedPrefix.append opening
    spike2_row7_value_setup_selected_prefix
  have extraction := ProductionPrefix.SelectedPrefix.append valueSetup
    spike2_row7_extraction_selected_prefix
  have write := ProductionPrefix.SelectedPrefix.append extraction spike2_row7_write_selected_prefix
  have terminator := ProductionPrefix.SelectedPrefix.append write
    spike2_row7_line_terminator_selected_prefix
  have writeSetup := ProductionPrefix.SelectedPrefix.append terminator
    spike2_row7_write_setup_selected_prefix
  have writeSyscall := ProductionPrefix.SelectedPrefix.append writeSetup
    spike2_row7_write_syscall_selected_prefix
  have recurrence := ProductionPrefix.SelectedPrefix.append writeSyscall
    spike2_row7_recurrence_selected_prefix
  simpa [spike2Row7WriteEventsRev] using recurrence

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Boundary facts exported for the finite 90-row driver composition.  They expose only the
machine fields that genuinely vary across rows, leaving this instruction certificate cached. -/
theorem spike2_row7_after_recurrence_boundary :
    spike2Row7AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row7AfterRecurrence.gprs .r13 = 8 ∧
    spike2Row7AfterRecurrence.gprs .r14 = 21 ∧
    spike2Row7AfterRecurrence.gprs .r15 = 34 ∧
    spike2Row7AfterRecurrence.rsp = spike2Row6AfterRecurrence.rsp ∧
    spike2Row7AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux

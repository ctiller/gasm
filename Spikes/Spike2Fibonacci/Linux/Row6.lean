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
import Spikes.Spike2Fibonacci.Linux.Row5

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
def spike2Row6AfterIndexHeader : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41)
    (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
              (spike2AfterMainHeader spike2Row5AfterRecurrence))))))

/-- The real joined value-format entry reached by the row-one one-digit branch. -/
def spike2Row6AfterIndex : X86_64MachineState :=
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
                      spike2Row6AfterIndexHeader)))))))))

/-- Entry to the real decimal extraction loop for the first value, which is one. -/
def spike2Row6AfterValueSetup : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx)
    (X86_64Instruction.step (mov_r64_imm64 .r10 10)
      (X86_64Instruction.step (mov_r64 .rax .r14) spike2Row6AfterIndex))

/-- The terminating single extraction pass for row one's value. -/
def spike2Row6AfterExtraction : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 236)
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row6AfterValueSetup))))))

/-- The terminating pop/write pass which materializes row one's sole decimal digit. -/
def spike2Row6AfterWrite : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 243)
    (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) spike2Row6AfterExtraction))))

/-- The line terminator stores are kept separate from decimal formatting so this certificate
matches the production formatter/write schedule one instruction at a time. -/
def spike2Row6AfterLineTerminator : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .rdi 1)
    (X86_64Instruction.step (mov_mem8 .rdi .rax)
      (X86_64Instruction.step (mov_r64_imm64 .rax 10)
        (X86_64Instruction.step (add_r64_imm8 .rdi 1)
          (X86_64Instruction.step (mov_mem8 .rdi .rax)
            (X86_64Instruction.step (mov_r64_imm64 .rax 13) spike2Row6AfterWrite)))))

/-- Register setup immediately before the production Linux `SYS_write` instruction. -/
def spike2Row6BeforeWriteSyscall : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .eax 1)
    (X86_64Instruction.step (mov_r32 .edi 1)
      (X86_64Instruction.step (mov_r64 .rdx .r8)
        (X86_64Instruction.step (sub_r64 .r8 .rsi)
          (X86_64Instruction.step (lea_rsp .rsi 0x40)
            (X86_64Instruction.step (mov_r64 .r8 .rdi) spike2Row6AfterLineTerminator)))))

/-- The host-resumed state after the real selected `SYS_write` call. -/
def spike2Row6AfterWriteSyscall : X86_64MachineState :=
  (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).1

/-- Reverse event accumulator after row one's selected write boundary. -/
def spike2Row6WriteEventsRev : List AnyEvent :=
  accumulateEvent [] (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2

/-- The actual main-loop-header state reached after row one's recurrence and back edge. -/
def spike2Row6AfterRecurrence : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967027)
    (X86_64Instruction.step (add_r64_imm8 .r13 1)
      (X86_64Instruction.step (mov_r64 .r15 .r8)
        (X86_64Instruction.step (mov_r64 .r14 .r15)
          (X86_64Instruction.step (add_r64 .r8 .r15)
            (X86_64Instruction.step (mov_r64 .r8 .r14) spike2Row6AfterWriteSyscall)))))

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Six literal linked steps establish the first row's one-digit formatting path.  The JGE
fallthrough is checked at `r13 = 1`; each selected/silent fact is over the production index. -/
theorem spike2_row6_index_header_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      (spike2AfterMainHeader spike2Row5AfterRecurrence) ([] : List AnyEvent)
      spike2Row6AfterIndexHeader [] [] := by
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
theorem spike2_row6_index_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 10
      spike2Row6AfterIndexHeader ([] : List AnyEvent) spike2Row6AfterIndex [] [] := by
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

/-- The three instructions that seed the production decimal formatter for row one's value. -/
theorem spike2_row6_value_setup_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 3
      spike2Row6AfterIndex ([] : List AnyEvent) spike2Row6AfterValueSetup [] [] := by
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

/-- Row one's value is one, so its sole division/push extraction pass takes the real JNE
fallthrough.  This is the actual seven-instruction production loop body. -/
theorem spike2_row6_extraction_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 7
      spike2Row6AfterValueSetup ([] : List AnyEvent) spike2Row6AfterExtraction [] [] := by
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

/-- Row one's sole pushed digit is written by the actual five-instruction pop loop. -/
theorem spike2_row6_write_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5
      spike2Row6AfterExtraction ([] : List AnyEvent) spike2Row6AfterWrite [] [] := by
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

/-- The CR/LF suffix is six concrete silent production instructions. -/
theorem spike2_row6_line_terminator_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row6AfterWrite ([] : List AnyEvent) spike2Row6AfterLineTerminator [] [] := by
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
theorem spike2_row6_write_setup_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row6AfterLineTerminator ([] : List AnyEvent) spike2Row6BeforeWriteSyscall [] [] := by
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
theorem spike2_row6_write_syscall_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      spike2Row6BeforeWriteSyscall ([] : List AnyEvent) spike2Row6AfterWriteSyscall
      (accumulateEvent [] (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2)
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2) := by
  have hstep : X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall =
      { (spike2Row6BeforeWriteSyscall.setGpr64 .rcx
          (spike2Row6BeforeWriteSyscall.rip + 2)).setGpr64 .r11
          spike2Row6BeforeWriteSyscall.flags with rip := linuxSyscallEntry } := rfl
  have hrax : (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).gprs .rax =
      SYS_write := by rfl
  have hstdout : (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).gprs .rdi =
      1 := by rfl
  have hrip : (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).rip =
      linuxSyscallEntry := by rw [hstep]
  have hsafe : (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).fault = none := by
    rfl
  refine ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
    (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed) (.syscall)
    (hooked := spike2Row6AfterWriteSyscall)
    (event := (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2) ?_ ?_ ?_ ?_ ?_
  · rfl
  · change selectedNonInputPlatformCall
      (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).rip
      (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall) = true
    rw [selectedNonInputPlatformCall, hrip]
    simp [selectedNonInputLinuxCall, hrax, SYS_write, linuxSyscallEntry]
  · change (if (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).rip ==
      linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = some _
    rw [hrip]
    simp [linuxSyscallIntercept, hrax, hstdout, SYS_write, sysWriteHook, linuxSyscallEntry]
    rfl
  · unfold spike2Row6AfterWriteSyscall
    simp only [sysWriteHook, hstdout, ↓reduceIte]
    change (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall).fault = none
    exact hsafe
  · exact .nil _ _

/-- The real Fibonacci register update and linked `jmp near main_loop` complete row one. -/
theorem spike2_row6_recurrence_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row6AfterWriteSyscall spike2Row6WriteEventsRev spike2Row6AfterRecurrence
      spike2Row6WriteEventsRev [] := by
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
/-- The first eighteen actual row transitions compose from the linked main header through the
one-digit formatting join; no evaluator result is used as a substitute for these instructions. -/
theorem spike2_row6_opening_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 18
      spike2Row5AfterRecurrence ([] : List AnyEvent) spike2Row6AfterIndex [] [] := by
  have header := spike2_main_header_selected_prefix 5 spike2Row5AfterRecurrence ([] : List AnyEvent)
    (by omega) rfl rfl rfl
  have opening := ProductionPrefix.SelectedPrefix.append header
    spike2_row6_index_header_selected_prefix
  have joined := ProductionPrefix.SelectedPrefix.append opening spike2_row6_index_selected_prefix
  simpa using joined

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- A complete finite certificate for the first production Fibonacci row.  Its 52 transitions
include the linked formatter loops, selected `SYS_write` boundary, recurrence, and main-loop
back edge; it is composed only from exact production prefixes. -/
theorem spike2_row6_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 52
      spike2Row5AfterRecurrence ([] : List AnyEvent) spike2Row6AfterRecurrence spike2Row6WriteEventsRev
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2) := by
  have opening := spike2_row6_opening_selected_prefix
  have valueSetup := ProductionPrefix.SelectedPrefix.append opening
    spike2_row6_value_setup_selected_prefix
  have extraction := ProductionPrefix.SelectedPrefix.append valueSetup
    spike2_row6_extraction_selected_prefix
  have write := ProductionPrefix.SelectedPrefix.append extraction spike2_row6_write_selected_prefix
  have terminator := ProductionPrefix.SelectedPrefix.append write
    spike2_row6_line_terminator_selected_prefix
  have writeSetup := ProductionPrefix.SelectedPrefix.append terminator
    spike2_row6_write_setup_selected_prefix
  have writeSyscall := ProductionPrefix.SelectedPrefix.append writeSetup
    spike2_row6_write_syscall_selected_prefix
  have recurrence := ProductionPrefix.SelectedPrefix.append writeSyscall
    spike2_row6_recurrence_selected_prefix
  simpa [spike2Row6WriteEventsRev] using recurrence

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Boundary facts exported for the finite 90-row driver composition.  They expose only the
machine fields that genuinely vary across rows, leaving this instruction certificate cached. -/
theorem spike2_row6_after_recurrence_boundary :
    spike2Row6AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row6AfterRecurrence.gprs .r13 = 7 ∧
    spike2Row6AfterRecurrence.gprs .r14 = 13 ∧
    spike2Row6AfterRecurrence.gprs .r15 = 21 ∧
    spike2Row6AfterRecurrence.rsp = spike2Row5AfterRecurrence.rsp ∧
    spike2Row6AfterRecurrence.fault = none := by
  decide

/-- The exact reverse accumulator after rebasing rows two through six beneath row one.
`rebaseEvents_empty` is applicable here only because each imported row certificate was already
checked from the empty accumulator; it cannot manufacture a row transition or change its state. -/
def spike2Rows1To6EventsRev : List AnyEvent :=
  (emittedBy (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2).reverse ++
  (emittedBy (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row5BeforeWriteSyscall)).2).reverse ++
  (emittedBy (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row4BeforeWriteSyscall)).2).reverse ++
  (emittedBy (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2).reverse ++
  (emittedBy (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
  spike2Row1WriteEventsRev

theorem spike2_rows1_to6_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 312
      spike2AfterPrologue ([] : List AnyEvent) spike2Row6AfterRecurrence
      spike2Rows1To6EventsRev
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row1BeforeWriteSyscall)).2 ++
       emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2 ++
       emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2 ++
       emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row4BeforeWriteSyscall)).2 ++
       emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row5BeforeWriteSyscall)).2 ++
       emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2) := by
  have row2 := spike2_row2_selected_prefix.rebaseEvents_empty spike2Row1WriteEventsRev
  have rows12 := ProductionPrefix.SelectedPrefix.append spike2_row1_selected_prefix row2
  have row3 := spike2_row3_selected_prefix.rebaseEvents_empty
    ((emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
      spike2Row1WriteEventsRev)
  have rows123 := ProductionPrefix.SelectedPrefix.append rows12 row3
  have row4 := spike2_row4_selected_prefix.rebaseEvents_empty
    ((emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
      spike2Row1WriteEventsRev)
  have rows1234 := ProductionPrefix.SelectedPrefix.append rows123 row4
  have row5 := spike2_row5_selected_prefix.rebaseEvents_empty
    ((emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row4BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
      spike2Row1WriteEventsRev)
  have rows12345 := ProductionPrefix.SelectedPrefix.append rows1234 row5
  have row6 := spike2_row6_selected_prefix.rebaseEvents_empty
    ((emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row5BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row4BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row3BeforeWriteSyscall)).2).reverse ++
     (emittedBy (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row2BeforeWriteSyscall)).2).reverse ++
      spike2Row1WriteEventsRev)
  have rows123456 := ProductionPrefix.SelectedPrefix.append rows12345 row6
  simpa [spike2Rows1To6EventsRev] using rows123456

end Spikes.Spike2Fibonacci.Linux

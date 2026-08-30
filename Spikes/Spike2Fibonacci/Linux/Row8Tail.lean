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
import Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

/-!
# Row 8 formatter tail and output boundary

This producer-local tail proves the CR/LF stores, write setup, selected Linux output transition,
and recurrence separately from the decimal formatter's cached certificate.
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
open Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- The CR/LF suffix is six exact silent production instructions. -/
theorem spike2_row8_line_terminator_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row8AfterWrite ([] : List AnyEvent) spike2Row8AfterLineTerminator [] [] := by
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

/-- Six exact moves prepare the linked Linux write transition. -/
theorem spike2_row8_write_setup_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row8AfterLineTerminator ([] : List AnyEvent) spike2Row8BeforeWriteSyscall [] [] := by
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

/-- The production `SYS_write` transition is selected, intercepted, and resumes safely with its
emitted event.  The evidence is limited to the syscall's ABI fields and hook result. -/
theorem spike2_row8_write_syscall_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      spike2Row8BeforeWriteSyscall ([] : List AnyEvent) spike2Row8AfterWriteSyscall
      spike2Row8WriteEventsRev
      (emittedBy (sysWriteHook (Event := AnyEvent)
        (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall)).2) := by
  have hstep : X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall =
      { (spike2Row8BeforeWriteSyscall.setGpr64 .rcx
          (spike2Row8BeforeWriteSyscall.rip + 2)).setGpr64 .r11
          spike2Row8BeforeWriteSyscall.flags with rip := linuxSyscallEntry } := rfl
  have hrax : (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).gprs .rax =
      SYS_write := by rfl
  have hstdout : (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).gprs .rdi =
      1 := by rfl
  have hrip : (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).rip =
      linuxSyscallEntry := by rw [hstep]
  have hsafe : (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).fault = none := by
    rfl
  refine ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
    (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed) (.syscall)
    (hooked := spike2Row8AfterWriteSyscall)
    (event := (sysWriteHook (Event := AnyEvent)
      (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall)).2) ?_ ?_ ?_ ?_ ?_
  · rfl
  · change selectedNonInputPlatformCall
      (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).rip
      (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall) = true
    rw [selectedNonInputPlatformCall, hrip]
    simp [selectedNonInputLinuxCall, hrax, SYS_write, linuxSyscallEntry]
  · change (if (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).rip ==
      linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = some _
    rw [hrip]
    simp [linuxSyscallIntercept, hrax, hstdout, SYS_write, sysWriteHook, linuxSyscallEntry]
    rfl
  · unfold spike2Row8AfterWriteSyscall
    simp only [sysWriteHook, hstdout]
    change (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall).fault = none
    exact hsafe
  · exact .nil _ _

/-- The Fibonacci register update and linked main-loop back edge complete Row 8. -/
theorem spike2_row8_recurrence_selected_prefix :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      spike2Row8AfterWriteSyscall spike2Row8WriteEventsRev spike2Row8AfterRecurrence
      spike2Row8WriteEventsRev [] := by
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

end Spikes.Spike2Fibonacci.Linux

/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.NativeAdapter

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- The loop-counter increment transition. -/
def spike2AfterRecurrenceIncrement (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .r13 1) state

private theorem sequentialRecurrenceIncrement : SequentialInstruction (add_r64_imm8 .r13 1) where
  encoding := .addImm8 .r13 1
  safeFallthrough := by intro state _; rfl

private theorem selected_silent_unaligned (state : X86_64MachineState) (address : UInt64)
    (hrip : state.rip = address) (notLinux : address ≠ linuxSyscallEntry)
    (unaligned : address % 8 ≠ 0) :
    selectedNonInputPlatformCall address state = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ address state = none := by
  constructor
  · simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, hrip, unaligned]
  · change Gasm.Targets.Windows.win32Intercept (Event := AnyEvent) address state = none
    simp [Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex, hrip, unaligned]

theorem spike2_recurrence_increment_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713535) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (spike2AfterRecurrenceIncrement state) eventsRev [] := by
  have hnext : (spike2AfterRecurrenceIncrement state).rip = 5368713539 := by
    unfold spike2AfterRecurrenceIncrement
    rw [show (X86_64Instruction.step (add_r64_imm8 .r13 1) state).rip =
      state.rip + (X86_64Instruction.encode (add_r64_imm8 .r13 1)).size.toUInt64 from
      (sequentialRecurrenceIncrement.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  have hboundary := selected_silent_unaligned (spike2AfterRecurrenceIncrement state) 5368713539
    hnext (by decide) (by decide)
  have hselected : selectedNonInputPlatformCall
      (X86_64Instruction.step (add_r64_imm8 .r13 1) state).rip
      (X86_64Instruction.step (add_r64_imm8 .r13 1) state) = true := by
    change selectedNonInputPlatformCall (spike2AfterRecurrenceIncrement state).rip
      (spike2AfterRecurrenceIncrement state) = true
    rw [hnext]
    exact hboundary.1
  have hsilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (add_r64_imm8 .r13 1) state).rip
      (X86_64Instruction.step (add_r64_imm8 .r13 1) state) = none := by
    change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterRecurrenceIncrement state).rip (spike2AfterRecurrenceIncrement state) = none
    rw [hnext]
    exact hboundary.2
  refine ProductionPrefix.SelectedPrefix.ordinary sequentialRecurrenceIncrement
    (by simpa [hrip] using spike2Recurrence_inc_fetch) hselected hsilent ?_ (.nil _ _)
  change state.fault = none
  exact hsafe

theorem spike2_recurrence_increment_effect (state : X86_64MachineState) :
    (spike2AfterRecurrenceIncrement state).gprs .r13 = state.gprs .r13 + 1 := by
  rfl

theorem spike2_recurrence_increment_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713535) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceIncrement state).rip = 5368713539 ∧
    (spike2AfterRecurrenceIncrement state).fault = none := by
  constructor
  · unfold spike2AfterRecurrenceIncrement
    rw [show (X86_64Instruction.step (add_r64_imm8 .r13 1) state).rip =
      state.rip + (X86_64Instruction.encode (add_r64_imm8 .r13 1)).size.toUInt64 from
      (sequentialRecurrenceIncrement.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  · change state.fault = none
    exact hsafe

end Spikes.Spike2Fibonacci.Windows

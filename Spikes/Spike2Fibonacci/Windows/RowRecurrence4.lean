/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.NativeAdapter

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRecurrence4 :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- The `mov r15, r8` transition of the recurrence. -/
def spike2AfterRecurrenceMove15 (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_r64 .r15 .r8) state

private theorem sequentialRecurrenceMove15 : SequentialInstruction (mov_r64 .r15 .r8) where
  encoding := .mov .r15 .r8
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

theorem spike2_recurrence_move15_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713532) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (spike2AfterRecurrenceMove15 state) eventsRev [] := by
  have hnext : (spike2AfterRecurrenceMove15 state).rip = 5368713535 := by
    unfold spike2AfterRecurrenceMove15
    rw [show (X86_64Instruction.step (mov_r64 .r15 .r8) state).rip =
      state.rip + (X86_64Instruction.encode (mov_r64 .r15 .r8)).size.toUInt64 from
      (sequentialRecurrenceMove15.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  have hboundary := selected_silent_unaligned (spike2AfterRecurrenceMove15 state) 5368713535
    hnext (by decide) (by decide)
  have hselected : selectedNonInputPlatformCall
      (X86_64Instruction.step (mov_r64 .r15 .r8) state).rip
      (X86_64Instruction.step (mov_r64 .r15 .r8) state) = true := by
    change selectedNonInputPlatformCall (spike2AfterRecurrenceMove15 state).rip
      (spike2AfterRecurrenceMove15 state) = true
    rw [hnext]
    exact hboundary.1
  have hsilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (mov_r64 .r15 .r8) state).rip
      (X86_64Instruction.step (mov_r64 .r15 .r8) state) = none := by
    change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterRecurrenceMove15 state).rip (spike2AfterRecurrenceMove15 state) = none
    rw [hnext]
    exact hboundary.2
  refine ProductionPrefix.SelectedPrefix.ordinary sequentialRecurrenceMove15
    (by simpa [hrip] using spike2Recurrence_mov15_fetch) hselected hsilent ?_ (.nil _ _)
  change state.fault = none
  exact hsafe

theorem spike2_recurrence_move15_effect (state : X86_64MachineState) :
    (spike2AfterRecurrenceMove15 state).gprs .r14 = state.gprs .r14 ∧
    (spike2AfterRecurrenceMove15 state).gprs .r15 = state.gprs .r8 := by
  exact ⟨rfl, rfl⟩

theorem spike2_recurrence_move15_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713532) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceMove15 state).rip = 5368713535 ∧
    (spike2AfterRecurrenceMove15 state).fault = none := by
  constructor
  · unfold spike2AfterRecurrenceMove15
    rw [show (X86_64Instruction.step (mov_r64 .r15 .r8) state).rip =
      state.rip + (X86_64Instruction.encode (mov_r64 .r15 .r8)).size.toUInt64 from
      (sequentialRecurrenceMove15.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  · change state.fault = none
    exact hsafe

end Spikes.Spike2Fibonacci.Windows

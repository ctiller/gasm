/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.NativeAdapter

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- The first concrete recurrence transition after the WriteFile hook. -/
def spike2AfterRecurrenceMove (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_r64 .r8 .r14) state

private theorem sequentialRecurrenceMove : SequentialInstruction (mov_r64 .r8 .r14) where
  encoding := .mov .r8 .r14
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

/-- Exact selected certificate for only `mov r8, r14`.  The next producer consumes the opaque
post-move state rather than expanding the preceding WriteFile certificate. -/
theorem spike2_recurrence_move_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713523) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (spike2AfterRecurrenceMove state) eventsRev [] := by
  have hnext : (spike2AfterRecurrenceMove state).rip = 5368713526 := by
    unfold spike2AfterRecurrenceMove
    rw [show (X86_64Instruction.step (mov_r64 .r8 .r14) state).rip =
      state.rip + (X86_64Instruction.encode (mov_r64 .r8 .r14)).size.toUInt64 from
      (sequentialRecurrenceMove.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  have hboundary := selected_silent_unaligned (spike2AfterRecurrenceMove state) 5368713526
    hnext (by decide) (by decide)
  have hselected : selectedNonInputPlatformCall
      (X86_64Instruction.step (mov_r64 .r8 .r14) state).rip
      (X86_64Instruction.step (mov_r64 .r8 .r14) state) = true := by
    change selectedNonInputPlatformCall (spike2AfterRecurrenceMove state).rip
      (spike2AfterRecurrenceMove state) = true
    rw [hnext]
    exact hboundary.1
  have hsilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (mov_r64 .r8 .r14) state).rip
      (X86_64Instruction.step (mov_r64 .r8 .r14) state) = none := by
    change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterRecurrenceMove state).rip (spike2AfterRecurrenceMove state) = none
    rw [hnext]
    exact hboundary.2
  refine ProductionPrefix.SelectedPrefix.ordinary sequentialRecurrenceMove
    (by simpa [hrip] using spike2Recurrence_mov_fetch) hselected hsilent ?_ (.nil _ _)
  change state.fault = none
  exact hsafe

/-- Minimal recurrence observation exported to the next body producer. -/
theorem spike2_recurrence_move_effect (state : X86_64MachineState) :
    (spike2AfterRecurrenceMove state).gprs .r8 = state.gprs .r14 ∧
    (spike2AfterRecurrenceMove state).gprs .r14 = state.gprs .r14 ∧
    (spike2AfterRecurrenceMove state).gprs .r15 = state.gprs .r15 := by
  exact ⟨rfl, rfl, rfl⟩

theorem spike2_recurrence_move_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713523) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceMove state).rip = 5368713526 ∧
    (spike2AfterRecurrenceMove state).fault = none := by
  constructor
  · unfold spike2AfterRecurrenceMove
    rw [show (X86_64Instruction.step (mov_r64 .r8 .r14) state).rip =
      state.rip + (X86_64Instruction.encode (mov_r64 .r8 .r14)).size.toUInt64 from
      (sequentialRecurrenceMove.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  · change state.fault = none
    exact hsafe

end Spikes.Spike2Fibonacci.Windows

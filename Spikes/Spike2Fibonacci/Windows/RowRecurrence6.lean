/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.NativeAdapter

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- The linked direct branch that returns from the recurrence tail to the driver header. -/
def spike2AfterRecurrenceBackedge (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967019) state

private theorem jmpRel32_preserves_fault (displacement : Int32) (state : X86_64MachineState) :
    (X86_64Instruction.step (jmp_rel32 displacement) state).fault = state.fault := by
  rfl

private theorem jmpRel32_preserves_rsp (displacement : Int32) (state : X86_64MachineState) :
    (X86_64Instruction.step (jmp_rel32 displacement) state).rsp = state.rsp := by
  rfl

private theorem jmpRel32_preserves_gpr (displacement : Int32) (state : X86_64MachineState)
    (register : Reg64) :
    (X86_64Instruction.step (jmp_rel32 displacement) state).gprs register =
      state.gprs register := by
  rfl

private theorem jmpRel32_preserves_memory (displacement : Int32) (state : X86_64MachineState) :
    (X86_64Instruction.step (jmp_rel32 displacement) state).memory = state.memory := by
  rfl

private theorem selected_silent_unaligned (state : X86_64MachineState) (address : UInt64)
    (hrip : state.rip = address) (notLinux : address ≠ linuxSyscallEntry)
    (unaligned : address % 8 ≠ 0) :
    selectedNonInputPlatformCall address state = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ address state = none := by
  constructor
  · simp [selectedNonInputPlatformCall, notLinux, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, hrip, unaligned]
  · change (if address == linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = none
    simp [notLinux, Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex, hrip, unaligned]

/-- Exact selected certificate for the concrete recurrence back edge. -/
theorem spike2_recurrence_backedge_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713539) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (spike2AfterRecurrenceBackedge state) eventsRev [] := by
  have hnext : (spike2AfterRecurrenceBackedge state).rip = spike2WindowsMainLoopRip := by
    change state.rip + 5 + signExtend32To64 4294967019 = spike2WindowsMainLoopRip
    rw [hrip]
    rfl
  have hboundary := selected_silent_unaligned (spike2AfterRecurrenceBackedge state)
    spike2WindowsMainLoopRip hnext (by decide) (by decide)
  have hselected : selectedNonInputPlatformCall
      (X86_64Instruction.step (jmp_rel32 4294967019) state).rip
      (X86_64Instruction.step (jmp_rel32 4294967019) state) = true := by
    change selectedNonInputPlatformCall (spike2AfterRecurrenceBackedge state).rip
      (spike2AfterRecurrenceBackedge state) = true
    rw [hnext]
    exact hboundary.1
  have hsilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (jmp_rel32 4294967019) state).rip
      (X86_64Instruction.step (jmp_rel32 4294967019) state) = none := by
    change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterRecurrenceBackedge state).rip (spike2AfterRecurrenceBackedge state) = none
    rw [hnext]
    exact hboundary.2
  refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent) (.rel32 4294967019)
    ?_ hselected hsilent ?_ (.nil _ _)
  · rw [hrip]
    exact spike2Recurrence_backedge_fetch
  rw [jmpRel32_preserves_fault]
  exact hsafe

theorem spike2_recurrence_backedge_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713539) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceBackedge state).rip = spike2WindowsMainLoopRip ∧
    (spike2AfterRecurrenceBackedge state).fault = none ∧
    (spike2AfterRecurrenceBackedge state).rsp = state.rsp ∧
    (spike2AfterRecurrenceBackedge state).gprs .r13 = state.gprs .r13 ∧
    (spike2AfterRecurrenceBackedge state).memory = state.memory := by
  constructor
  · change state.rip + 5 + signExtend32To64 4294967019 = spike2WindowsMainLoopRip
    rw [hrip]
    rfl
  · constructor
    · unfold spike2AfterRecurrenceBackedge
      rw [jmpRel32_preserves_fault]
      exact hsafe
    · constructor
      · exact jmpRel32_preserves_rsp 4294967019 state
      · constructor
        · exact jmpRel32_preserves_gpr 4294967019 state .r13
        · exact jmpRel32_preserves_memory 4294967019 state

end Spikes.Spike2Fibonacci.Windows

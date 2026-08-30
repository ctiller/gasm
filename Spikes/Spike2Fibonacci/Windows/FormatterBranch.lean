/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.FormatterLocal

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

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

/-- Exact selected conditional edge for a formatter branch whose condition has been established
symbolically.  The caller supplies only the linked fetch, condition, and concrete successor. -/
theorem spike2_selected_conditional_prefix {instruction : X86_64Instr} {kind : X86BranchCondition}
    (encoding : ConditionalJumpEncoding instruction kind) (state : X86_64MachineState)
    (taken : kind.holds state) (eventsRev : List AnyEvent)
    (fetch : instructionAtRipIndexed spike2Indexed state.rip = some instruction)
    (nextAddress : UInt64) (nextRip : (X86_64Instruction.step instruction state).rip = nextAddress)
    (selectedAt : selectedNonInputPlatformCall (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = true)
    (silent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step instruction state).rip (X86_64Instruction.step instruction state) = none)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (X86_64Instruction.step instruction state) eventsRev [] := by
  exact ProductionPrefix.SelectedPrefix.conditionalTaken encoding taken fetch selectedAt silent safe (.nil _ _)

/-- Exact selected fallthrough edge for a formatter branch. -/
theorem spike2_selected_conditional_fallthrough_prefix {instruction : X86_64Instr}
    {kind : X86BranchCondition} (encoding : ConditionalJumpEncoding instruction kind)
    (state : X86_64MachineState) (notTaken : ¬ kind.holds state) (eventsRev : List AnyEvent)
    (fetch : instructionAtRipIndexed spike2Indexed state.rip = some instruction)
    (nextAddress : UInt64) (nextRip : (X86_64Instruction.step instruction state).rip = nextAddress)
    (selectedAt : selectedNonInputPlatformCall (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = true)
    (silent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step instruction state).rip (X86_64Instruction.step instruction state) = none)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (X86_64Instruction.step instruction state) eventsRev [] := by
  exact ProductionPrefix.SelectedPrefix.conditionalFallthrough encoding notTaken fetch selectedAt silent safe (.nil _ _)

end Spikes.Spike2Fibonacci.Windows

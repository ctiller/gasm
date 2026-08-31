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

/-- Exact selected conditional edge for a formatter branch whose condition has been established
symbolically.  The caller supplies only the linked fetch, condition, and concrete successor. -/
theorem spike2_selected_conditional_prefix {instruction : X86_64Instr} {kind : X86BranchCondition}
    (encoding : ConditionalJumpEncoding instruction kind) (state : X86_64MachineState)
    (taken : kind.holds state) (eventsRev : List AnyEvent)
    (fetch : instructionAtRipIndexed spike2Indexed state.rip = some instruction)
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
    (selectedAt : selectedNonInputPlatformCall (X86_64Instruction.step instruction state).rip
      (X86_64Instruction.step instruction state) = true)
    (silent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step instruction state).rip (X86_64Instruction.step instruction state) = none)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (X86_64Instruction.step instruction state) eventsRev [] := by
  exact ProductionPrefix.SelectedPrefix.conditionalFallthrough encoding notTaken fetch selectedAt silent safe (.nil _ _)

end Spikes.Spike2Fibonacci.Windows

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

theorem spike2_selected_silent_unaligned (state : X86_64MachineState) (address : UInt64)
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

/-- An aligned instruction address is still an ordinary selected boundary when its memory word is
not an IAT self-reference.  Row invariants use this bridge for loop headers and branch targets,
which cannot use the syntactic unaligned-address shortcut. -/
theorem spike2_selected_silent_nonIat (state : X86_64MachineState) (address : UInt64)
    (hrip : state.rip = address) (notLinux : address ≠ linuxSyscallEntry)
    (notSelfRef : state.read64 address ≠ address) :
    selectedNonInputPlatformCall address state = true ∧
      @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _ address state = none := by
  constructor
  · simp [selectedNonInputPlatformCall, notLinux, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, notSelfRef]
  · change (if address == linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = none
    simp [notLinux, Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex, notSelfRef]

/-- One exact ordinary linked instruction at a proven non-IAT boundary.  Formatter slices supply
only their instruction/fetch and successor address; selection and silent dispatch are derived
here from the actual target classifier. -/
theorem spike2_selected_local_prefix (instruction : X86_64Instr)
    (sequential : SequentialInstruction instruction) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (fetch : instructionAtRipIndexed spike2Indexed state.rip = some instruction)
    (nextAddress : UInt64) (nextRip : (X86_64Instruction.step instruction state).rip = nextAddress)
    (notLinux : nextAddress ≠ linuxSyscallEntry) (unaligned : nextAddress % 8 ≠ 0)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (X86_64Instruction.step instruction state) eventsRev [] := by
  have hboundary := spike2_selected_silent_unaligned (X86_64Instruction.step instruction state) nextAddress
    nextRip notLinux unaligned
  refine ProductionPrefix.SelectedPrefix.ordinary sequential fetch ?_ ?_ safe (.nil _ _)
  · rw [nextRip]
    exact hboundary.1
  · rw [nextRip]
    exact hboundary.2

end Spikes.Spike2Fibonacci.Windows

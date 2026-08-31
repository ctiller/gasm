/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.NativeAdapter

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowWrite :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/-! The single real WriteFile import transition, isolated from formatter and recurrence proofs. -/

/-- The raw linked `WriteFile` CALL state, before the Win32 hook executes. -/
def spike2AfterWriteFileCall (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (call_rip 0x1edd) state

/-- One `WriteFile` boundary is the actual linked import call and its concrete `ConsoleEvent.out`
hook. The formatter supplies IAT preservation and raw-call safety, never an arbitrary event or
interceptor result. -/
theorem spike2_writeFile_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713517)
    (iatTarget : (spike2AfterWriteFileCall state).rip = 0x140003010)
    (iatIndex : Gasm.Targets.Windows.findIatIndex (spike2AfterWriteFileCall state)
      (spike2AfterWriteFileCall state).rip = some 2)
    (steppedSafe : (spike2AfterWriteFileCall state).fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1
      (accumulateEvent eventsRev (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).2)
      (emittedBy (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).2) := by
  have hnotLinux : (spike2AfterWriteFileCall state).rip ≠ linuxSyscallEntry := by
    rw [iatTarget]
    decide
  have hselected : selectedNonInputPlatformCall (spike2AfterWriteFileCall state).rip
      (spike2AfterWriteFileCall state) = true := by
    simp [selectedNonInputPlatformCall, selectedNonInputWin32Call, iatIndex]
  have hintercept : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterWriteFileCall state).rip (spike2AfterWriteFileCall state) =
      some (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)) := by
    change Gasm.Targets.Windows.win32Intercept (Event := AnyEvent)
      (spike2AfterWriteFileCall state).rip (spike2AfterWriteFileCall state) = some _
    simp [Gasm.Targets.Windows.win32Intercept, iatIndex]
  have hsafe : (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1.fault = none := by
    unfold writeFileHook
    change (spike2AfterWriteFileCall state).fault = none
    exact steppedSafe
  have h : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed (0 + 1)
      state eventsRev (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1
      (accumulateEvent eventsRev (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).2)
      (emittedBy (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).2 ++ []) :=
    ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
      (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed) (.callRip 0x1edd)
      (by simpa [hrip] using spike2WriteFile_fetch) hselected hintercept hsafe (.nil _ _)
  simpa using h


end Spikes.Spike2Fibonacci.Windows

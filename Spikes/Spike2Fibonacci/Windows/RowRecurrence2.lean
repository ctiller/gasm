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
import Gasm.Targets.Dispatcher
import Spikes.Spike2Fibonacci.Windows.NativeAdapter

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRecurrence2 :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- The second concrete recurrence transition after the WriteFile hook. -/
def spike2AfterRecurrenceAdd (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (add_r64 .r8 .r15) state

private theorem sequentialRecurrenceAdd : SequentialInstruction (add_r64 .r8 .r15) where
  encoding := .add .r8 .r15
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

/-- Exact selected certificate for only `add r8, r15`. -/
theorem spike2_recurrence_add_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713526) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (spike2AfterRecurrenceAdd state) eventsRev [] := by
  have hnext : (spike2AfterRecurrenceAdd state).rip = 5368713529 := by
    unfold spike2AfterRecurrenceAdd
    rw [show (X86_64Instruction.step (add_r64 .r8 .r15) state).rip =
      state.rip + (X86_64Instruction.encode (add_r64 .r8 .r15)).size.toUInt64 from
      (sequentialRecurrenceAdd.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  have hboundary := selected_silent_unaligned (spike2AfterRecurrenceAdd state) 5368713529
    hnext (by decide) (by decide)
  have hselected : selectedNonInputPlatformCall
      (X86_64Instruction.step (add_r64 .r8 .r15) state).rip
      (X86_64Instruction.step (add_r64 .r8 .r15) state) = true := by
    change selectedNonInputPlatformCall (spike2AfterRecurrenceAdd state).rip
      (spike2AfterRecurrenceAdd state) = true
    rw [hnext]
    exact hboundary.1
  have hsilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (add_r64 .r8 .r15) state).rip
      (X86_64Instruction.step (add_r64 .r8 .r15) state) = none := by
    change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterRecurrenceAdd state).rip (spike2AfterRecurrenceAdd state) = none
    rw [hnext]
    exact hboundary.2
  refine ProductionPrefix.SelectedPrefix.ordinary sequentialRecurrenceAdd
    (by simpa [hrip] using spike2Recurrence_add_fetch) hselected hsilent ?_ (.nil _ _)
  change state.fault = none
  exact hsafe

/-- Minimal recurrence observation exported to the next body producer. -/
theorem spike2_recurrence_add_effect (state : X86_64MachineState) :
    (spike2AfterRecurrenceAdd state).gprs .r8 = state.gprs .r8 + state.gprs .r15 ∧
    (spike2AfterRecurrenceAdd state).gprs .r14 = state.gprs .r14 ∧
    (spike2AfterRecurrenceAdd state).gprs .r15 = state.gprs .r15 := by
  exact ⟨rfl, rfl, rfl⟩

theorem spike2_recurrence_add_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713526) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceAdd state).rip = 5368713529 ∧
    (spike2AfterRecurrenceAdd state).fault = none := by
  constructor
  · unfold spike2AfterRecurrenceAdd
    rw [show (X86_64Instruction.step (add_r64 .r8 .r15) state).rip =
      state.rip + (X86_64Instruction.encode (add_r64 .r8 .r15)).size.toUInt64 from
      (sequentialRecurrenceAdd.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  · change state.fault = none
    exact hsafe

end Spikes.Spike2Fibonacci.Windows

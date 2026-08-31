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

local instance (priority := 1100) spike2WindowsRuntimeForRowRecurrence3 :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- The `mov r14, r15` transition of the recurrence. -/
def spike2AfterRecurrenceMove14 (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_r64 .r14 .r15) state

private theorem sequentialRecurrenceMove14 : SequentialInstruction (mov_r64 .r14 .r15) where
  encoding := .mov .r14 .r15
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

theorem spike2_recurrence_move14_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713529) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1 state eventsRev
      (spike2AfterRecurrenceMove14 state) eventsRev [] := by
  have hnext : (spike2AfterRecurrenceMove14 state).rip = 5368713532 := by
    unfold spike2AfterRecurrenceMove14
    rw [show (X86_64Instruction.step (mov_r64 .r14 .r15) state).rip =
      state.rip + (X86_64Instruction.encode (mov_r64 .r14 .r15)).size.toUInt64 from
      (sequentialRecurrenceMove14.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  have hboundary := selected_silent_unaligned (spike2AfterRecurrenceMove14 state) 5368713532
    hnext (by decide) (by decide)
  have hselected : selectedNonInputPlatformCall
      (X86_64Instruction.step (mov_r64 .r14 .r15) state).rip
      (X86_64Instruction.step (mov_r64 .r14 .r15) state) = true := by
    change selectedNonInputPlatformCall (spike2AfterRecurrenceMove14 state).rip
      (spike2AfterRecurrenceMove14 state) = true
    rw [hnext]
    exact hboundary.1
  have hsilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (X86_64Instruction.step (mov_r64 .r14 .r15) state).rip
      (X86_64Instruction.step (mov_r64 .r14 .r15) state) = none := by
    change @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterRecurrenceMove14 state).rip (spike2AfterRecurrenceMove14 state) = none
    rw [hnext]
    exact hboundary.2
  refine ProductionPrefix.SelectedPrefix.ordinary sequentialRecurrenceMove14
    (by simpa [hrip] using spike2Recurrence_mov14_fetch) hselected hsilent ?_ (.nil _ _)
  change state.fault = none
  exact hsafe

theorem spike2_recurrence_move14_effect (state : X86_64MachineState) :
    (spike2AfterRecurrenceMove14 state).gprs .r14 = state.gprs .r15 ∧
    (spike2AfterRecurrenceMove14 state).gprs .r15 = state.gprs .r15 := by
  exact ⟨rfl, rfl⟩

theorem spike2_recurrence_move14_boundary (state : X86_64MachineState)
    (hrip : state.rip = 5368713529) (hsafe : state.fault = none) :
    (spike2AfterRecurrenceMove14 state).rip = 5368713532 ∧
    (spike2AfterRecurrenceMove14 state).fault = none := by
  constructor
  · unfold spike2AfterRecurrenceMove14
    rw [show (X86_64Instruction.step (mov_r64 .r14 .r15) state).rip =
      state.rip + (X86_64Instruction.encode (mov_r64 .r14 .r15)).size.toUInt64 from
      (sequentialRecurrenceMove14.step_rip_eq_of_safe state hsafe), hrip]
    rfl
  · change state.fault = none
    exact hsafe

end Spikes.Spike2Fibonacci.Windows

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
-/import Spikes.Spike2Fibonacci.Windows.RowExitFacts

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowExit :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

/-- Typed terminal edge after the structurally completed 90-row driver. -/
def spike2_exit_tail : SelectedProcessExitTail selectedNonInputPlatformCall spike2Indexed
    (Spike2RowInvariant 90) where
  maxFuel := 3
  run state eventsRev holds := by
    have counter : state.gprs .r13 = UInt64.ofNat 91 := by
      simpa using holds.counter
    have exits := spike2_main_counter_exits state counter
    have headerRip := spike2_main_header_taken_rip state holds.rip exits
    have headerLow : Spike2RowLowMemory (spike2AfterMainHeader state) :=
      holds.lowMemory.of_memory_eq (spike2_main_header_memory state)
    have headerNotSelfRef :
        (spike2AfterMainHeader state).read64 5368713544 ≠ 5368713544 := by
      rw [headerLow 5368713544 (by decide)]
      exact spike2_initial_text_3544_not_selfref
    have headerBoundary := spike2_selected_silent_nonIat (spike2AfterMainHeader state)
      5368713544 headerRip (by decide) headerNotSelfRef
    have headerSelected : selectedNonInputPlatformCall (spike2AfterMainHeader state).rip
        (spike2AfterMainHeader state) = true := by
      rw [headerRip]
      exact headerBoundary.1
    have headerSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
        (spike2AfterMainHeader state).rip (spike2AfterMainHeader state) = none := by
      rw [headerRip]
      exact headerBoundary.2
    have headerPrefix := spike2_main_header_taken_selected_prefix state eventsRev holds.rip exits
      headerSelected headerSilent holds.fault
    have beforeRip := spike2_before_exit_process_rip state headerRip
    have beforeBoundary := spike2_selected_silent_unaligned (spike2BeforeExitProcess state)
      5368713546 beforeRip (by decide) (by decide)
    have beforeSelected : selectedNonInputPlatformCall (spike2BeforeExitProcess state).rip
        (spike2BeforeExitProcess state) = true := by
      rw [beforeRip]
      exact beforeBoundary.1
    have beforeSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
        (spike2BeforeExitProcess state).rip (spike2BeforeExitProcess state) = none := by
      rw [beforeRip]
      exact beforeBoundary.2
    have setupPrefix := spike2_exit_setup_selected_prefix state eventsRev headerRip
      beforeSelected beforeSilent holds.fault
    have beforeLow : Spike2RowLowMemory (spike2BeforeExitProcess state) :=
      headerLow.of_memory_eq (spike2_before_exit_process_memory state)
    have beforeRsp : (spike2BeforeExitProcess state).rsp = spike2AfterPrologue.rsp :=
      (spike2_before_exit_process_rsp state).trans holds.rsp
    have beforeSafe : (spike2BeforeExitProcess state).fault = none :=
      (spike2_before_exit_process_fault state).trans holds.fault
    have exitIat : (spike2BeforeExitProcess state).read64 5368721432 = 5368721432 := by
      rw [beforeLow 5368721432 (by decide)]
      exact spike2_after_prologue_exitProcessIat
    have callTarget := spike2_exit_process_call_target (spike2BeforeExitProcess state)
      beforeRip exitIat
    have calledLow := spike2_exit_process_call_lowMemory (spike2BeforeExitProcess state)
      beforeLow beforeRsp
    have calledSelfRef :
        (spike2AfterExitProcessCall (spike2BeforeExitProcess state)).read64 5368721432 =
          5368721432 := by
      rw [calledLow 5368721432 (by decide)]
      exact spike2_after_prologue_exitProcessIat
    have iatIndex := spike2_exit_process_iat_index
      (spike2AfterExitProcessCall (spike2BeforeExitProcess state)) callTarget calledSelfRef
    have callSafe := spike2_exit_process_call_safe (spike2BeforeExitProcess state) beforeSafe
    have exitStep := spike2_exit_process_selected_step (spike2BeforeExitProcess state)
      beforeRip callTarget iatIndex (spike2_before_exit_process_code_zero state) callSafe
    exact ⟨{
      fuel := 3
      final := spike2BeforeExitProcess state
      finalEventsRev := eventsRev
      emitted := []
      code := 0
      certificate := by simpa using headerPrefix.append setupPrefix
      exitStep := exitStep }, by exact Nat.le_refl 3⟩

/-- The typed exit tail contributes exactly the public process-exit event.  Consumers need not
    unfold the Win32 import realization or its concrete placement to identify the event. -/
theorem spike2_exit_tail_event (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (holds : Spike2RowInvariant 90 state eventsRev) :
    let result := (spike2_exit_tail.run state eventsRev holds).val
    result.exitStep.event = some (Inject.inject (ProcessEvent.exit 0)) := by
  have hzero :
      (spike2AfterExitProcessCall (spike2BeforeExitProcess state)).gprs .rcx = 0 := by
    change ((spike2BeforeExitProcess state).push64
      ((spike2BeforeExitProcess state).rip + 6)).gprs .rcx = 0
    simpa [X86_64MachineState.push64, X86_64MachineState.setGpr64] using
      spike2_before_exit_process_code_zero state
  simp [spike2_exit_tail, spike2_exit_process_selected_step,
    Gasm.Targets.Windows.exitProcessHook, hzero]

/-- The exit tail itself is silent and selects exit code zero. -/
theorem spike2_exit_tail_summary (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (holds : Spike2RowInvariant 90 state eventsRev) :
    let result := (spike2_exit_tail.run state eventsRev holds).val
    result.finalEventsRev = eventsRev ∧ result.code = 0 := by
  simp [spike2_exit_tail]

end Spikes.Spike2Fibonacci.Windows

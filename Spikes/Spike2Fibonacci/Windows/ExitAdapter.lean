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

import Spikes.Spike2Fibonacci.Windows.NativeAdapter
import Gasm.Targets.Dispatcher

/-!
# Typed Windows Spike 2 exit boundary

This module deliberately exposes only the narrow terminal boundary: the linked `cmp`/`jge`
edge, the `xor ecx, ecx` setup, and the actual `ExitProcess` import transition.  A row producer
need only supply its final RIP, counter condition, fault freedom, and IAT facts; it never needs
to unfold the production outcome runner or retain a full predecessor machine state.
-/

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- Exact two-instruction terminal header in the linked Windows image. -/
def spike2AfterMainHeader (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jge_rel32 267)
    (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state)

/-- State immediately before the linked `ExitProcess` import call. -/
def spike2BeforeExitProcess (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx) (spike2AfterMainHeader state)

private theorem sequentialCmpCounter : SequentialInstruction (cmp_r64_imm8 .r13 91) where
  encoding := .compareImm8 .r13 91
  safeFallthrough := by intro _ _; rfl

private theorem sequentialXorExitCode : SequentialInstruction (xor_r32 .ecx .ecx) where
  encoding := .xor32 .ecx .ecx
  safeFallthrough := by intro _ _; rfl

private theorem stepCmpImm8 (dst : Reg64) (imm : UInt8) (state : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm8 dst imm) state =
      { state.setFlagsCmp64 (state.gprs dst) (signExtend8To64 imm) with rip := state.rip + 4 } := rfl

private theorem stepJge32 (disp : Int32) (state : X86_64MachineState) :
    X86_64Instruction.step (jge_rel32 disp) state =
      { state with rip := if state.sf == state.of_ then
          state.rip + 6 + signExtend32To64 disp else state.rip + 6 } := rfl

/-- The terminal main-header branch takes the linked `jge` edge.  Selection and silence at the
landing point are explicit inputs, so this producer exports no expanded predecessor state. -/
theorem spike2_main_header_taken_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : state.rip = spike2WindowsMainLoopRip)
    (exits : X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state))
    (exitSelected : selectedNonInputPlatformCall (spike2AfterMainHeader state).rip
      (spike2AfterMainHeader state) = true)
    (exitSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterMainHeader state).rip (spike2AfterMainHeader state) = none)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterMainHeader state) eventsRev [] := by
  change ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed (1 + 1) state
    eventsRev (spike2AfterMainHeader state) eventsRev []
  have hcmpRip : (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip = 5368713271 := by
    rw [stepCmpImm8, hrip, spike2WindowsMainLoopRip_eq]
    rfl
  refine ProductionPrefix.SelectedPrefix.ordinary
    (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
    sequentialCmpCounter ?_ ?_ ?_ ?_ ?_
  · rw [hrip]
    exact spike2MainLoop_fetch
  · simp [selectedNonInputPlatformCall, selectedNonInputWin32Call,
      Gasm.Targets.Windows.findIatIndex, hcmpRip, linuxSyscallEntry]
  · change (if (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip ==
        linuxSyscallEntry then linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = none
    rw [hcmpRip]
    simp [linuxSyscallEntry, Gasm.Targets.Windows.win32Intercept,
      Gasm.Targets.Windows.findIatIndex]
  · rw [stepCmpImm8]
    exact hsafe
  · refine ProductionPrefix.SelectedPrefix.conditionalTaken
      (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
      (.jge32 267) exits ?_ exitSelected exitSilent ?_ (.nil _ _)
    · rw [hcmpRip]
      rfl
    · change state.fault = none
      exact hsafe

/-- The terminal setup is the real linked `xor ecx, ecx`; the following import is kept separate
so the final transition is certified by `SelectedProcessExitStep`. -/
theorem spike2_exit_setup_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent)
    (hrip : (spike2AfterMainHeader state).rip = 5368713544)
    (selectedAt : selectedNonInputPlatformCall (spike2BeforeExitProcess state).rip
      (spike2BeforeExitProcess state) = true)
    (silent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2BeforeExitProcess state).rip (spike2BeforeExitProcess state) = none)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      (spike2AfterMainHeader state) eventsRev (spike2BeforeExitProcess state) eventsRev [] := by
  refine ProductionPrefix.SelectedPrefix.ordinary
    (Event := AnyEvent) (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed)
    sequentialXorExitCode ?_ selectedAt silent ?_ (.nil _ _)
  · rw [hrip]
    rfl
  · change state.fault = none
    exact hsafe

def spike2AfterExitProcessCall (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (call_rip 0x1ec8) state

/-- Package the real linked `ExitProcess` import call.  Its IAT target/index and raw-call safety
remain as small, concrete obligations for the row/exit consumer. -/
def spike2_exit_process_selected_step (state : X86_64MachineState)
    (hrip : state.rip = 5368713546)
    (iatTarget : (spike2AfterExitProcessCall state).rip = 0x140003018)
    (iatIndex : Gasm.Targets.Windows.findIatIndex (spike2AfterExitProcessCall state)
      (spike2AfterExitProcessCall state).rip = some 3)
    (exitCodeZero : state.gprs .rcx = 0)
    (steppedSafe : (spike2AfterExitProcessCall state).fault = none) :
    ProductionPrefix.SelectedPrefix.SelectedProcessExitStep (Event := AnyEvent)
      selectedNonInputPlatformCall spike2Indexed state 0 where
  instruction := call_rip 0x1ec8
  hooked := (exitProcessHook (Event := AnyEvent) (spike2AfterExitProcessCall state)).1
  event := (exitProcessHook (Event := AnyEvent) (spike2AfterExitProcessCall state)).2
  encoding := .callRip 0x1ec8
  lookup := by rw [hrip]; rfl
  selectedAt := by
    change selectedNonInputPlatformCall (spike2AfterExitProcessCall state).rip
      (spike2AfterExitProcessCall state) = true
    have hnotLinux : (spike2AfterExitProcessCall state).rip ≠ linuxSyscallEntry := by
      rw [iatTarget]
      decide
    simp [selectedNonInputPlatformCall, hnotLinux, selectedNonInputWin32Call, iatIndex]
  steppedSafe := steppedSafe
  intercept := by
    change (if (spike2AfterExitProcessCall state).rip == linuxSyscallEntry then
      linuxSyscallIntercept _ _ else Gasm.Targets.Windows.win32Intercept _ _) = some _
    have hnotLinux : (spike2AfterExitProcessCall state).rip ≠ linuxSyscallEntry := by
      rw [iatTarget]
      decide
    have hnotLinuxBool : ((spike2AfterExitProcessCall state).rip == linuxSyscallEntry) = false :=
      decide_eq_false_iff_not.mpr hnotLinux
    rw [hnotLinuxBool]
    change Gasm.Targets.Windows.win32Intercept (spike2AfterExitProcessCall state).rip
      (spike2AfterExitProcessCall state) = some _
    simp only [Gasm.Targets.Windows.win32Intercept, iatIndex]
  exits := by
    have hzero : (spike2AfterExitProcessCall state).gprs .rcx = 0 := by
      change (state.push64 (state.rip + 6)).gprs .rcx = 0
      simp [X86_64MachineState.push64, X86_64MachineState.setGpr64, exitCodeZero]
    simp [exitProcessHook, hzero]

end Spikes.Spike2Fibonacci.Windows

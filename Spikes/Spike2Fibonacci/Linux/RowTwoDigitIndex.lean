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

import Spikes.Spike2Fibonacci.Linux.RowLoopInvariant

/-!
# Parametric two-digit row-index opening

Rows 10 through 90 take the real linked two-digit index branch.  This producer starts from an
arbitrary predecessor and ends at a state function of that predecessor; it consumes only local
instruction, selector, interceptor, and safety projections.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

namespace RowTwoDigitIndex

open Row8Parametric

def twoDigitIndexCode : List X86_64Instr := [
  mov_r64 .rax .r13,
  mov_r64_imm64 .r10 10,
  xor_r32 .edx .edx,
  div_r64 .r10,
  add_r64_imm8 .rax 0x30,
  add_r64_imm8 .rdx 0x30,
  lea_rsp .rdi 0x44,
  mov_mem8 .rdi .rax,
  lea_rsp .rdi 0x45,
  mov_mem8 .rdi .rdx,
  mov_rsp_byte 0x46 0x29,
  mov_rsp_byte 0x47 0x20,
  mov_rsp_byte 0x48 0x3d,
  mov_rsp_byte 0x49 0x20,
  lea_rsp .rdi 0x4a
]

def afterTwoDigitIndex (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps twoDigitIndexCode (afterIndexHeader predecessor)

def afterTwoDigitValueSetup (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps valueSetupCode (afterTwoDigitIndex predecessor)

structure TwoDigitOpeningRestFrame (predecessor : X86_64MachineState) : Prop where
  index : SequentialBlockFrame twoDigitIndexCode (afterIndexHeader predecessor)
  valueSetup : SequentialBlockFrame valueSetupCode (afterTwoDigitIndex predecessor)

private theorem ordinarySelected (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    selectedNonInputPlatformCall state.rip state = true := by
  simp [selectedNonInputPlatformCall, ordinary.notLinuxEntry,
    Gasm.Targets.Windows.selectedNonInputWin32Call,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem ordinarySilent (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    ExternalCallInterceptor.interceptCall X86_64 (Event := AnyEvent) state.rip state = none := by
  change (if state.rip == linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = none
  simp [ordinary.notLinuxEntry, Gasm.Targets.Windows.win32Intercept,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem indexHeaderTakenPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (twoDigit : 10 ≤ completed + 1)
    (frame : OpeningFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      (body predecessor) eventsRev (afterIndexHeader predecessor) eventsRev [] := by
  have hbody : (body predecessor).rip = 4198447 :=
    spike2_after_main_header_body_rip completed predecessor entry.completed_lt entry.rip
      entry.counter
  have hf : (afterF predecessor).rip = 4198452 := by
    rw [afterF, show (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
      (body predecessor)).rip = (body predecessor).rip + 5 by rfl, hbody]
    decide
  have hi : (afterI predecessor).rip = 4198457 := by
    rw [afterI, show (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
      (afterF predecessor)).rip = (afterF predecessor).rip + 5 by rfl, hf]
    decide
  have hb : (afterB predecessor).rip = 4198462 := by
    rw [afterB, show (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (afterI predecessor)).rip = (afterI predecessor).rip + 5 by rfl, hi]
    decide
  have hopen : (afterOpen predecessor).rip = 4198467 := by
    rw [afterOpen, show (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
      (afterB predecessor)).rip = (afterB predecessor).rip + 5 by rfl, hb]
    decide
  have hcmp : (afterIndexCmp predecessor).rip = 4198471 := by
    rw [afterIndexCmp, show (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (afterOpen predecessor)).rip = (afterOpen predecessor).rip + 4 by rfl, hopen]
    decide
  have hcounter : (afterOpen predecessor).gprs .r13 = (completed + 1).toUInt64 := by
    change predecessor.gprs .r13 = (completed + 1).toUInt64
    exact entry.counter
  have htaken : X86BranchCondition.greaterEqual.holds (afterIndexCmp predecessor) :=
    spike2_index_two_digits (afterOpen predecessor) (completed + 1) twoDigit
      (by have := entry.completed_lt; omega) hcounter
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x40 0x46
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · rw [hbody]
    rfl
  · exact ordinarySelected _ frame.afterF
  · exact ordinarySilent _ frame.afterF
  · change predecessor.fault = none
    exact entry.safe
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x41 0x69
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · change instructionAtRipIndexed spike2Indexed (afterF predecessor).rip = _
      rw [hf]
      rfl
    · exact ordinarySelected _ frame.afterI
    · exact ordinarySilent _ frame.afterI
    · change predecessor.fault = none
      exact entry.safe
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .movRspByte 0x42 0x62
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · change instructionAtRipIndexed spike2Indexed (afterI predecessor).rip = _
        rw [hi]
        rfl
      · exact ordinarySelected _ frame.afterB
      · exact ordinarySilent _ frame.afterB
      · change predecessor.fault = none
        exact entry.safe
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .movRspByte 0x43 0x28
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · change instructionAtRipIndexed spike2Indexed (afterB predecessor).rip = _
          rw [hb]
          rfl
        · exact ordinarySelected _ frame.afterOpen
        · exact ordinarySilent _ frame.afterOpen
        · change predecessor.fault = none
          exact entry.safe
        · refine ProductionPrefix.SelectedPrefix.ordinary
            (Spikes.Spike2Fibonacci.Linux.Row8BoundaryData.spike2Row8SequentialCmp .r13 10)
            ?_ ?_ ?_ ?_ ?_
          · change instructionAtRipIndexed spike2Indexed (afterOpen predecessor).rip = _
            rw [hopen]
            rfl
          · exact ordinarySelected _ frame.afterIndexCmp
          · exact ordinarySilent _ frame.afterIndexCmp
          · change predecessor.fault = none
            exact entry.safe
          · refine ProductionPrefix.SelectedPrefix.conditionalTaken (.jge8 41) htaken
              ?_ ?_ ?_ ?_ ?_
            · change instructionAtRipIndexed spike2Indexed (afterIndexCmp predecessor).rip = _
              rw [hcmp]
              rfl
            · exact ordinarySelected _ frame.afterIndexHeader
            · exact ordinarySilent _ frame.afterIndexHeader
            · change predecessor.fault = none
              exact entry.safe
            · exact .nil _ _

theorem openingPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (twoDigit : 10 ≤ completed + 1)
    (frame : OpeningFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 8
      predecessor eventsRev (afterIndexHeader predecessor) eventsRev [] := by
  exact (spike2_row_header_from_entry (eventsRev := eventsRev) entry).append
    (indexHeaderTakenPrefix entry twoDigit frame)

theorem openingRestPrefix {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : TwoDigitOpeningRestFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 18
      (afterIndexHeader predecessor) eventsRev
      (afterTwoDigitValueSetup predecessor) eventsRev [] := by
  have index := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall twoDigitIndexCode spike2Indexed
    (afterIndexHeader predecessor) frame.index eventsRev
  have setup := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall valueSetupCode spike2Indexed
    (afterTwoDigitIndex predecessor) frame.valueSetup eventsRev
  simpa [twoDigitIndexCode, valueSetupCode, afterTwoDigitIndex,
    afterTwoDigitValueSetup] using index.append setup

/-- Row 10 reaches the real decimal formatter entry through the same symbolic predecessor
discipline used for Row 9, now taking the linked two-digit index edge. -/
theorem row10_opening_reuse {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry 9 55 89 predecessor)
    (openingFrame : OpeningFrame predecessor)
    (restFrame : TwoDigitOpeningRestFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 26
      predecessor eventsRev (afterTwoDigitValueSetup predecessor) eventsRev [] := by
  have opening := openingPrefix (eventsRev := eventsRev) entry (by omega) openingFrame
  exact opening.append (openingRestPrefix (eventsRev := eventsRev) restFrame)

end RowTwoDigitIndex

end Spikes.Spike2Fibonacci.Linux

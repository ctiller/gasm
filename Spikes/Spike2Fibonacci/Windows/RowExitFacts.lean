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
-/import Spikes.Spike2Fibonacci.Windows.RowPass
import Spikes.Spike2Fibonacci.Windows.FormatterLocal

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

private theorem stepCmpImm8 (dst : Reg64) (imm : UInt8) (state : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm8 dst imm) state =
      { state.setFlagsCmp64 (state.gprs dst) (signExtend8To64 imm) with
        rip := state.rip + 4 } := rfl

private theorem stepJge32 (disp : Int32) (state : X86_64MachineState) :
    X86_64Instruction.step (jge_rel32 disp) state =
      { state with rip := if state.sf == state.of_ then
          state.rip + 6 + signExtend32To64 disp else state.rip + 6 } := rfl

/-- The taken terminal header reaches the linked ExitProcess setup. -/
theorem spike2_main_header_taken_rip (state : X86_64MachineState)
    (hrip : state.rip = spike2WindowsMainLoopRip)
    (exits : X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state)) :
    (spike2AfterMainHeader state).rip = 5368713544 := by
  have hcmpRip : (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip =
      5368713271 := by
    rw [stepCmpImm8, hrip, spike2WindowsMainLoopRip_eq]
    rfl
  unfold spike2AfterMainHeader
  rw [stepJge32]
  simp only [X86BranchCondition.holds] at exits
  rw [if_pos (by simpa using exits), hcmpRip]
  rfl

theorem spike2_main_header_memory (state : X86_64MachineState) :
    (spike2AfterMainHeader state).memory = state.memory := by
  rfl

theorem spike2_main_header_rsp (state : X86_64MachineState) :
    (spike2AfterMainHeader state).rsp = state.rsp := by
  rfl

theorem spike2_main_header_fault (state : X86_64MachineState) :
    (spike2AfterMainHeader state).fault = state.fault := by
  rfl

/-- The exit-code XOR falls through to the real linked import call. -/
theorem spike2_before_exit_process_rip (state : X86_64MachineState)
    (headerRip : (spike2AfterMainHeader state).rip = 5368713544) :
    (spike2BeforeExitProcess state).rip = 5368713546 := by
  unfold spike2BeforeExitProcess
  change (spike2AfterMainHeader state).rip + 2 = 5368713546
  rw [headerRip]
  rfl

theorem spike2_before_exit_process_memory (state : X86_64MachineState) :
    (spike2BeforeExitProcess state).memory = (spike2AfterMainHeader state).memory := by
  rfl

theorem spike2_before_exit_process_rsp (state : X86_64MachineState) :
    (spike2BeforeExitProcess state).rsp = state.rsp := by
  rfl

theorem spike2_before_exit_process_fault (state : X86_64MachineState) :
    (spike2BeforeExitProcess state).fault = state.fault := by
  rfl

theorem spike2_before_exit_process_code_zero (state : X86_64MachineState) :
    (spike2BeforeExitProcess state).gprs .rcx = 0 := by
  unfold spike2BeforeExitProcess
  simp [step_xor_r32, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64]

/-- The ExitProcess CALL only pushes its return address. -/
theorem spike2_after_exit_process_call_memory (state : X86_64MachineState) :
    (spike2AfterExitProcessCall state).memory =
      (state.write64 (state.rsp - 8) (state.rip + 6)).memory := by
  rfl

theorem spike2_exit_process_call_target (state : X86_64MachineState)
    (hrip : state.rip = 5368713546)
    (iat : state.read64 5368721432 = 5368721432) :
    (spike2AfterExitProcessCall state).rip = 5368721432 := by
  unfold spike2AfterExitProcessCall
  change state.read64 (state.rip + 6 + signExtend32To64 0x1ec8) = 5368721432
  rw [hrip]
  rw [show (5368713546 : UInt64) + 6 + signExtend32To64 0x1ec8 = 5368721432 by decide]
  exact iat

theorem spike2_exit_process_call_safe (state : X86_64MachineState)
    (safe : state.fault = none) :
    (spike2AfterExitProcessCall state).fault = none := by
  change state.fault = none
  exact safe

theorem spike2_exit_process_call_lowMemory (state : X86_64MachineState)
    (low : Spike2RowLowMemory state) (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterExitProcessCall state) := by
  have rspConcrete : state.rsp = 140737488289664 := rsp.trans spike2_after_prologue_rsp_eq
  have pushed := low.write64 (state.rsp - 8) (state.rip + 6)
    (by rw [rspConcrete]; decide) (by rw [rspConcrete]; decide)
  exact pushed.of_memory_eq (spike2_after_exit_process_call_memory state)

theorem spike2_exit_process_iat_index (state : X86_64MachineState)
    (target : state.rip = 5368721432)
    (selfref : state.read64 5368721432 = 5368721432) :
    Gasm.Targets.Windows.findIatIndex state state.rip = some 3 := by
  rw [target]
  simp [Gasm.Targets.Windows.findIatIndex, selfref]
  decide

end Spikes.Spike2Fibonacci.Windows

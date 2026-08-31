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
-/import Spikes.Spike2Fibonacci.Windows.RowInvariant

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowOpening :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

structure Spike2OpeningResult (initial : X86_64MachineState) (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  rip : final.rip = 5368713297
  rsp : final.rsp = spike2AfterPrologue.rsp
  fault : final.fault = none
  lowMemory : Spike2RowLowMemory final
  buffer : BufHolds final.memory (initial.rsp + 64) [0x46, 0x69, 0x62, 0x28]

private theorem main_fallthrough_rip (state : X86_64MachineState)
    (hrip : state.rip = spike2WindowsMainLoopRip)
    (continues : ¬ X86BranchCondition.greaterEqual.holds
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state)) :
    (spike2AfterMainHeader state).rip = 5368713277 := by
  simp only [X86BranchCondition.holds] at continues
  have hcond : ((X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).sf ==
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).of_) = false :=
    decide_eq_false_iff_not.mpr continues
  unfold spike2AfterMainHeader
  rw [show X86_64Instruction.step (jge_rel32 267)
      (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state) =
    { X86_64Instruction.step (cmp_r64_imm8 .r13 91) state with
      rip := if (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).sf ==
        (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).of_ then
        (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip + 6 +
          signExtend32To64 267
        else (X86_64Instruction.step (cmp_r64_imm8 .r13 91) state).rip + 6 } by rfl]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]
  change state.rip + 4 + 6 = 5368713277
  rw [hrip, spike2WindowsMainLoopRip_eq]
  rfl

opaque spike2_row_opening (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (within : completed < 90)
    (holds : Spike2RowInvariant completed state eventsRev) :
    Spike2OpeningResult state eventsRev := by
  let main := spike2AfterMainHeader state
  let literal := spike2AfterFibLiteral main
  have continues := spike2_main_counter_continues state completed within holds.counter
  have mainPrefix := spike2_main_header_fallthrough_selected_prefix state eventsRev holds.rip
    continues holds.fault
  have mainRip : main.rip = 5368713277 := main_fallthrough_rip state holds.rip continues
  have mainFrame := spike2_main_header_registerFrame state
  have mainRsp : main.rsp = spike2AfterPrologue.rsp := mainFrame.rsp.trans holds.rsp
  have mainSafe : main.fault = none := mainFrame.fault.trans holds.fault
  have mainLow : Spike2RowLowMemory main := holds.lowMemory.of_memory_eq (by rfl)
  have literalPrefix := spike2_fib_literal_selected_prefix main eventsRev mainRip mainSafe
  have literalFrame := spike2_fib_literal_registerFrame main
  have literalRsp : literal.rsp = spike2AfterPrologue.rsp := literalFrame.rsp.trans mainRsp
  exact {
    final := literal
    certificate := mainPrefix.append literalPrefix
    registers := mainFrame.trans literalFrame
    fibRegisters := by constructor <;> rfl
    rip := by
      change main.rip + 5 + 5 + 5 + 5 = 5368713297
      rw [mainRip]
      rfl
    rsp := literalRsp
    fault := literalFrame.fault.trans mainSafe
    lowMemory := spike2_fib_literal_lowMemory main mainLow mainRsp
    buffer := by
      have literalBuffer := spike2_fib_literal_buffer main
      rw [mainFrame.rsp] at literalBuffer
      change BufHolds (spike2AfterFibLiteral main).memory (state.rsp + 64) _
      exact literalBuffer }

end Spikes.Spike2Fibonacci.Windows

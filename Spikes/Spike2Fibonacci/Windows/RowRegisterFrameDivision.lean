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
-/import Spikes.Spike2Fibonacci.Windows.RowRegisterFrameBase

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRegisterFrameDivision :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

theorem spike2_two_digit_division_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitDivision state) := by
  let s1 := X86_64Instruction.step (mov_r64 .rax .r13) state
  let s2 := X86_64Instruction.step (mov_r64_imm64 .r10 10) s1
  let s3 := X86_64Instruction.step (xor_r32 .edx .edx) s2
  have zeroHigh : s3.gprs .rdx = 0 := by
    dsimp [s3]
    simp [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64]
  have divisor2 : s2.gprs .r10 = 10 := by dsimp [s2]; rfl
  have divisor : s3.gprs .r10 = 10 := by
    dsimp [s3]
    simpa [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64] using divisor2
  unfold spike2AfterTwoDigitDivision
  rw [step_div_r64_by10 s3 zeroHigh divisor]
  constructor <;> rfl

theorem spike2_two_digit_division_fibRegisterFrame (state : X86_64MachineState) :
    Spike2FibRegisterFrame state (spike2AfterTwoDigitDivision state) := by
  let s1 := X86_64Instruction.step (mov_r64 .rax .r13) state
  let s2 := X86_64Instruction.step (mov_r64_imm64 .r10 10) s1
  let s3 := X86_64Instruction.step (xor_r32 .edx .edx) s2
  have zeroHigh : s3.gprs .rdx = 0 := by
    dsimp [s3]
    simp [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64]
  have divisor2 : s2.gprs .r10 = 10 := by dsimp [s2]; rfl
  have divisor : s3.gprs .r10 = 10 := by
    dsimp [s3]
    simpa [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64] using divisor2
  unfold spike2AfterTwoDigitDivision
  rw [step_div_r64_by10 s3 zeroHigh divisor]
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows

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
import Spikes.Spike2Fibonacci.Windows.RowFormatter

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowDivisionFacts :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Stdlib.Fmt

/-- Numbers in the formatter's two-digit range have exactly the quotient and remainder digits. -/
theorem formatDecimal_two_digits (n : Nat) (lower : 10 ≤ n) (upper : n < 100) :
    formatDecimal n = [byteOfDigit (n / 10), byteOfDigit (n % 10)] := by
  unfold formatDecimal
  rw [show digits n = digits (n / 10) ++ [n % 10] by
    rw [digits]
    simp [show ¬ n < 10 by omega]]
  rw [digits_single _ (by omega)]
  rfl

private theorem division_step (state : X86_64MachineState) :
    let s1 := X86_64Instruction.step (mov_r64 .rax .r13) state
    let s2 := X86_64Instruction.step (mov_r64_imm64 .r10 10) s1
    let s3 := X86_64Instruction.step (xor_r32 .edx .edx) s2
    X86_64Instruction.step (div_r64 .r10) s3 =
      { (s3.setGpr64 .rax (((s3.gprs .rax).toNat / 10 : Nat)).toUInt64
          |>.setGpr64 .rdx (((s3.gprs .rax).toNat % 10 : Nat)).toUInt64) with
        rip := s3.rip + 3 } := by
  dsimp only
  apply step_div_r64_by10
  · simp [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64]
  · have setTen :
        (X86_64Instruction.step (mov_r64_imm64 .r10 10)
          (X86_64Instruction.step (mov_r64 .rax .r13) state)).gprs .r10 = 10 := rfl
    simpa [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64] using setTen

theorem spike2_two_digit_division_quotient (state : X86_64MachineState) :
    (spike2AfterTwoDigitDivision state).gprs .rax =
      UInt64.ofNat ((state.gprs .r13).toNat / 10) := by
  have projected := congrArg (fun result : X86_64MachineState => result.gprs .rax)
    (division_step state)
  have dividend :
      (X86_64Instruction.step (mov_r64_imm64 .r10 10)
        (X86_64Instruction.step (mov_r64 .rax .r13) state)).gprs .rax = state.gprs .r13 := rfl
  simpa [spike2AfterTwoDigitDivision, X86_64MachineState.setGpr64,
    step_xor_r32, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64, dividend] using projected

theorem spike2_two_digit_division_remainder (state : X86_64MachineState) :
    (spike2AfterTwoDigitDivision state).gprs .rdx =
      UInt64.ofNat ((state.gprs .r13).toNat % 10) := by
  have projected := congrArg (fun result : X86_64MachineState => result.gprs .rdx)
    (division_step state)
  have dividend :
      (X86_64Instruction.step (mov_r64_imm64 .r10 10)
        (X86_64Instruction.step (mov_r64 .rax .r13) state)).gprs .rax = state.gprs .r13 := rfl
  simpa [spike2AfterTwoDigitDivision, X86_64MachineState.setGpr64,
    step_xor_r32, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64, dividend] using projected

end Spikes.Spike2Fibonacci.Windows

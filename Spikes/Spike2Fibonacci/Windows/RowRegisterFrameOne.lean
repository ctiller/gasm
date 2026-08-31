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
-/import Spikes.Spike2Fibonacci.Windows.RowRegisterFrameOneSteps

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRegisterFrameOne :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxHeartbeats 5000000

theorem spike2_one_digit_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterOneDigitIndex state) := by
  let s1 := X86_64Instruction.step (mov_r64 .rax .r13) state
  let s2 := X86_64Instruction.step (add_r64_imm8 .rax 0x30) s1
  let s3 := X86_64Instruction.step (lea_rsp .rdi 0x44) s2
  let s4 := X86_64Instruction.step (mov_mem8 .rdi .rax) s3
  let s5 := X86_64Instruction.step (mov_rsp_byte 0x45 0x29) s4
  let s6 := X86_64Instruction.step (mov_rsp_byte 0x46 0x20) s5
  let s7 := X86_64Instruction.step (mov_rsp_byte 0x47 0x3d) s6
  let s8 := X86_64Instruction.step (mov_rsp_byte 0x48 0x20) s7
  let s9 := X86_64Instruction.step (lea_rsp .rdi 0x49) s8
  let s10 := X86_64Instruction.step (jmp_rel8 65) s9
  have h1 := spike2_frame_mov_rax_r13 state
  have h2 := spike2_frame_add_rax_imm s1 0x30
  have h3 := spike2_frame_lea_rdi_rsp s2 0x44
  have h4 := spike2_frame_mov_mem8_rdi s3 .rax
  have h5 := spike2_frame_mov_rsp_byte s4 0x45 0x29
  have h6 := spike2_frame_mov_rsp_byte s5 0x46 0x20
  have h7 := spike2_frame_mov_rsp_byte s6 0x47 0x3d
  have h8 := spike2_frame_mov_rsp_byte s7 0x48 0x20
  have h9 := spike2_frame_lea_rdi_rsp s8 0x49
  have h10 := spike2_frame_jmp_rel8 s9 65
  exact ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9).trans h10

end Spikes.Spike2Fibonacci.Windows

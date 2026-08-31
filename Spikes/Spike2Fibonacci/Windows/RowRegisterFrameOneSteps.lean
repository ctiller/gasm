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

local instance (priority := 1100) spike2WindowsRuntimeForRowRegisterFrameOneSteps :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

theorem spike2_frame_mov_rax_r13 (state : X86_64MachineState) :
    Spike2RowRegisterFrame state
      (X86_64Instruction.step (mov_r64 .rax .r13) state) := by
  constructor <;> rfl

theorem spike2_frame_add_rax_imm (state : X86_64MachineState) (imm : UInt8) :
    Spike2RowRegisterFrame state
      (X86_64Instruction.step (add_r64_imm8 .rax imm) state) := by
  constructor <;> rfl

theorem spike2_frame_lea_rdi_rsp (state : X86_64MachineState) (disp : UInt8) :
    Spike2RowRegisterFrame state
      (X86_64Instruction.step (lea_rsp .rdi disp) state) := by
  constructor <;> rfl

theorem spike2_frame_mov_mem8_rdi (state : X86_64MachineState) (src : Reg64) :
    Spike2RowRegisterFrame state
      (X86_64Instruction.step (mov_mem8 .rdi src) state) := by
  constructor <;> rfl

theorem spike2_frame_mov_rsp_byte (state : X86_64MachineState) (disp value : UInt8) :
    Spike2RowRegisterFrame state
      (X86_64Instruction.step (mov_rsp_byte disp value) state) := by
  constructor <;> rfl

theorem spike2_frame_jmp_rel8 (state : X86_64MachineState) (disp : UInt8) :
    Spike2RowRegisterFrame state
      (X86_64Instruction.step (jmp_rel8 disp) state) := by
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows

/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRegisterFrameBase

namespace Spikes.Spike2Fibonacci.Windows

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

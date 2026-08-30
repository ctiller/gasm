/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRegisterFrame

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- Cursor observations composed from the same cached one-step register boundaries. -/
theorem spike2_one_digit_cursor (state : X86_64MachineState) :
    (spike2AfterOneDigitIndex state).gprs .rdi = state.rsp + 73 := by
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
  have rsp8 : s8.rsp = state.rsp :=
    h8.rsp.trans (h7.rsp.trans (h6.rsp.trans
      (h5.rsp.trans (h4.rsp.trans (h3.rsp.trans (h2.rsp.trans h1.rsp))))))
  have rdi9 : s9.gprs .rdi = s8.rsp + 73 := by rfl
  have rdi10 : s10.gprs .rdi = s9.gprs .rdi := by rfl
  change s10.gprs .rdi = state.rsp + 73
  rw [rdi10, rdi9, rsp8]

theorem spike2_two_digit_cursor (state : X86_64MachineState) :
    (spike2AfterTwoDigitIndex state).gprs .rdi = state.rsp + 74 := by
  let s1 := X86_64Instruction.step (mov_rsp_byte 0x46 0x29) state
  let s2 := X86_64Instruction.step (mov_rsp_byte 0x47 0x20) s1
  let s3 := X86_64Instruction.step (mov_rsp_byte 0x48 0x3d) s2
  let s4 := X86_64Instruction.step (mov_rsp_byte 0x49 0x20) s3
  let s5 := X86_64Instruction.step (lea_rsp .rdi 0x4a) s4
  have h1 := spike2_frame_mov_rsp_byte state 0x46 0x29
  have h2 := spike2_frame_mov_rsp_byte s1 0x47 0x20
  have h3 := spike2_frame_mov_rsp_byte s2 0x48 0x3d
  have h4 := spike2_frame_mov_rsp_byte s3 0x49 0x20
  have rsp4 : s4.rsp = state.rsp := h4.rsp.trans (h3.rsp.trans (h2.rsp.trans h1.rsp))
  have rdi5 : s5.gprs .rdi = s4.rsp + 74 := by rfl
  change s5.gprs .rdi = state.rsp + 74
  rw [rdi5, rsp4]

end Spikes.Spike2Fibonacci.Windows

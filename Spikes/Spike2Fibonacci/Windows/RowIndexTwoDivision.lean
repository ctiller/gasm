/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowIndexTwoBranch

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

opaque spike2_two_digit_division_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713344)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) :
    Spike2FramedSliceResult state eventsRev 4 5368713362 := by
  let final := spike2AfterTwoDigitDivision state
  have frame := spike2_two_digit_division_registerFrame state
  have finalRip : final.rip = 5368713362 := by
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
    unfold final spike2AfterTwoDigitDivision
    rw [step_div_r64_by10 s3 zeroHigh divisor]
    change state.rip + 3 + 10 + 2 + 3 = 5368713362
    rw [hrip]
    rfl
  exact {
    final := final
    certificate := spike2_two_digit_division_selected_prefix state eventsRev hrip safe
    registers := frame
    rip := finalRip
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := spike2_two_digit_division_lowMemory state low }

end Spikes.Spike2Fibonacci.Windows

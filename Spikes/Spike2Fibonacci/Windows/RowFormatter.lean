/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.DecimalPhases

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

private theorem sequentialAddImm (dst : Reg64) (imm : UInt8) :
    SequentialInstruction (add_r64_imm8 dst imm) where
  encoding := .addImm8 dst imm
  safeFallthrough := by intro _ _; rfl

private theorem sequentialMovImm (dst : Reg64) (value : UInt64) :
    SequentialInstruction (mov_r64_imm64 dst value) where
  encoding := .loadImm dst value
  safeFallthrough := by intro _ _; rfl

private theorem divCoreFallthrough (state : X86_64MachineState)
    (safe : (X86_64Instruction.step (DivR64.mk .r10) state).fault = none) :
    (X86_64Instruction.step (DivR64.mk .r10) state).rip = state.rip + 3 := by
  simp only [X86_64Instruction.step] at safe ⊢
  split at safe
  · contradiction
  · rename_i hnonzero
    split at safe
    · contradiction
    · rename_i hfits
      simp [hnonzero, hfits]

private theorem sequentialDivR10 : SequentialInstruction (div_r64 .r10) where
  encoding := .div .r10
  safeFallthrough := by
    intro state safe
    let core : X86_64MachineState :=
      { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
      { divisor := .r10 } core).fault = none at safe
    change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
      { divisor := .r10 } core).rip = state.rip + 3
    exact divCoreFallthrough core safe

/-- The one-digit index slice ends at the common value-formatter setup. -/
def spike2AfterOneDigitIndex (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel8 65)
    (X86_64Instruction.step (lea_rsp .rdi 0x49)
      (X86_64Instruction.step (mov_rsp_byte 0x48 0x20)
        (X86_64Instruction.step (mov_rsp_byte 0x47 0x3d)
          (X86_64Instruction.step (mov_rsp_byte 0x46 0x20)
            (X86_64Instruction.step (mov_rsp_byte 0x45 0x29)
              (X86_64Instruction.step (mov_mem8 .rdi .rax)
                (X86_64Instruction.step (lea_rsp .rdi 0x44)
                  (X86_64Instruction.step (add_r64_imm8 .rax 0x30)
                    (X86_64Instruction.step (mov_r64 .rax .r13) state)))))))))

/-- Parameterized one-digit index producer.  Every intermediate and final successor is
unaligned, so the platform boundary checks are independent of mutable stack contents. -/
theorem spike2_one_digit_index_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713303)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 10 state eventsRev
      (spike2AfterOneDigitIndex state) eventsRev [] := by
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
  have h1 : s1.rip = 5368713306 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (mov_r64 .rax .r13) state).rip = state.rip + 3 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713310 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (add_r64_imm8 .rax 0x30) s1).rip = s1.rip + 4 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713315 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (lea_rsp .rdi 0x44) s2).rip = s2.rip + 5 by rfl, h2]; rfl
  have h4 : s4.rip = 5368713317 := by dsimp [s4]; rw [show (X86_64Instruction.step
    (mov_mem8 .rdi .rax) s3).rip = s3.rip + 2 by rfl, h3]; rfl
  have h5 : s5.rip = 5368713322 := by dsimp [s5]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x45 0x29) s4).rip = s4.rip + 5 by rfl, h4]; rfl
  have h6 : s6.rip = 5368713327 := by dsimp [s6]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x46 0x20) s5).rip = s5.rip + 5 by rfl, h5]; rfl
  have h7 : s7.rip = 5368713332 := by dsimp [s7]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x47 0x3d) s6).rip = s6.rip + 5 by rfl, h6]; rfl
  have h8 : s8.rip = 5368713337 := by dsimp [s8]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x48 0x20) s7).rip = s7.rip + 5 by rfl, h7]; rfl
  have h9 : s9.rip = 5368713342 := by dsimp [s9]; rw [show (X86_64Instruction.step
    (lea_rsp .rdi 0x49) s8).rip = s8.rip + 5 by rfl, h8]; rfl
  have h10 : s10.rip = 5368713409 := by
    dsimp [s10]
    rw [show (X86_64Instruction.step (jmp_rel8 65) s9).rip =
      s9.rip + 2 + signExtend8To64 65 by rfl, h9]
    rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have hs2 : s2.fault = none := by change s1.fault = none; exact hs1
  have hs3 : s3.fault = none := by change s2.fault = none; exact hs2
  have hs4 : s4.fault = none := by change s3.fault = none; exact hs3
  have hs5 : s5.fault = none := by change s4.fault = none; exact hs4
  have hs6 : s6.fault = none := by change s5.fault = none; exact hs5
  have hs7 : s7.fault = none := by change s6.fault = none; exact hs6
  have hs8 : s8.fault = none := by change s7.fault = none; exact hs7
  have hs9 : s9.fault = none := by change s8.fault = none; exact hs8
  have hs10 : s10.fault = none := by change s9.fault = none; exact hs9
  have p1 := spike2_selected_local_prefix (mov_r64 .rax .r13)
    (ControlFlowFree.mov .rax .r13).sequential state eventsRev (by rw [hrip]; rfl)
    5368713306 h1 (by decide) (by decide) hs1
  have p2 := spike2_selected_local_prefix (add_r64_imm8 .rax 0x30)
    (sequentialAddImm .rax 0x30) s1 eventsRev (by rw [h1]; rfl)
    5368713310 h2 (by decide) (by decide) hs2
  have p3 := spike2_selected_local_prefix (lea_rsp .rdi 0x44)
    ({ encoding := .leaRsp .rdi 0x44
       safeFallthrough := by intro _ _; rfl })
    s2 eventsRev (by rw [h2]; rfl)
    5368713315 h3 (by decide) (by decide) hs3
  have p4 := spike2_selected_local_prefix (mov_mem8 .rdi .rax)
    ({ encoding := .movMem8 .rdi .rax
       safeFallthrough := by intro _ _; rfl })
    s3 eventsRev (by rw [h3]; rfl)
    5368713317 h4 (by decide) (by decide) hs4
  have p5 := spike2_selected_local_prefix (mov_rsp_byte 0x45 0x29)
    ({ encoding := .movRspByte 0x45 0x29
       safeFallthrough := by intro _ _; rfl })
    s4 eventsRev (by rw [h4]; rfl)
    5368713322 h5 (by decide) (by decide) hs5
  have p6 := spike2_selected_local_prefix (mov_rsp_byte 0x46 0x20)
    ({ encoding := .movRspByte 0x46 0x20
       safeFallthrough := by intro _ _; rfl })
    s5 eventsRev (by rw [h5]; rfl)
    5368713327 h6 (by decide) (by decide) hs6
  have p7 := spike2_selected_local_prefix (mov_rsp_byte 0x47 0x3d)
    ({ encoding := .movRspByte 0x47 0x3d
       safeFallthrough := by intro _ _; rfl })
    s6 eventsRev (by rw [h6]; rfl)
    5368713332 h7 (by decide) (by decide) hs7
  have p8 := spike2_selected_local_prefix (mov_rsp_byte 0x48 0x20)
    ({ encoding := .movRspByte 0x48 0x20
       safeFallthrough := by intro _ _; rfl })
    s7 eventsRev (by rw [h7]; rfl)
    5368713337 h8 (by decide) (by decide) hs8
  have p9 := spike2_selected_local_prefix (lea_rsp .rdi 0x49)
    ({ encoding := .leaRsp .rdi 0x49
       safeFallthrough := by intro _ _; rfl })
    s8 eventsRev (by rw [h8]; rfl)
    5368713342 h9 (by decide) (by decide) hs9
  have boundary := spike2_selected_silent_unaligned s10 5368713409 h10
    (by decide) (by decide)
  have p10 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s9 eventsRev s10 eventsRev [] := by
    exact .directBranch (.rel8 65) (by rw [h9]; rfl)
      (by rw [h10]; exact boundary.1) (by rw [h10]; exact boundary.2)
      hs10 (.nil _ _)
  have joined := ((((((((p1.append p2).append p3).append p4).append p5).append p6).append p7).append p8).append p9).append p10
  simpa [spike2AfterOneDigitIndex, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
    using joined

/-- Register setup and safe division for the two-digit index path. -/
def spike2AfterTwoDigitDivision (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (div_r64 .r10)
    (X86_64Instruction.step (xor_r32 .edx .edx)
      (X86_64Instruction.step (mov_r64_imm64 .r10 10)
        (X86_64Instruction.step (mov_r64 .rax .r13) state)))

theorem spike2_two_digit_division_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713344)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 4 state eventsRev
      (spike2AfterTwoDigitDivision state) eventsRev [] := by
  let s1 := X86_64Instruction.step (mov_r64 .rax .r13) state
  let s2 := X86_64Instruction.step (mov_r64_imm64 .r10 10) s1
  let s3 := X86_64Instruction.step (xor_r32 .edx .edx) s2
  let s4 := spike2AfterTwoDigitDivision state
  have step4 : X86_64Instruction.step (div_r64 .r10) s3 = s4 := by rfl
  have h1 : s1.rip = 5368713347 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (mov_r64 .rax .r13) state).rip = state.rip + 3 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713357 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (mov_r64_imm64 .r10 10) s1).rip = s1.rip + 10 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713359 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (xor_r32 .edx .edx) s2).rip = s2.rip + 2 by rfl, h2]; rfl
  have zeroHigh : s3.gprs .rdx = 0 := by
    dsimp [s3]
    simp [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64]
  have divisor2 : s2.gprs .r10 = 10 := by dsimp [s2]; rfl
  have divisor : s3.gprs .r10 = 10 := by
    dsimp [s3]
    simpa [step_xor_r32, X86_64MachineState.setGpr32,
      X86_64MachineState.setFlagsLogic, reg32To64] using divisor2
  have divStep := step_div_r64_by10 s3 zeroHigh divisor
  have h4 : s4.rip = 5368713362 := by rw [← step4, divStep, h3]; rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have hs2 : s2.fault = none := by change s1.fault = none; exact hs1
  have hs3 : s3.fault = none := by change s2.fault = none; exact hs2
  have hs4 : s4.fault = none := by rw [← step4, divStep]; exact hs3
  have p1 := spike2_selected_local_prefix (mov_r64 .rax .r13)
    (ControlFlowFree.mov .rax .r13).sequential state eventsRev (by rw [hrip]; rfl)
    5368713347 h1 (by decide) (by decide) hs1
  have p2 := spike2_selected_local_prefix (mov_r64_imm64 .r10 10)
    (sequentialMovImm .r10 10) s1 eventsRev (by rw [h1]; rfl)
    5368713357 h2 (by decide) (by decide) hs2
  have p3 := spike2_selected_local_prefix (xor_r32 .edx .edx)
    ({ encoding := .xor32 .edx .edx
       safeFallthrough := by intro _ _; rfl }) s2 eventsRev (by rw [h2]; rfl)
    5368713359 h3 (by decide) (by decide) hs3
  have p4 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s3 eventsRev s4 eventsRev [] := by
    rw [← step4]
    exact spike2_selected_local_prefix (div_r64 .r10) sequentialDivR10 s3 eventsRev
      (by rw [h3]; rfl) 5368713362 (by rw [divStep, h3]; rfl)
      (by decide) (by decide) (by rw [divStep]; exact hs3)
  exact ((p1.append p2).append p3).append p4

/-- ASCII adjustment and the first digit store. -/
def spike2AfterTwoDigitTens (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_mem8 .rdi .rax)
    (X86_64Instruction.step (lea_rsp .rdi 0x44)
      (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
        (X86_64Instruction.step (add_r64_imm8 .rax 0x30) state)))

theorem spike2_two_digit_tens_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713362)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 4 state eventsRev
      (spike2AfterTwoDigitTens state) eventsRev [] := by
  let s1 := X86_64Instruction.step (add_r64_imm8 .rax 0x30) state
  let s2 := X86_64Instruction.step (add_r64_imm8 .rdx 0x30) s1
  let s3 := X86_64Instruction.step (lea_rsp .rdi 0x44) s2
  let s4 := spike2AfterTwoDigitTens state
  have step4 : X86_64Instruction.step (mov_mem8 .rdi .rax) s3 = s4 := by rfl
  have h1 : s1.rip = 5368713366 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (add_r64_imm8 .rax 0x30) state).rip = state.rip + 4 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713370 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (add_r64_imm8 .rdx 0x30) s1).rip = s1.rip + 4 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713375 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (lea_rsp .rdi 0x44) s2).rip = s2.rip + 5 by rfl, h2]; rfl
  have h4 : s4.rip = 5368713377 := by rw [← step4, show (X86_64Instruction.step
    (mov_mem8 .rdi .rax) s3).rip = s3.rip + 2 by rfl, h3]; rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have hs2 : s2.fault = none := by change s1.fault = none; exact hs1
  have hs3 : s3.fault = none := by change s2.fault = none; exact hs2
  have hs4 : s4.fault = none := by rw [← step4]; change s3.fault = none; exact hs3
  have p1 := spike2_selected_local_prefix (add_r64_imm8 .rax 0x30)
    (sequentialAddImm .rax 0x30) state eventsRev (by rw [hrip]; rfl)
    5368713366 h1 (by decide) (by decide) hs1
  have p2 := spike2_selected_local_prefix (add_r64_imm8 .rdx 0x30)
    (sequentialAddImm .rdx 0x30) s1 eventsRev (by rw [h1]; rfl)
    5368713370 h2 (by decide) (by decide) hs2
  have p3 := spike2_selected_local_prefix (lea_rsp .rdi 0x44)
    ({ encoding := .leaRsp .rdi 0x44
       safeFallthrough := by intro _ _; rfl }) s2 eventsRev (by rw [h2]; rfl)
    5368713375 h3 (by decide) (by decide) hs3
  have p4 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s3 eventsRev s4 eventsRev [] := by
    rw [← step4]
    exact spike2_selected_local_prefix (mov_mem8 .rdi .rax)
      ({ encoding := .movMem8 .rdi .rax
         safeFallthrough := by intro _ _; rfl }) s3 eventsRev (by rw [h3]; rfl)
      5368713377 (by
        rw [show (X86_64Instruction.step (mov_mem8 .rdi .rax) s3).rip = s3.rip + 2 by rfl,
          h3]
        rfl) (by decide) (by decide)
      (by change s3.fault = none; exact hs3)
  exact ((p1.append p2).append p3).append p4

/-- Second digit store, whose successor is the sole aligned cutpoint on this index path. -/
def spike2AfterTwoDigitHead (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_mem8 .rdi .rdx)
    (X86_64Instruction.step (lea_rsp .rdi 0x45) state)

theorem spike2_two_digit_head_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713377)
    (hsafe : state.fault = none)
    (alignedSelected : selectedNonInputPlatformCall (spike2AfterTwoDigitHead state).rip
      (spike2AfterTwoDigitHead state) = true)
    (alignedSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterTwoDigitHead state).rip (spike2AfterTwoDigitHead state) = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2 state eventsRev
      (spike2AfterTwoDigitHead state) eventsRev [] := by
  let s1 := X86_64Instruction.step (lea_rsp .rdi 0x45) state
  let s2 := spike2AfterTwoDigitHead state
  have step2 : X86_64Instruction.step (mov_mem8 .rdi .rdx) s1 = s2 := by rfl
  have h1 : s1.rip = 5368713382 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (lea_rsp .rdi 0x45) state).rip = state.rip + 5 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713384 := by rw [← step2, show (X86_64Instruction.step
    (mov_mem8 .rdi .rdx) s1).rip = s1.rip + 2 by rfl, h1]; rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have p1 := spike2_selected_local_prefix (lea_rsp .rdi 0x45)
    ({ encoding := .leaRsp .rdi 0x45
       safeFallthrough := by intro _ _; rfl }) state eventsRev (by rw [hrip]; rfl)
    5368713382 h1 (by decide) (by decide) hs1
  have p2 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s1 eventsRev s2 eventsRev [] := by
    rw [← step2]
    exact .ordinary ({ encoding := .movMem8 .rdi .rdx
                       safeFallthrough := by intro _ _; rfl }) (by rw [h1]; rfl)
      (by rw [step2]; exact alignedSelected) (by rw [step2]; exact alignedSilent)
      (by change s1.fault = none; exact hs1) (.nil _ _)
  exact p1.append p2

/-- Remaining two-digit punctuation stores and output cursor setup. -/
def spike2AfterTwoDigitIndex (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (lea_rsp .rdi 0x4a)
    (X86_64Instruction.step (mov_rsp_byte 0x49 0x20)
      (X86_64Instruction.step (mov_rsp_byte 0x48 0x3d)
        (X86_64Instruction.step (mov_rsp_byte 0x47 0x20)
          (X86_64Instruction.step (mov_rsp_byte 0x46 0x29) state))))

theorem spike2_two_digit_tail_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713384)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 5 state eventsRev
      (spike2AfterTwoDigitIndex state) eventsRev [] := by
  let s1 := X86_64Instruction.step (mov_rsp_byte 0x46 0x29) state
  let s2 := X86_64Instruction.step (mov_rsp_byte 0x47 0x20) s1
  let s3 := X86_64Instruction.step (mov_rsp_byte 0x48 0x3d) s2
  let s4 := X86_64Instruction.step (mov_rsp_byte 0x49 0x20) s3
  let s5 := X86_64Instruction.step (lea_rsp .rdi 0x4a) s4
  have h1 : s1.rip = 5368713389 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x46 0x29) state).rip = state.rip + 5 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713394 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x47 0x20) s1).rip = s1.rip + 5 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713399 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x48 0x3d) s2).rip = s2.rip + 5 by rfl, h2]; rfl
  have h4 : s4.rip = 5368713404 := by dsimp [s4]; rw [show (X86_64Instruction.step
    (mov_rsp_byte 0x49 0x20) s3).rip = s3.rip + 5 by rfl, h3]; rfl
  have h5 : s5.rip = 5368713409 := by dsimp [s5]; rw [show (X86_64Instruction.step
    (lea_rsp .rdi 0x4a) s4).rip = s4.rip + 5 by rfl, h4]; rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have hs2 : s2.fault = none := by change s1.fault = none; exact hs1
  have hs3 : s3.fault = none := by change s2.fault = none; exact hs2
  have hs4 : s4.fault = none := by change s3.fault = none; exact hs3
  have hs5 : s5.fault = none := by change s4.fault = none; exact hs4
  have p1 := spike2_selected_local_prefix (mov_rsp_byte 0x46 0x29)
    ({ encoding := .movRspByte 0x46 0x29
       safeFallthrough := by intro _ _; rfl }) state eventsRev (by rw [hrip]; rfl)
    5368713389 h1 (by decide) (by decide) hs1
  have p2 := spike2_selected_local_prefix (mov_rsp_byte 0x47 0x20)
    ({ encoding := .movRspByte 0x47 0x20
       safeFallthrough := by intro _ _; rfl }) s1 eventsRev (by rw [h1]; rfl)
    5368713394 h2 (by decide) (by decide) hs2
  have p3 := spike2_selected_local_prefix (mov_rsp_byte 0x48 0x3d)
    ({ encoding := .movRspByte 0x48 0x3d
       safeFallthrough := by intro _ _; rfl }) s2 eventsRev (by rw [h2]; rfl)
    5368713399 h3 (by decide) (by decide) hs3
  have p4 := spike2_selected_local_prefix (mov_rsp_byte 0x49 0x20)
    ({ encoding := .movRspByte 0x49 0x20
       safeFallthrough := by intro _ _; rfl }) s3 eventsRev (by rw [h3]; rfl)
    5368713404 h4 (by decide) (by decide) hs4
  have p5 := spike2_selected_local_prefix (lea_rsp .rdi 0x4a)
    ({ encoding := .leaRsp .rdi 0x4a
       safeFallthrough := by intro _ _; rfl }) s4 eventsRev (by rw [h4]; rfl)
    5368713409 h5 (by decide) (by decide) hs5
  simpa [spike2AfterTwoDigitIndex, s1, s2, s3, s4, s5] using
    ((((p1.append p2).append p3).append p4).append p5)

/-- Three shared register-only instructions establish the bidirectional decimal-loop entry. -/
def spike2AfterDecimalSetup (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx)
    (X86_64Instruction.step (mov_r64_imm64 .r10 10)
      (X86_64Instruction.step (mov_r64 .rax .r14) state))

theorem spike2_decimal_setup_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713409)
    (hsafe : state.fault = none)
    (text3424 : (spike2AfterDecimalSetup state).read64 5368713424 ≠ 5368713424) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 3 state eventsRev
      (spike2AfterDecimalSetup state) eventsRev [] := by
  let s1 := X86_64Instruction.step (mov_r64 .rax .r14) state
  let s2 := X86_64Instruction.step (mov_r64_imm64 .r10 10) s1
  let s3 := X86_64Instruction.step (xor_r32 .ecx .ecx) s2
  have h1 : s1.rip = 5368713412 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (mov_r64 .rax .r14) state).rip = state.rip + 3 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713422 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (mov_r64_imm64 .r10 10) s1).rip = s1.rip + 10 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713424 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (xor_r32 .ecx .ecx) s2).rip = s2.rip + 2 by rfl, h2]; rfl
  have p1 := spike2_selected_local_prefix (mov_r64 .rax .r14)
    (ControlFlowFree.mov .rax .r14).sequential state eventsRev (by rw [hrip]; rfl)
    5368713412 h1 (by decide) (by decide) (by change state.fault = none; exact hsafe)
  have p2 := spike2_selected_local_prefix (mov_r64_imm64 .r10 10)
    (sequentialMovImm .r10 10) s1 eventsRev (by rw [h1]; rfl)
    5368713422 h2 (by decide) (by decide) (by change state.fault = none; exact hsafe)
  have boundary := spike2_selected_silent_nonIat s3 5368713424 h3 (by decide) (by
    simpa [spike2AfterDecimalSetup, s1, s2, s3] using text3424)
  have p3 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s2 eventsRev s3 eventsRev [] := by
    exact .ordinary ({ encoding := .xor32 .ecx .ecx
                       safeFallthrough := by intro _ _; rfl })
      (by rw [h2]; rfl)
      (by rw [h3]; exact boundary.1) (by rw [h3]; exact boundary.2)
      (by change state.fault = none; exact hsafe) (.nil _ _)
  simpa [spike2AfterDecimalSetup, s1, s2, s3] using (p1.append p2).append p3

end Spikes.Spike2Fibonacci.Windows

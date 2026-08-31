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
-/import Spikes.Spike2Fibonacci.Windows.RowOutputSetup
import Spikes.Spike2Fibonacci.Windows.RowWriteTail
import Spikes.Spike2Fibonacci.Windows.FormatterLiteral

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowFrame :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The immutable code/IAT prefix below the formatter's high stack arena. -/
def spike2RowLowMemoryTop : Nat := 5368721440

def Spike2RowLowMemory (state : X86_64MachineState) : Prop :=
  ∀ address, address.toNat + 8 ≤ spike2RowLowMemoryTop →
    state.read64 address = spike2AfterPrologue.read64 address

theorem Spike2RowLowMemory.write8 {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (address : UInt64) (value : UInt8)
    (noWrap : address.toNat + 1 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ address.toNat) :
    Spike2RowLowMemory (state.write8 address value) := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w8 address value.toUInt64 state.memory) = _
  rw [X86_64Mem.read64_write_below .w8 state.memory address observed value.toUInt64
    noWrap (by omega)]
  exact holds observed below

theorem Spike2RowLowMemory.write32 {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (address : UInt64) (value : UInt32)
    (noWrap : address.toNat + 4 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ address.toNat) :
    Spike2RowLowMemory (state.write32 address value) := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w32 address value.toUInt64 state.memory) = _
  rw [X86_64Mem.read64_write_below .w32 state.memory address observed value.toUInt64
    noWrap (by omega)]
  exact holds observed below

theorem Spike2RowLowMemory.write64 {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (address value : UInt64)
    (noWrap : address.toNat + 8 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ address.toNat) :
    Spike2RowLowMemory (state.write64 address value) := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w64 address value state.memory) = _
  rw [X86_64Mem.read64_write_below .w64 state.memory address observed value
    noWrap (by omega)]
  exact holds observed below

theorem Spike2RowLowMemory.of_memory_eq {initial final : X86_64MachineState}
    (holds : Spike2RowLowMemory initial) (memory : final.memory = initial.memory) :
    Spike2RowLowMemory final := by
  intro address below
  change X86_64Mem.read .w64 address final.memory = _
  rw [memory]
  exact holds address below

theorem Spike2RowLowMemory.movRspByte {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (disp value : UInt8)
    (noWrap : (state.rsp + signExtend8To64 disp).toNat + 1 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ (state.rsp + signExtend8To64 disp).toNat) :
    Spike2RowLowMemory (X86_64Instruction.step (mov_rsp_byte disp value) state) := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w8 (state.rsp + signExtend8To64 disp) value.toUInt64 state.memory) = _
  rw [X86_64Mem.read64_write_below .w8 state.memory _ observed value.toUInt64
    noWrap (by omega)]
  exact holds observed below

theorem Spike2RowLowMemory.movMem8 {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (dst src : Reg64)
    (noWrap : (state.gprs dst).toNat + 1 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ (state.gprs dst).toNat) :
    Spike2RowLowMemory (X86_64Instruction.step (mov_mem8 dst src) state) := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w8 (state.gprs dst) (state.gprs src).toUInt8.toUInt64 state.memory) = _
  rw [X86_64Mem.read64_write_below .w8 state.memory _ observed _ noWrap (by omega)]
  exact holds observed below

theorem Spike2RowLowMemory.movRsp64 {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (disp : UInt8) (value : UInt32)
    (noWrap : (state.rsp + signExtend8To64 disp).toNat + 8 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ (state.rsp + signExtend8To64 disp).toNat) :
    Spike2RowLowMemory (X86_64Instruction.step (mov_rsp64 disp value) state) := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w64 (state.rsp + signExtend8To64 disp)
        (signExtendUInt32To64 value) state.memory) = _
  rw [X86_64Mem.read64_write_below .w64 state.memory _ observed _ noWrap (by omega)]
  exact holds observed below

theorem spike2_after_prologue_lowMemory : Spike2RowLowMemory spike2AfterPrologue := by
  intro _ _
  rfl

/-- Scalar stack boundary exported without exposing the concrete prologue state to row consumers. -/
theorem spike2_after_prologue_rsp_eq :
    spike2AfterPrologue.rsp = 140737488289664 := by
  rfl

theorem spike2_fib_literal_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterFibLiteral state) := by
  let s1 := X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state
  let s2 := X86_64Instruction.step (mov_rsp_byte 0x41 0x69) s1
  let s3 := X86_64Instruction.step (mov_rsp_byte 0x42 0x62) s2
  have h1 : Spike2RowLowMemory s1 := holds.movRspByte 0x40 0x46
    (by rw [show state.rsp + signExtend8To64 0x40 =
      spike2AfterPrologue.rsp + signExtend8To64 0x40 by rw [rsp]]; decide)
    (by rw [show state.rsp + signExtend8To64 0x40 =
      spike2AfterPrologue.rsp + signExtend8To64 0x40 by rw [rsp]]; decide)
  have h2 : Spike2RowLowMemory s2 := h1.movRspByte 0x41 0x69
    (by rw [show s1.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s1.rsp = state.rsp by rfl, rsp]; decide)
  have h3 : Spike2RowLowMemory s3 := h2.movRspByte 0x42 0x62
    (by rw [show s2.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s2.rsp = state.rsp by rfl, rsp]; decide)
  have h4 := h3.movRspByte 0x43 0x28
    (by rw [show s3.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s3.rsp = state.rsp by rfl, rsp]; decide)
  simpa only [spike2AfterFibLiteral, s1, s2, s3] using h4

theorem spike2_one_digit_index_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterOneDigitIndex state) := by
  let s1 := X86_64Instruction.step (mov_r64 .rax .r13) state
  let s2 := X86_64Instruction.step (add_r64_imm8 .rax 0x30) s1
  let s3 := X86_64Instruction.step (lea_rsp .rdi 0x44) s2
  let s4 := X86_64Instruction.step (mov_mem8 .rdi .rax) s3
  let s5 := X86_64Instruction.step (mov_rsp_byte 0x45 0x29) s4
  let s6 := X86_64Instruction.step (mov_rsp_byte 0x46 0x20) s5
  let s7 := X86_64Instruction.step (mov_rsp_byte 0x47 0x3d) s6
  let s8 := X86_64Instruction.step (mov_rsp_byte 0x48 0x20) s7
  have h3 : Spike2RowLowMemory s3 := holds.of_memory_eq (by rfl)
  have rdi3 : s3.gprs .rdi = state.rsp + signExtend8To64 0x44 := by rfl
  have h4 : Spike2RowLowMemory s4 := h3.movMem8 .rdi .rax
    (by rw [rdi3, rsp]; decide) (by rw [rdi3, rsp]; decide)
  have h5 : Spike2RowLowMemory s5 := h4.movRspByte 0x45 0x29
    (by rw [show s4.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s4.rsp = state.rsp by rfl, rsp]; decide)
  have h6 : Spike2RowLowMemory s6 := h5.movRspByte 0x46 0x20
    (by rw [show s5.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s5.rsp = state.rsp by rfl, rsp]; decide)
  have h7 : Spike2RowLowMemory s7 := h6.movRspByte 0x47 0x3d
    (by rw [show s6.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s6.rsp = state.rsp by rfl, rsp]; decide)
  have h8 : Spike2RowLowMemory s8 := h7.movRspByte 0x48 0x20
    (by rw [show s7.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s7.rsp = state.rsp by rfl, rsp]; decide)
  apply h8.of_memory_eq
  rfl

theorem spike2_two_digit_division_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state) :
    Spike2RowLowMemory (spike2AfterTwoDigitDivision state) := by
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
  apply holds.of_memory_eq
  unfold spike2AfterTwoDigitDivision
  rw [step_div_r64_by10 s3 zeroHigh divisor]
  rfl

theorem spike2_two_digit_tens_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterTwoDigitTens state) := by
  let s1 := X86_64Instruction.step (add_r64_imm8 .rax 0x30) state
  let s2 := X86_64Instruction.step (add_r64_imm8 .rdx 0x30) s1
  let s3 := X86_64Instruction.step (lea_rsp .rdi 0x44) s2
  have h3 : Spike2RowLowMemory s3 := holds.of_memory_eq (by rfl)
  have rdi3 : s3.gprs .rdi = state.rsp + signExtend8To64 0x44 := by rfl
  have h4 := h3.movMem8 .rdi .rax (by rw [rdi3, rsp]; decide)
    (by rw [rdi3, rsp]; decide)
  simpa only [spike2AfterTwoDigitTens, s1, s2, s3] using h4

theorem spike2_two_digit_head_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterTwoDigitHead state) := by
  let s1 := X86_64Instruction.step (lea_rsp .rdi 0x45) state
  have h1 : Spike2RowLowMemory s1 := holds.of_memory_eq (by rfl)
  have rdi1 : s1.gprs .rdi = state.rsp + signExtend8To64 0x45 := by rfl
  have h2 := h1.movMem8 .rdi .rdx (by rw [rdi1, rsp]; decide)
    (by rw [rdi1, rsp]; decide)
  simpa only [spike2AfterTwoDigitHead, s1] using h2

theorem spike2_two_digit_tail_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterTwoDigitIndex state) := by
  let s1 := X86_64Instruction.step (mov_rsp_byte 0x46 0x29) state
  let s2 := X86_64Instruction.step (mov_rsp_byte 0x47 0x20) s1
  let s3 := X86_64Instruction.step (mov_rsp_byte 0x48 0x3d) s2
  let s4 := X86_64Instruction.step (mov_rsp_byte 0x49 0x20) s3
  have h1 := holds.movRspByte 0x46 0x29
    (by rw [rsp]; decide) (by rw [rsp]; decide)
  have h2 := h1.movRspByte 0x47 0x20
    (by rw [show s1.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s1.rsp = state.rsp by rfl, rsp]; decide)
  have h3 := h2.movRspByte 0x48 0x3d
    (by rw [show s2.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s2.rsp = state.rsp by rfl, rsp]; decide)
  have h4 := h3.movRspByte 0x49 0x20
    (by rw [show s3.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s3.rsp = state.rsp by rfl, rsp]; decide)
  apply h4.of_memory_eq
  rfl

theorem spike2_decimal_setup_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state) :
    Spike2RowLowMemory (spike2AfterDecimalSetup state) :=
  holds.of_memory_eq (by rfl)

theorem spike2_line_terminator_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (cursorAbove : spike2RowLowMemoryTop ≤ (state.gprs .rdi).toNat)
    (cursorRoom : (state.gprs .rdi).toNat + 2 ≤ 2 ^ 64) :
    Spike2RowLowMemory (spike2AfterLineTerminator state) := by
  let s1 := X86_64Instruction.step (mov_r64_imm64 .rax 13) state
  let s2 := X86_64Instruction.step (mov_mem8 .rdi .rax) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdi 1) s2
  let s4 := X86_64Instruction.step (mov_r64_imm64 .rax 10) s3
  let s5 := X86_64Instruction.step (mov_mem8 .rdi .rax) s4
  have rdi1 : s1.gprs .rdi = state.gprs .rdi := by rfl
  have h2 : Spike2RowLowMemory s2 := (holds.of_memory_eq (by rfl)).movMem8 .rdi .rax
    (by rw [rdi1]; omega) (by rw [rdi1]; exact cursorAbove)
  have rdi4 : s4.gprs .rdi = state.gprs .rdi + 1 := by rfl
  have rdi4Nat : (s4.gprs .rdi).toNat = (state.gprs .rdi).toNat + 1 := by
    rw [rdi4, UInt64.toNat_add]
    have bound : (state.gprs .rdi).toNat + 1 < 2 ^ 64 := by omega
    simp [Nat.mod_eq_of_lt bound]
  have h5 : Spike2RowLowMemory s5 := (h2.of_memory_eq (by rfl)).movMem8 .rdi .rax
    (by rw [rdi4Nat]; omega) (by rw [rdi4Nat]; omega)
  apply h5.of_memory_eq
  rfl

theorem spike2_write_setup_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2BeforeWriteFile state) := by
  let s1 := X86_64Instruction.step (mov_r64 .rcx .r12) state
  let s2 := X86_64Instruction.step (lea_rsp .rdx 0x40) s1
  let s3 := X86_64Instruction.step (mov_r64 .r8 .rdi) s2
  let s4 := X86_64Instruction.step (sub_r64 .r8 .rdx) s3
  let s5 := X86_64Instruction.step (lea_rsp .r9 0x28) s4
  have h5 : Spike2RowLowMemory s5 := holds.of_memory_eq (by rfl)
  have result := h5.movRsp64 0x20 0
    (by rw [show s5.rsp = state.rsp by rfl, rsp]; decide)
    (by rw [show s5.rsp = state.rsp by rfl, rsp]; decide)
  simpa only [spike2BeforeWriteFile, s1, s2, s3, s4, s5] using result

end Spikes.Spike2Fibonacci.Windows

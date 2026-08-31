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
-/import Spikes.Spike2Fibonacci.Windows.RowFormatter

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowOutputSetup :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

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

/-- CRLF append slice, separated from the Win32 call setup. -/
def spike2AfterLineTerminator (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .rdi 1)
    (X86_64Instruction.step (mov_mem8 .rdi .rax)
      (X86_64Instruction.step (mov_r64_imm64 .rax 10)
        (X86_64Instruction.step (add_r64_imm8 .rdi 1)
          (X86_64Instruction.step (mov_mem8 .rdi .rax)
            (X86_64Instruction.step (mov_r64_imm64 .rax 13) state)))))

theorem spike2_line_terminator_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713457)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6 state eventsRev
      (spike2AfterLineTerminator state) eventsRev [] := by
  let s1 := X86_64Instruction.step (mov_r64_imm64 .rax 13) state
  let s2 := X86_64Instruction.step (mov_mem8 .rdi .rax) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdi 1) s2
  let s4 := X86_64Instruction.step (mov_r64_imm64 .rax 10) s3
  let s5 := X86_64Instruction.step (mov_mem8 .rdi .rax) s4
  let s6 := spike2AfterLineTerminator state
  have step6 : X86_64Instruction.step (add_r64_imm8 .rdi 1) s5 = s6 := by rfl
  have h1 : s1.rip = 5368713467 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (mov_r64_imm64 .rax 13) state).rip = state.rip + 10 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713469 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (mov_mem8 .rdi .rax) s1).rip = s1.rip + 2 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713473 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (add_r64_imm8 .rdi 1) s2).rip = s2.rip + 4 by rfl, h2]; rfl
  have h4 : s4.rip = 5368713483 := by dsimp [s4]; rw [show (X86_64Instruction.step
    (mov_r64_imm64 .rax 10) s3).rip = s3.rip + 10 by rfl, h3]; rfl
  have h5 : s5.rip = 5368713485 := by dsimp [s5]; rw [show (X86_64Instruction.step
    (mov_mem8 .rdi .rax) s4).rip = s4.rip + 2 by rfl, h4]; rfl
  have h6 : s6.rip = 5368713489 := by rw [← step6, show (X86_64Instruction.step
    (add_r64_imm8 .rdi 1) s5).rip = s5.rip + 4 by rfl, h5]; rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have hs2 : s2.fault = none := by change s1.fault = none; exact hs1
  have hs3 : s3.fault = none := by change s2.fault = none; exact hs2
  have hs4 : s4.fault = none := by change s3.fault = none; exact hs3
  have hs5 : s5.fault = none := by change s4.fault = none; exact hs4
  have p1 := spike2_selected_local_prefix (mov_r64_imm64 .rax 13)
    (sequentialMovImm .rax 13) state eventsRev (by rw [hrip]; rfl)
    5368713467 h1 (by decide) (by decide) hs1
  have p2 := spike2_selected_local_prefix (mov_mem8 .rdi .rax)
    ({ encoding := .movMem8 .rdi .rax
       safeFallthrough := by intro _ _; rfl }) s1 eventsRev (by rw [h1]; rfl)
    5368713469 h2 (by decide) (by decide) hs2
  have p3 := spike2_selected_local_prefix (add_r64_imm8 .rdi 1)
    (sequentialAddImm .rdi 1) s2 eventsRev (by rw [h2]; rfl)
    5368713473 h3 (by decide) (by decide) hs3
  have p4 := spike2_selected_local_prefix (mov_r64_imm64 .rax 10)
    (sequentialMovImm .rax 10) s3 eventsRev (by rw [h3]; rfl)
    5368713483 h4 (by decide) (by decide) hs4
  have p5 := spike2_selected_local_prefix (mov_mem8 .rdi .rax)
    ({ encoding := .movMem8 .rdi .rax
       safeFallthrough := by intro _ _; rfl }) s4 eventsRev (by rw [h4]; rfl)
    5368713485 h5 (by decide) (by decide) hs5
  have p6 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s5 eventsRev s6 eventsRev [] := by
    rw [← step6]
    exact spike2_selected_local_prefix (add_r64_imm8 .rdi 1)
      (sequentialAddImm .rdi 1) s5 eventsRev (by rw [h5]; rfl)
      5368713489 (by
        rw [show (X86_64Instruction.step (add_r64_imm8 .rdi 1) s5).rip = s5.rip + 4 by rfl,
          h5]
        rfl) (by decide) (by decide)
      (by change s5.fault = none; exact hs5)
  exact (((((p1.append p2).append p3).append p4).append p5).append p6)

/-- Register and shadow-space setup immediately before the real WriteFile import call. -/
def spike2BeforeWriteFile (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_rsp64 0x20 0)
    (X86_64Instruction.step (lea_rsp .r9 0x28)
      (X86_64Instruction.step (sub_r64 .r8 .rdx)
        (X86_64Instruction.step (mov_r64 .r8 .rdi)
          (X86_64Instruction.step (lea_rsp .rdx 0x40)
            (X86_64Instruction.step (mov_r64 .rcx .r12) state)))))

theorem spike2_write_setup_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713489)
    (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6 state eventsRev
      (spike2BeforeWriteFile state) eventsRev [] := by
  let s1 := X86_64Instruction.step (mov_r64 .rcx .r12) state
  let s2 := X86_64Instruction.step (lea_rsp .rdx 0x40) s1
  let s3 := X86_64Instruction.step (mov_r64 .r8 .rdi) s2
  let s4 := X86_64Instruction.step (sub_r64 .r8 .rdx) s3
  let s5 := X86_64Instruction.step (lea_rsp .r9 0x28) s4
  let s6 := spike2BeforeWriteFile state
  have step6 : X86_64Instruction.step (mov_rsp64 0x20 0) s5 = s6 := by rfl
  have h1 : s1.rip = 5368713492 := by dsimp [s1]; rw [show (X86_64Instruction.step
    (mov_r64 .rcx .r12) state).rip = state.rip + 3 by rfl, hrip]; rfl
  have h2 : s2.rip = 5368713497 := by dsimp [s2]; rw [show (X86_64Instruction.step
    (lea_rsp .rdx 0x40) s1).rip = s1.rip + 5 by rfl, h1]; rfl
  have h3 : s3.rip = 5368713500 := by dsimp [s3]; rw [show (X86_64Instruction.step
    (mov_r64 .r8 .rdi) s2).rip = s2.rip + 3 by rfl, h2]; rfl
  have h4 : s4.rip = 5368713503 := by dsimp [s4]; rw [show (X86_64Instruction.step
    (sub_r64 .r8 .rdx) s3).rip = s3.rip + 3 by rfl, h3]; rfl
  have h5 : s5.rip = 5368713508 := by dsimp [s5]; rw [show (X86_64Instruction.step
    (lea_rsp .r9 0x28) s4).rip = s4.rip + 5 by rfl, h4]; rfl
  have h6 : s6.rip = 5368713517 := by rw [← step6, show (X86_64Instruction.step
    (mov_rsp64 0x20 0) s5).rip = s5.rip + 9 by rfl, h5]; rfl
  have hs1 : s1.fault = none := by change state.fault = none; exact hsafe
  have hs2 : s2.fault = none := by change s1.fault = none; exact hs1
  have hs3 : s3.fault = none := by change s2.fault = none; exact hs2
  have hs4 : s4.fault = none := by change s3.fault = none; exact hs3
  have hs5 : s5.fault = none := by change s4.fault = none; exact hs4
  have p1 := spike2_selected_local_prefix (mov_r64 .rcx .r12)
    (ControlFlowFree.mov .rcx .r12).sequential state eventsRev (by rw [hrip]; rfl)
    5368713492 h1 (by decide) (by decide) hs1
  have p2 := spike2_selected_local_prefix (lea_rsp .rdx 0x40)
    ({ encoding := .leaRsp .rdx 0x40
       safeFallthrough := by intro _ _; rfl }) s1 eventsRev (by rw [h1]; rfl)
    5368713497 h2 (by decide) (by decide) hs2
  have p3 := spike2_selected_local_prefix (mov_r64 .r8 .rdi)
    (ControlFlowFree.mov .r8 .rdi).sequential s2 eventsRev (by rw [h2]; rfl)
    5368713500 h3 (by decide) (by decide) hs3
  have p4 := spike2_selected_local_prefix (sub_r64 .r8 .rdx)
    (ControlFlowFree.sub .r8 .rdx).sequential s3 eventsRev (by rw [h3]; rfl)
    5368713503 h4 (by decide) (by decide) hs4
  have p5 := spike2_selected_local_prefix (lea_rsp .r9 0x28)
    ({ encoding := .leaRsp .r9 0x28
       safeFallthrough := by intro _ _; rfl }) s4 eventsRev (by rw [h4]; rfl)
    5368713508 h5 (by decide) (by decide) hs5
  have p6 : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      s5 eventsRev s6 eventsRev [] := by
    rw [← step6]
    exact spike2_selected_local_prefix (mov_rsp64 0x20 0)
      ({ encoding := .movRsp64 0x20 0
         safeFallthrough := by intro _ _; rfl }) s5 eventsRev (by rw [h5]; rfl)
      5368713517 (by
        rw [show (X86_64Instruction.step (mov_rsp64 0x20 0) s5).rip = s5.rip + 9 by rfl,
          h5]
        rfl) (by decide) (by decide)
      (by change s5.fault = none; exact hs5)
  exact (((((p1.append p2).append p3).append p4).append p5).append p6)

end Spikes.Spike2Fibonacci.Windows

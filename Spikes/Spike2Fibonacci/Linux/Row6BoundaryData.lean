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

import Gasm.Targets.X86_64.EventfulSegment
import Gasm.Targets.Linux.OutcomeBridge
import Spikes.Spike2Fibonacci.Linux.Row5BoundaryData

open Spikes.Spike2Fibonacci.Linux.Row5BoundaryData

/-!
# First linked Linux Spike 2 row

This module owns the finite, instruction-indexed certificate for the first real Fibonacci output
row.  It is deliberately split from the universal equivalence module so Lean caches the row
certificate independently of the 90-row composition.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row6BoundaryData

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem sequentialMovRspByte40 :
    SequentialInstruction (mov_rsp_byte 0x40 0x46) where
  encoding := .movRspByte 0x40 0x46
  safeFallthrough := by intro _ _; rfl

theorem spike2Row6SequentialCmp (dst : Reg64) (value : UInt8) :
    SequentialInstruction (cmp_r64_imm8 dst value) where
  encoding := .compareImm8 dst value
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

theorem spike2Row6SequentialDivR10 : SequentialInstruction (div_r64 .r10) where
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

/-- The exact state after the literal `"Fib("` stores and the linked one-digit index branch. -/
def spike2Row6AfterIndexHeader : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41)
    (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
              (spike2AfterMainHeader spike2Row5AfterRecurrence))))))

/-- The real joined value-format entry reached by the row-one one-digit branch. -/
def spike2Row6AfterIndex : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel8 65)
    (X86_64Instruction.step (lea_rsp .rdi 0x49)
      (X86_64Instruction.step (mov_rsp_byte 0x48 0x20)
        (X86_64Instruction.step (mov_rsp_byte 0x47 0x3d)
          (X86_64Instruction.step (mov_rsp_byte 0x46 0x20)
            (X86_64Instruction.step (mov_rsp_byte 0x45 0x29)
              (X86_64Instruction.step (mov_mem8 .rdi .rax)
                (X86_64Instruction.step (lea_rsp .rdi 0x44)
                  (X86_64Instruction.step (add_r64_imm8 .rax 0x30)
                    (X86_64Instruction.step (mov_r64 .rax .r13)
                      spike2Row6AfterIndexHeader)))))))))

/-- Entry to the real decimal extraction loop for the first value, which is one. -/
def spike2Row6AfterValueSetup : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx)
    (X86_64Instruction.step (mov_r64_imm64 .r10 10)
      (X86_64Instruction.step (mov_r64 .rax .r14) spike2Row6AfterIndex))

/-- The terminating single extraction pass for row one's value. -/
def spike2Row6AfterExtraction : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 236)
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row6AfterValueSetup))))))

/-- The terminating pop/write pass which materializes row one's sole decimal digit. -/
def spike2Row6AfterWrite : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 243)
    (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) spike2Row6AfterExtraction))))

/-- The line terminator stores are kept separate from decimal formatting so this certificate
matches the production formatter/write schedule one instruction at a time. -/
def spike2Row6AfterLineTerminator : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .rdi 1)
    (X86_64Instruction.step (mov_mem8 .rdi .rax)
      (X86_64Instruction.step (mov_r64_imm64 .rax 10)
        (X86_64Instruction.step (add_r64_imm8 .rdi 1)
          (X86_64Instruction.step (mov_mem8 .rdi .rax)
            (X86_64Instruction.step (mov_r64_imm64 .rax 13) spike2Row6AfterWrite)))))

/-- Register setup immediately before the production Linux `SYS_write` instruction. -/
def spike2Row6BeforeWriteSyscall : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .eax 1)
    (X86_64Instruction.step (mov_r32 .edi 1)
      (X86_64Instruction.step (mov_r64 .rdx .r8)
        (X86_64Instruction.step (sub_r64 .r8 .rsi)
          (X86_64Instruction.step (lea_rsp .rsi 0x40)
            (X86_64Instruction.step (mov_r64 .r8 .rdi) spike2Row6AfterLineTerminator)))))

/-- The host-resumed state after the real selected `SYS_write` call. -/
def spike2Row6AfterWriteSyscall : X86_64MachineState :=
  (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).1

/-- Reverse event accumulator after row one's selected write boundary. -/
def spike2Row6WriteEventsRev : List AnyEvent :=
  accumulateEvent [] (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row6BeforeWriteSyscall)).2

/-- The actual main-loop-header state reached after row one's recurrence and back edge. -/
def spike2Row6AfterRecurrence : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967027)
    (X86_64Instruction.step (add_r64_imm8 .r13 1)
      (X86_64Instruction.step (mov_r64 .r15 .r8)
        (X86_64Instruction.step (mov_r64 .r14 .r15)
          (X86_64Instruction.step (add_r64 .r8 .r15)
            (X86_64Instruction.step (mov_r64 .r8 .r14) spike2Row6AfterWriteSyscall)))))

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
end Spikes.Spike2Fibonacci.Linux.Row6BoundaryData

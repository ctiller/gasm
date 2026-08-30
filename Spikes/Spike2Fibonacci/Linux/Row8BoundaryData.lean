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
import Spikes.Spike2Fibonacci.Linux.Row7BoundaryData

open Spikes.Spike2Fibonacci.Linux.Row7BoundaryData

/-!
# First linked Linux Spike 2 row

This module owns the finite, instruction-indexed certificate for the first real Fibonacci output
row.  It is deliberately split from the universal equivalence module so Lean caches the row
certificate independently of the 90-row composition.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

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

theorem spike2Row8SequentialCmp (dst : Reg64) (value : UInt8) :
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

theorem spike2Row8SequentialDivR10 : SequentialInstruction (div_r64 .r10) where
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
def spike2Row8AfterIndexHeader : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41)
    (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
              (spike2AfterMainHeader spike2Row7AfterRecurrence))))))

/-- The real joined value-format entry reached by Row 8's one-digit index branch. -/
def spike2Row8AfterIndex : X86_64MachineState :=
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
                      spike2Row8AfterIndexHeader)))))))))

/-- Entry to the real decimal extraction loop for the first value, which is one. -/
def spike2Row8AfterValueSetup : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .ecx .ecx)
    (X86_64Instruction.step (mov_r64_imm64 .r10 10)
      (X86_64Instruction.step (mov_r64 .rax .r14) spike2Row8AfterIndex))

/-- The first decimal extraction pass for Row 8's two-digit value. -/
def spike2Row8AfterExtractionFirst : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 236)
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
              (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup))))))

/-- First decimal extraction pass for row 8's two-digit value. -/
def spike2Row8AfterExtraction : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 236)
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0)
      (X86_64Instruction.step (add_r64_imm8 .rcx 1)
        (X86_64Instruction.step (push_r64 .rdx)
          (X86_64Instruction.step (add_r64_imm8 .rdx 0x30)
            (X86_64Instruction.step (div_r64 .r10)
              (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst))))))

/-- The first decimal pop/write pass for Row 8's two digits. -/
def spike2Row8AfterWriteFirst : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 243)
    (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterExtraction))))

/-- Second and final decimal write pass for row 8's two digits. -/
def spike2Row8AfterWrite : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 243)
    (X86_64Instruction.step (sub_r64_imm8 .rcx 1)
      (X86_64Instruction.step (add_r64_imm8 .rdi 1)
        (X86_64Instruction.step (mov_mem8 .rdi .rdx)
          (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterWriteFirst))))

/-- The line terminator stores are kept separate from decimal formatting so this certificate
matches the production formatter/write schedule one instruction at a time. -/
def spike2Row8AfterLineTerminator : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm8 .rdi 1)
    (X86_64Instruction.step (mov_mem8 .rdi .rax)
      (X86_64Instruction.step (mov_r64_imm64 .rax 10)
        (X86_64Instruction.step (add_r64_imm8 .rdi 1)
          (X86_64Instruction.step (mov_mem8 .rdi .rax)
            (X86_64Instruction.step (mov_r64_imm64 .rax 13) spike2Row8AfterWrite)))))

/-- Register setup immediately before the production Linux `SYS_write` instruction. -/
def spike2Row8BeforeWriteSyscall : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .eax 1)
    (X86_64Instruction.step (mov_r32 .edi 1)
      (X86_64Instruction.step (mov_r64 .rdx .r8)
        (X86_64Instruction.step (sub_r64 .r8 .rsi)
          (X86_64Instruction.step (lea_rsp .rsi 0x40)
            (X86_64Instruction.step (mov_r64 .r8 .rdi) spike2Row8AfterLineTerminator)))))

/-- The host-resumed state after the real selected `SYS_write` call. -/
def spike2Row8AfterWriteSyscall : X86_64MachineState :=
  (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall)).1

/-- Reverse event accumulator after Row 8's selected write boundary. -/
def spike2Row8WriteEventsRev : List AnyEvent :=
  accumulateEvent [] (sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op spike2Row8BeforeWriteSyscall)).2

/-- The actual main-loop-header state reached after Row 8's recurrence and back edge. -/
def spike2Row8AfterRecurrence : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967027)
    (X86_64Instruction.step (add_r64_imm8 .r13 1)
      (X86_64Instruction.step (mov_r64 .r15 .r8)
        (X86_64Instruction.step (mov_r64 .r14 .r15)
          (X86_64Instruction.step (add_r64 .r8 .r15)
            (X86_64Instruction.step (mov_r64 .r8 .r14) spike2Row8AfterWriteSyscall)))))

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/

theorem spike2Row8IndexHeaderLookupF : instructionAtRipIndexed spike2Indexed (spike2AfterMainHeader spike2Row7AfterRecurrence).rip = some (mov_rsp_byte 0x40 0x46) := by rfl
theorem spike2Row8IndexHeaderLookupI : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence)).rip = some (mov_rsp_byte 0x41 0x69) := by rfl
theorem spike2Row8IndexHeaderLookupB : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence))).rip = some (mov_rsp_byte 0x42 0x62) := by rfl
theorem spike2Row8IndexHeaderLookupOpen : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence)))).rip = some (mov_rsp_byte 0x43 0x28) := by rfl
theorem spike2Row8IndexHeaderLookupCmp : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x43 0x28) (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence))))).rip = some (cmp_r64_imm8 .r13 10) := by rfl
theorem spike2Row8IndexHeaderLookupBranch : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (cmp_r64_imm8 .r13 10) (X86_64Instruction.step (mov_rsp_byte 0x43 0x28) (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence)))))).rip = some (jge_rel8 41) := by rfl

theorem spike2Row8IndexLookupMove : instructionAtRipIndexed spike2Indexed spike2Row8AfterIndexHeader.rip = some (mov_r64 .rax .r13) := by rfl
theorem spike2Row8IndexLookupAscii : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader).rip = some (add_r64_imm8 .rax 0x30) := by rfl
theorem spike2Row8IndexLookupCursor : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader)).rip = some (lea_rsp .rdi 0x44) := by rfl
theorem spike2Row8IndexLookupStore : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader))).rip = some (mov_mem8 .rdi .rax) := by rfl
theorem spike2Row8IndexLookupClose : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_mem8 .rdi .rax) (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader)))).rip = some (mov_rsp_byte 0x45 0x29) := by rfl
theorem spike2Row8IndexLookupSpace : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x45 0x29) (X86_64Instruction.step (mov_mem8 .rdi .rax) (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader))))).rip = some (mov_rsp_byte 0x46 0x20) := by rfl
theorem spike2Row8IndexLookupEquals : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x46 0x20) (X86_64Instruction.step (mov_rsp_byte 0x45 0x29) (X86_64Instruction.step (mov_mem8 .rdi .rax) (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader)))))).rip = some (mov_rsp_byte 0x47 0x3d) := by rfl
theorem spike2Row8IndexLookupValueSpace : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x47 0x3d) (X86_64Instruction.step (mov_rsp_byte 0x46 0x20) (X86_64Instruction.step (mov_rsp_byte 0x45 0x29) (X86_64Instruction.step (mov_mem8 .rdi .rax) (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader))))))).rip = some (mov_rsp_byte 0x48 0x20) := by rfl
theorem spike2Row8IndexLookupValueCursor : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x48 0x20) (X86_64Instruction.step (mov_rsp_byte 0x47 0x3d) (X86_64Instruction.step (mov_rsp_byte 0x46 0x20) (X86_64Instruction.step (mov_rsp_byte 0x45 0x29) (X86_64Instruction.step (mov_mem8 .rdi .rax) (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader)))))))).rip = some (lea_rsp .rdi 0x49) := by rfl
theorem spike2Row8IndexLookupJoin : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (lea_rsp .rdi 0x49) (X86_64Instruction.step (mov_rsp_byte 0x48 0x20) (X86_64Instruction.step (mov_rsp_byte 0x47 0x3d) (X86_64Instruction.step (mov_rsp_byte 0x46 0x20) (X86_64Instruction.step (mov_rsp_byte 0x45 0x29) (X86_64Instruction.step (mov_mem8 .rdi .rax) (X86_64Instruction.step (lea_rsp .rdi 0x44) (X86_64Instruction.step (add_r64_imm8 .rax 0x30) (X86_64Instruction.step (mov_r64 .rax .r13) spike2Row8AfterIndexHeader))))))))).rip = some (jmp_rel8 65) := by rfl

theorem spike2Row8ValueSetupLookupMove : instructionAtRipIndexed spike2Indexed spike2Row8AfterIndex.rip = some (mov_r64 .rax .r14) := by rfl
theorem spike2Row8ValueSetupLookupBase : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_r64 .rax .r14) spike2Row8AfterIndex).rip = some (mov_r64_imm64 .r10 10) := by rfl
theorem spike2Row8ValueSetupLookupCount : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_r64_imm64 .r10 10) (X86_64Instruction.step (mov_r64 .rax .r14) spike2Row8AfterIndex)).rip = some (xor_r32 .ecx .ecx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupXor : instructionAtRipIndexed spike2Indexed spike2Row8AfterValueSetup.rip = some (xor_r32 .edx .edx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupDiv : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup).rip = some (div_r64 .r10) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupAscii : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup)).rip = some (add_r64_imm8 .rdx 0x30) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupPush : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup))).rip = some (push_r64 .rdx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupCount : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (push_r64 .rdx) (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup)))).rip = some (add_r64_imm8 .rcx 1) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupCmp : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rcx 1) (X86_64Instruction.step (push_r64 .rdx) (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup))))).rip = some (cmp_r64_imm8 .rax 0) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionFirstLookupBranch : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (cmp_r64_imm8 .rax 0) (X86_64Instruction.step (add_r64_imm8 .rcx 1) (X86_64Instruction.step (push_r64 .rdx) (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterValueSetup)))))).rip = some (jne_rel8 236) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupXor : instructionAtRipIndexed spike2Indexed spike2Row8AfterExtractionFirst.rip = some (xor_r32 .edx .edx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupDiv : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst).rip = some (div_r64 .r10) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupAscii : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst)).rip = some (add_r64_imm8 .rdx 0x30) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupPush : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst))).rip = some (push_r64 .rdx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupCount : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (push_r64 .rdx) (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst)))).rip = some (add_r64_imm8 .rcx 1) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupCmp : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rcx 1) (X86_64Instruction.step (push_r64 .rdx) (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst))))).rip = some (cmp_r64_imm8 .rax 0) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8ExtractionSecondLookupBranch : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (cmp_r64_imm8 .rax 0) (X86_64Instruction.step (add_r64_imm8 .rcx 1) (X86_64Instruction.step (push_r64 .rdx) (X86_64Instruction.step (add_r64_imm8 .rdx 0x30) (X86_64Instruction.step (div_r64 .r10) (X86_64Instruction.step (xor_r32 .edx .edx) spike2Row8AfterExtractionFirst)))))).rip = some (jne_rel8 236) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteFirstLookupPop : instructionAtRipIndexed spike2Indexed spike2Row8AfterExtraction.rip = some (pop_r64 .rdx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteFirstLookupStore : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterExtraction).rip = some (mov_mem8 .rdi .rdx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteFirstLookupCursor : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_mem8 .rdi .rdx) (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterExtraction)).rip = some (add_r64_imm8 .rdi 1) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteFirstLookupDecrement : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rdi 1) (X86_64Instruction.step (mov_mem8 .rdi .rdx) (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterExtraction))).rip = some (sub_r64_imm8 .rcx 1) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteFirstLookupBranch : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (sub_r64_imm8 .rcx 1) (X86_64Instruction.step (add_r64_imm8 .rdi 1) (X86_64Instruction.step (mov_mem8 .rdi .rdx) (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterExtraction)))).rip = some (jne_rel8 243) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteSecondLookupPop : instructionAtRipIndexed spike2Indexed spike2Row8AfterWriteFirst.rip = some (pop_r64 .rdx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteSecondLookupStore : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterWriteFirst).rip = some (mov_mem8 .rdi .rdx) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteSecondLookupCursor : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_mem8 .rdi .rdx) (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterWriteFirst)).rip = some (add_r64_imm8 .rdi 1) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteSecondLookupDecrement : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (add_r64_imm8 .rdi 1) (X86_64Instruction.step (mov_mem8 .rdi .rdx) (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterWriteFirst))).rip = some (sub_r64_imm8 .rcx 1) := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/
theorem spike2Row8WriteSecondLookupBranch : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (sub_r64_imm8 .rcx 1) (X86_64Instruction.step (add_r64_imm8 .rdi 1) (X86_64Instruction.step (mov_mem8 .rdi .rdx) (X86_64Instruction.step (pop_r64 .rdx) spike2Row8AfterWriteFirst)))).rip = some (jne_rel8 243) := by rfl
end Spikes.Spike2Fibonacci.Linux.Row8BoundaryData

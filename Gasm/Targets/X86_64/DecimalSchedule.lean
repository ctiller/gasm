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

import Gasm.Targets.X86_64.DecimalSegments
import Stdlib.Fmt.UInt64DecimalSchedule

/-!
# x86-64 realization of the bounded UInt64 decimal schedule

This layer connects the artifact-indexed production passes to the portable extraction/reverse
schedule. It retains exact target execution and selected-call evidence; it creates no evaluator,
artifact, export, or `VerifiedProgram` authority.
-/

namespace Gasm.Targets.X86_64.DecimalSchedule

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Stdlib.Fmt

private theorem divByTenCoreQuotient (state : X86_64MachineState)
    (highZero : state.gprs .rdx = 0) (divisorTen : state.gprs .r10 = 10) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs .rax =
      UInt64.ofNat ((state.gprs .rax).toNat / 10) := by
  simp only [X86_64Instruction.step]
  rw [divisorTen, highZero]
  have bound : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF := by
    have := (state.gprs .rax).toNat_lt
    omega
  have notOverflow : ¬ 0xFFFFFFFFFFFFFFFF < (state.gprs .rax).toNat / 10 :=
    Nat.not_lt_of_ge bound
  simp [notOverflow, X86_64MachineState.setGpr64]

private theorem divByTenCoreRemainder (state : X86_64MachineState)
    (highZero : state.gprs .rdx = 0) (divisorTen : state.gprs .r10 = 10) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs .rdx =
      UInt64.ofNat ((state.gprs .rax).toNat % 10) := by
  simp only [X86_64Instruction.step]
  rw [divisorTen, highZero]
  have bound : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF := by
    have := (state.gprs .rax).toNat_lt
    omega
  have notOverflow : ¬ 0xFFFFFFFFFFFFFFFF < (state.gprs .rax).toNat / 10 :=
    Nat.not_lt_of_ge bound
  simp [notOverflow, X86_64MachineState.setGpr64]

private theorem xorEdxCoreZero (state : X86_64MachineState) :
    (X86_64Instruction.step (XorR32R32.mk .edx .edx) state).gprs .rdx = 0 := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64]

private theorem divCorePreservesGpr (state : X86_64MachineState) (r : Reg64)
    (notRax : r ≠ .rax) (notRdx : r ≠ .rdx) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs r = state.gprs r := by
  simp only [X86_64Instruction.step]
  split
  · rfl
  · split
    · rfl
    · simp [X86_64MachineState.setGpr64, notRax, notRdx]

private theorem divCorePreservesMemory (state : X86_64MachineState) :
    (X86_64Instruction.step (DivR64.mk .r10) state).memory = state.memory := by
  simp only [X86_64Instruction.step]
  split
  · rfl
  · split <;> rfl

theorem extractionAfterDiv_preservesGpr (initial : X86_64MachineState) (r : Reg64)
    (notRax : r ≠ .rax) (notRdx : r ≠ .rdx) :
    (extractionStates initial).2.1.gprs r = initial.gprs r := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).gprs r = initial.gprs r
  rw [divCorePreservesGpr core r notRax notRdx]
  let input : X86_64MachineState :=
    { initial with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step XorR32R32 instX86_64InstructionXorR32R32
    { dst := .edx, src := .edx } input).gprs r = initial.gprs r
  dsimp only [input]
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64, notRdx]

theorem extractionAfterDiv_preservesMemory (initial : X86_64MachineState) :
    (extractionStates initial).2.1.memory = initial.memory := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).memory = initial.memory
  rw [divCorePreservesMemory core]
  rfl

theorem extractionAfterDiv_quotient (initial : X86_64MachineState)
    (divisorTen : initial.gprs .r10 = 10) :
    (extractionStates initial).2.1.gprs .rax =
      UInt64.ofNat ((initial.gprs .rax).toNat / 10) := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).gprs .rax = UInt64.ofNat ((initial.gprs .rax).toNat / 10)
  rw [divByTenCoreQuotient core]
  · rfl
  · change (X86_64Instruction.step (xor_r32 .edx .edx) initial).gprs .rdx = 0
    let input : X86_64MachineState :=
      { initial with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step XorR32R32 instX86_64InstructionXorR32R32
      { dst := .edx, src := .edx } input).gprs .rdx = 0
    exact xorEdxCoreZero input
  · exact divisorTen

theorem extractionAfterDiv_remainder (initial : X86_64MachineState)
    (divisorTen : initial.gprs .r10 = 10) :
    (extractionStates initial).2.1.gprs .rdx =
      UInt64.ofNat ((initial.gprs .rax).toNat % 10) := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).gprs .rdx = UInt64.ofNat ((initial.gprs .rax).toNat % 10)
  rw [divByTenCoreRemainder core]
  · rfl
  · change (X86_64Instruction.step (xor_r32 .edx .edx) initial).gprs .rdx = 0
    let input : X86_64MachineState :=
      { initial with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step XorR32R32 instX86_64InstructionXorR32R32
      { dst := .edx, src := .edx } input).gprs .rdx = 0
    exact xorEdxCoreZero input
  · exact divisorTen

/-- Architectural consequences of one extraction pass. Memory is stated as the exact PUSH
update; callers may derive any disjoint frame observation from that equation. -/
structure ExtractionPassEffect (backDisp : UInt8)
    (initial final : X86_64MachineState) : Prop where
  final_eq : final = extractionFinal backDisp initial
  quotient : final.gprs .rax = UInt64.ofNat ((initial.gprs .rax).toNat / 10)
  asciiRemainder : final.gprs .rdx = UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30
  count : final.gprs .rcx = initial.gprs .rcx + 1
  stackPointer : final.rsp = initial.rsp - 8
  memory : final.memory = X86_64Mem.write .w64 (initial.rsp - 8)
    (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30) initial.memory
  preservesR12 : final.gprs .r12 = initial.gprs .r12
  preservesR13 : final.gprs .r13 = initial.gprs .r13
  preservesR14 : final.gprs .r14 = initial.gprs .r14
  preservesR15 : final.gprs .r15 = initial.gprs .r15
  fault : final.fault = none

/-- Architectural consequences of one pop/write pass. Memory is the exact one-byte store. -/
structure WritePassEffect (backDisp : UInt8)
    (initial final : X86_64MachineState) : Prop where
  final_eq : final = writeFinal backDisp initial
  poppedDigit : final.gprs .rdx = initial.read64 initial.rsp
  cursor : final.gprs .rdi = initial.gprs .rdi + 1
  count : final.gprs .rcx = initial.gprs .rcx - 1
  stackPointer : final.rsp = initial.rsp + 8
  memory : final.memory = X86_64Mem.write .w8 (initial.gprs .rdi)
    (initial.read64 initial.rsp).toUInt8.toUInt64 initial.memory
  preservesR12 : final.gprs .r12 = initial.gprs .r12
  preservesR13 : final.gprs .r13 = initial.gprs .r13
  preservesR14 : final.gprs .r14 = initial.gprs .r14
  preservesR15 : final.gprs .r15 = initial.gprs .r15
  fault : final.fault = none

theorem extractionPassEffect (backDisp : UInt8) (stackLower : UInt64)
    (initial : X86_64MachineState) (pre : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety backDisp initial) :
    ExtractionPassEffect backDisp initial (extractionFinal backDisp initial) := by
  constructor
  · rfl
  · rw [show (extractionFinal backDisp initial).gprs .rax =
        (extractionStates initial).2.1.gprs .rax by rfl]
    exact extractionAfterDiv_quotient initial pre.divisorTen
  · rw [show (extractionFinal backDisp initial).gprs .rdx =
        (extractionStates initial).2.1.gprs .rdx + 0x30 by rfl]
    rw [extractionAfterDiv_remainder initial pre.divisorTen]
  · rw [show (extractionFinal backDisp initial).gprs .rcx =
        (extractionStates initial).2.1.gprs .rcx + 1 by rfl]
    rw [extractionAfterDiv_preservesGpr initial .rcx (by decide) (by decide)]
  · rw [show (extractionFinal backDisp initial).rsp =
        (extractionStates initial).2.1.rsp - 8 by rfl]
    change (extractionStates initial).2.1.gprs .rsp - 8 = initial.gprs .rsp - 8
    rw [extractionAfterDiv_preservesGpr initial .rsp (by decide) (by decide)]
  · rw [show (extractionFinal backDisp initial).memory =
        X86_64Mem.write .w64 ((extractionStates initial).2.1.rsp - 8)
          ((extractionStates initial).2.1.gprs .rdx + 0x30)
          (extractionStates initial).2.1.memory by rfl]
    rw [extractionAfterDiv_preservesMemory initial]
    rw [extractionAfterDiv_remainder initial pre.divisorTen]
    change X86_64Mem.write .w64
      ((extractionStates initial).2.1.gprs .rsp - 8)
      (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 48) initial.memory =
      X86_64Mem.write .w64 (initial.gprs .rsp - 8)
      (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 48) initial.memory
    rw [extractionAfterDiv_preservesGpr initial .rsp (by decide) (by decide)]
  · rw [show (extractionFinal backDisp initial).gprs .r12 =
        (extractionStates initial).2.1.gprs .r12 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r12 (by decide) (by decide)
  · rw [show (extractionFinal backDisp initial).gprs .r13 =
        (extractionStates initial).2.1.gprs .r13 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r13 (by decide) (by decide)
  · rw [show (extractionFinal backDisp initial).gprs .r14 =
        (extractionStates initial).2.1.gprs .r14 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r14 (by decide) (by decide)
  · rw [show (extractionFinal backDisp initial).gprs .r15 =
        (extractionStates initial).2.1.gprs .r15 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r15 (by decide) (by decide)
  · exact safe.branchSafe

theorem writePassEffect (backDisp : UInt8) (stackUpper bufferLimit : UInt64)
    (initial : X86_64MachineState) (_pre : WriteSafety stackUpper bufferLimit initial)
    (safe : WriteExecutionSafety backDisp initial) :
    WritePassEffect backDisp initial (writeFinal backDisp initial) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact safe.branchSafe

/-- Any caller-selected byte outside the exact pushed word is preserved. The no-wrap premise is
the memory hook's real range law, not an informal stack-frame assertion. -/
theorem ExtractionPassEffect.preservesMemoryAt {backDisp : UInt8}
    {initial final : X86_64MachineState}
    (effect : ExtractionPassEffect backDisp initial final) (address : UInt64)
    (noWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (outside : address.toNat < (initial.rsp - 8).toNat ∨
      (initial.rsp - 8).toNat + 8 ≤ address.toNat) :
    X86_64Mem.readByte final.memory address = X86_64Mem.readByte initial.memory address := by
  rw [effect.memory]
  exact X86_64Mem.readByte_write_disjoint .w64 _ _ _ _ noWrap outside

/-- Any caller-selected byte other than the exact output cursor is preserved by one write pass. -/
theorem WritePassEffect.preservesMemoryAt {backDisp : UInt8}
    {initial final : X86_64MachineState}
    (effect : WritePassEffect backDisp initial final) (address : UInt64)
    (noWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (outside : address.toNat < (initial.gprs .rdi).toNat ∨
      (initial.gprs .rdi).toNat + 1 ≤ address.toNat) :
    X86_64Mem.readByte final.memory address = X86_64Mem.readByte initial.memory address := by
  rw [effect.memory]
  exact X86_64Mem.readByte_write_disjoint .w8 _ _ _ _ noWrap outside

end Gasm.Targets.X86_64.DecimalSchedule

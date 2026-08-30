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

import Spikes.Spike2Fibonacci.Linux.RowTailByteAuthority

/-! # Decimal text authority across row write setup and syscall -/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
namespace Row8Parametric

private theorem sysWriteHook_preserves_read64 (state : X86_64MachineState)
    (address : UInt64) :
    (sysWriteHook (Event := AnyEvent) state).1.read64 address = state.read64 address := by
  simp only [sysWriteHook]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

private theorem authority_afterMovR8Rdi (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r64 .r8 .rdi) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterLeaRsi (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (lea_rsp .rsi 0x40) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterSubR8Rsi (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (sub_r64 .r8 .rsi) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterMovRdxR8 (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r64 .rdx .r8) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterMovEdi (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r32 .edi 1) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterMovEax (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r32 .eax 1) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterSyscallInstruction (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step syscall_op state) :=
  authority.transportRead64 _ _ (by intro; rfl)

theorem decimalAuthority_afterWriteSetupEnd {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterLineTerminator predecessor)) :
    Spike2DecimalTextAuthority (afterWriteSetupEnd predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r64 .r8 .rdi) (afterLineTerminator predecessor))
  exact authority_afterMovR8Rdi _ authority

theorem decimalAuthority_afterWriteSetupBuffer {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSetupEnd predecessor)) :
    Spike2DecimalTextAuthority (afterWriteSetupBuffer predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (lea_rsp .rsi 0x40) (afterWriteSetupEnd predecessor))
  exact authority_afterLeaRsi _ authority

theorem decimalAuthority_afterWriteSetupLength {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSetupBuffer predecessor)) :
    Spike2DecimalTextAuthority (afterWriteSetupLength predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (sub_r64 .r8 .rsi) (afterWriteSetupBuffer predecessor))
  exact authority_afterSubR8Rsi _ authority

theorem decimalAuthority_afterWriteSetupCount {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSetupLength predecessor)) :
    Spike2DecimalTextAuthority (afterWriteSetupCount predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r64 .rdx .r8) (afterWriteSetupLength predecessor))
  exact authority_afterMovRdxR8 _ authority

theorem decimalAuthority_afterWriteSetupFd {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSetupCount predecessor)) :
    Spike2DecimalTextAuthority (afterWriteSetupFd predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r32 .edi 1) (afterWriteSetupCount predecessor))
  exact authority_afterMovEdi _ authority

theorem decimalAuthority_beforeWriteSyscall {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSetupFd predecessor)) :
    Spike2DecimalTextAuthority (beforeWriteSyscall predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r32 .eax 1) (afterWriteSetupFd predecessor))
  exact authority_afterMovEax _ authority

theorem decimalAuthority_beforeWriteHook {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (beforeWriteSyscall predecessor)) :
    Spike2DecimalTextAuthority (beforeWriteHook predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step syscall_op (beforeWriteSyscall predecessor))
  exact authority_afterSyscallInstruction _ authority

/-- Register-only write setup and the write hook preserve decimal text authority. -/
theorem decimalAuthority_afterWriteSyscall {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterLineTerminator predecessor)) :
    Spike2DecimalTextAuthority (afterWriteSyscall predecessor) := by
  have atEnd := decimalAuthority_afterWriteSetupEnd (predecessor := predecessor) authority
  have atBuffer := decimalAuthority_afterWriteSetupBuffer (predecessor := predecessor) atEnd
  have atLength := decimalAuthority_afterWriteSetupLength (predecessor := predecessor) atBuffer
  have atCount := decimalAuthority_afterWriteSetupCount (predecessor := predecessor) atLength
  have atFd := decimalAuthority_afterWriteSetupFd (predecessor := predecessor) atCount
  have atSyscall := decimalAuthority_beforeWriteSyscall (predecessor := predecessor) atFd
  have atHook := decimalAuthority_beforeWriteHook (predecessor := predecessor) atSyscall
  exact atHook.transportRead64 _ _ (sysWriteHook_preserves_read64 _)

end Row8Parametric

end Spikes.Spike2Fibonacci.Linux

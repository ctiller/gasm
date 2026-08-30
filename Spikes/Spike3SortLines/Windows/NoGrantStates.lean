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
import Spikes.Spike3SortLines.NativeOutcome
import Spikes.Spike3SortLines.Windows.InstructionStepLemmas
import Spikes.Spike3SortLines.Windows.InterceptLemmas
import Spikes.Spike3SortLines.Windows.LinkCertificate

/-! # Named states for the finite Win32 preparation-abort prefix

This is deliberately just the concrete state spine.  IAT provenance, host-transition facts and
runner certificates are in separate modules so Lean caches the expensive finite reductions once.
-/

namespace Spikes.Spike3SortLines.Windows

open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.Windows
open Spikes.Spike3SortLines

set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000

local instance spike3NoGrantRuntime : ExternalCallInterceptor X86_64 AnyEvent :=
  spike3WindowsRuntime AnyEvent noNativeArenaGrant

theorem spike3NoGrantRuntime_none_of_not_aligned {state : X86_64MachineState} {address : Gasm.Core.Address}
    (halign : (address % 8 != 0) = true) :
    (ExternalCallInterceptor.interceptCall (Event := AnyEvent) (Arch := X86_64) address state) = none := by
  change spike3WindowsCallIntercept noNativeArenaGrant address state = none
  unfold spike3WindowsCallIntercept
  rw [findIatIndex_none_of_not_aligned halign]
  unfold win32CallIntercept win32Intercept
  rw [findIatIndex_none_of_not_aligned halign]

def noGrantInitial (stdin : ByteArray) : X86_64MachineState :=
  (spike3ExecutableWithArena spike3NoGrantReservationBytes).loadWithStdin stdin
def noGrantAfterSub (stdin : ByteArray) := X86_64Instruction.step (sub_rsp 120) (noGrantInitial stdin)
def noGrantBeforeGetStdHandle (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r32 .ecx 0xFFFFFFF6) (noGrantAfterSub stdin)
def noGrantAtGetStdHandle (stdin : ByteArray) :=
  X86_64Instruction.step (call_rip 8177) (noGrantBeforeGetStdHandle stdin)
def noGrantAfterGetStdHandle (stdin : ByteArray) :=
  (getStdHandleHook (Event := AnyEvent) (noGrantAtGetStdHandle stdin)).1
def noGrantAfterStdinSave (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r64 .r12 .rax) (noGrantAfterGetStdHandle stdin)
def noGrantAfterNullAddress (stdin : ByteArray) :=
  X86_64Instruction.step (xor_r32 .ecx .ecx) (noGrantAfterStdinSave stdin)
def noGrantAfterRequestedBytes (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r32 .edx spike3NoGrantReservationBytes)
    (noGrantAfterNullAddress stdin)
def noGrantAfterAllocationType (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r32 .r8d 0x3000) (noGrantAfterRequestedBytes stdin)
def noGrantBeforeVirtualAlloc (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r32 .r9d 0x04) (noGrantAfterAllocationType stdin)
def noGrantAtVirtualAlloc (stdin : ByteArray) :=
  X86_64Instruction.step (call_rip 8181) (noGrantBeforeVirtualAlloc stdin)
def noGrantAfterVirtualAlloc (stdin : ByteArray) :=
  (spike3VirtualAllocHook (Event := AnyEvent) noNativeArenaGrant (noGrantAtVirtualAlloc stdin)).1
def noGrantAfterNullCheck (stdin : ByteArray) :=
  X86_64Instruction.step (cmp_r64_imm8 .rax 0) (noGrantAfterVirtualAlloc stdin)
def noGrantAtResourceExit (stdin : ByteArray) :=
  X86_64Instruction.step (je_rel32 1314) (noGrantAfterNullCheck stdin)
def noGrantBeforeExitProcess (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r32 .ecx spike3ResourceFailureExitCode) (noGrantAtResourceExit stdin)
def noGrantAtExitProcess (stdin : ByteArray) :=
  X86_64Instruction.step (call_rip 6838) (noGrantBeforeExitProcess stdin)
def noGrantAfterExitProcess (stdin : ByteArray) :=
  (spike3ExitProcessHook (Event := AnyEvent) (noGrantAtExitProcess stdin)).1

theorem sequentialMov32 (dst : Reg32) (value : UInt32) : SequentialInstruction (mov_r32 dst value) :=
  mov_r32_sequential dst value

theorem sequentialMov64 (dst src : Reg64) : SequentialInstruction (mov_r64 dst src) where
  encoding := .mov dst src
  safeFallthrough := by intro _ _; rfl

theorem sequentialXor32 (dst src : Reg32) : SequentialInstruction (xor_r32 dst src) where
  encoding := .xor32 dst src
  safeFallthrough := by intro _ _; cases dst <;> cases src <;> rfl

theorem sequentialCmpImm8 (dst : Reg64) (value : UInt8) : SequentialInstruction (cmp_r64_imm8 dst value) where
  encoding := .compareImm8 dst value
  safeFallthrough := by intro _ _; rfl

theorem read64_write64_disjoint (readAddr writeAddr : UInt64) (value : UInt64)
    (memory : X86_64Memory)
    (h0 : readAddr.toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ readAddr.toNat)
    (h1 : (readAddr + 1).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 1).toNat)
    (h2 : (readAddr + 2).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 2).toNat)
    (h3 : (readAddr + 3).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 3).toNat)
    (h4 : (readAddr + 4).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 4).toNat)
    (h5 : (readAddr + 5).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 5).toNat)
    (h6 : (readAddr + 6).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 6).toNat)
    (h7 : (readAddr + 7).toNat < writeAddr.toNat ∨ writeAddr.toNat + 8 ≤ (readAddr + 7).toNat)
    (hno : writeAddr.toNat + 8 ≤ 2 ^ 64) :
    X86_64Mem.read .w64 readAddr (X86_64Mem.write .w64 writeAddr value memory) =
      X86_64Mem.read .w64 readAddr memory := by
  unfold X86_64Mem.read
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory readAddr hno h0]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 1) hno h1]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 2) hno h2]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 3) hno h3]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 4) hno h4]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 5) hno h5]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 6) hno h6]
  rw [X86_64Mem.readByte_write_disjoint .w64 writeAddr value memory (readAddr + 7) hno h7]

end Spikes.Spike3SortLines.Windows

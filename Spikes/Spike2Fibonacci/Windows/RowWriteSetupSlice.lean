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
-/import Spikes.Spike2Fibonacci.Windows.RowLineSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

set_option maxHeartbeats 5000000

structure Spike2WriteSetupResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (bytes : List UInt8) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713517
  rsp : final.rsp = spike2AfterPrologue.rsp
  writtenPointer : final.gprs .r9 = final.rsp + 40
  fault : final.fault = none
  writeFileIat : final.read64 5368721424 = 5368721424
  bufferArgument : final.gprs .rdx = final.rsp + 64
  lengthArgument : (final.gprs .r8).toNat = bytes.length
  buffer : BufHolds final.memory (final.rsp + 64) bytes
  bufferNoWrap : (final.rsp + 64).toNat + bytes.length < 2 ^ 64

opaque spike2_write_setup_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (bytes : List UInt8)
    (hrip : state.rip = 5368713489) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (cursor : state.gprs .rdi = state.rsp + 64 + UInt64.ofNat bytes.length)
    (cursorNat : (state.gprs .rdi).toNat = (state.rsp + 64).toNat + bytes.length)
    (buffer : BufHolds state.memory (state.rsp + 64) bytes) :
    Spike2WriteSetupResult state eventsRev bytes := by
  let final := spike2BeforeWriteFile state
  have frame := spike2_write_setup_registerFrame state
  have finalLow := spike2_write_setup_lowMemory state low rsp
  have finalMemory : final.memory = X86_64Mem.write .w64 (state.rsp + 32) 0 state.memory := by
    rfl
  have finalBuffer : BufHolds final.memory (final.rsp + 64) bytes := by
    rw [frame.rsp, finalMemory]
    apply BufHolds_of_getElem
    intro index within
    have observed := BufHolds_getElem state.memory (state.rsp + 64) bytes buffer index within
    let address := state.rsp + 64 + UInt64.ofNat index
    have addressNat : address.toNat = (state.rsp + 64).toNat + index := by
      dsimp [address]
      have upper := (state.gprs .rdi).toNat_lt_size
      change (state.gprs .rdi).toNat < 2 ^ 64 at upper
      rw [cursorNat] at upper
      have indexBound : index < 2 ^ 64 := by omega
      have sumBound : (state.rsp + 64).toNat + index < 2 ^ 64 := by omega
      rw [UInt64.toNat_add]
      have indexCast : (UInt64.ofNat index).toNat = index := by
        simp [Nat.toUInt64, Nat.mod_eq_of_lt indexBound]
      rw [indexCast, Nat.mod_eq_of_lt sumBound]
    have writeNoWrap : (state.rsp + 32).toNat + 8 ≤ 2 ^ 64 := by
      rw [rsp, spike2_after_prologue_rsp_eq]
      decide
    have outside : (state.rsp + 32).toNat + 8 ≤ address.toNat := by
      rw [addressNat, rsp, spike2_after_prologue_rsp_eq]
      simp [UInt64.toNat_add]
      omega
    have preserved := X86_64Mem.readByte_write_disjoint .w64 (state.rsp + 32) 0
      state.memory address writeNoWrap (Or.inr outside)
    change X86_64Mem.read .w8 address (X86_64Mem.write .w64 (state.rsp + 32) 0 state.memory) = _
    rw [show X86_64Mem.read .w8 address _ =
      (X86_64Mem.readByte (X86_64Mem.write .w64 (state.rsp + 32) 0 state.memory) address).toUInt64
        by rfl, preserved]
    simpa [address] using congrArg UInt8.toUInt64 observed
  exact {
    final := final
    certificate := spike2_write_setup_selected_prefix state eventsRev hrip safe
    registers := frame
    fibRegisters := by constructor <;> rfl
    lowMemory := finalLow
    rip := by
      change state.rip + 3 + 5 + 3 + 3 + 5 + 9 = 5368713517
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    writtenPointer := by rfl
    fault := frame.fault.trans safe
    writeFileIat := by
      rw [finalLow 5368721424 (by decide)]
      exact spike2_after_prologue_writeFileIat
    bufferArgument := by rfl
    lengthArgument := by
      have lengthBound : bytes.length < 2 ^ 64 := by
        have upper := (state.gprs .rdi).toNat_lt_size
        change (state.gprs .rdi).toNat < 2 ^ 64 at upper
        rw [cursorNat] at upper
        omega
      have exactValue : final.gprs .r8 = UInt64.ofNat bytes.length := by
        change state.gprs .rdi - (state.rsp + 64) = UInt64.ofNat bytes.length
        rw [cursor]
        bv_decide
      rw [exactValue]
      simp [Nat.toUInt64, Nat.mod_eq_of_lt lengthBound]
    buffer := finalBuffer
    bufferNoWrap := by
      rw [frame.rsp, ← cursorNat]
      exact (state.gprs .rdi).toNat_lt_size }

end Spikes.Spike2Fibonacci.Windows

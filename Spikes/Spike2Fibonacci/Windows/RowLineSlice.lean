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
-/import Spikes.Spike2Fibonacci.Windows.RowDecimalSlice

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowLineSlice :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2LineSliceResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (bytes : List UInt8)
    extends Spike2FramedSliceResult initial eventsRev 6 5368713489 where
  buffer : BufHolds final.memory (initial.rsp + 64) (bytes ++ [13, 10])
  cursor : final.gprs .rdi = initial.gprs .rdi + 2
  cursorNat : (final.gprs .rdi).toNat =
    (initial.rsp + 64).toNat + (bytes ++ [13, 10]).length

opaque spike2_line_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (bytes : List UInt8)
    (hrip : state.rip = 5368713457) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (cursorAbove : spike2RowLowMemoryTop ≤ (state.gprs .rdi).toNat)
    (cursorRoom : (state.gprs .rdi).toNat + 2 < 2 ^ 64)
    (cursor : state.gprs .rdi = state.rsp + 64 + UInt64.ofNat bytes.length)
    (cursorNat : (state.gprs .rdi).toNat = (state.rsp + 64).toNat + bytes.length)
    (buffer : BufHolds state.memory (state.rsp + 64) bytes) :
    Spike2LineSliceResult state eventsRev bytes := by
  let final := spike2AfterLineTerminator state
  have frame := spike2_line_terminator_registerFrame state
  let afterCr := X86_64Mem.write .w8 (state.gprs .rdi) 13 state.memory
  have cr : BufHolds afterCr (state.rsp + 64) (bytes ++ [13]) := by
    apply BufHolds_write8_append state.memory (state.rsp + 64) (state.gprs .rdi) 13 bytes
      buffer cursor
    have room := cursorRoom
    rw [cursorNat] at room
    omega
  have full : BufHolds
      (X86_64Mem.write .w8 (state.gprs .rdi + 1) 10 afterCr)
      (state.rsp + 64) (bytes ++ [13, 10]) := by
    have next : state.gprs .rdi + 1 =
        state.rsp + 64 + UInt64.ofNat (bytes ++ [13]).length := by
      rw [cursor]
      simp [Nat.toUInt64]
      ac_rfl
    have bound : (state.rsp + 64).toNat + (bytes ++ [13]).length < 2 ^ 64 := by
      rw [rsp, spike2_after_prologue_rsp_eq]
      simp [UInt64.toNat_add]
      have room := cursorRoom
      rw [cursorNat, rsp, spike2_after_prologue_rsp_eq] at room
      simp [UInt64.toNat_add] at room
      omega
    simpa [List.append_assoc] using
      BufHolds_write8_append afterCr (state.rsp + 64) (state.gprs .rdi + 1) 10
        (bytes ++ [13]) cr next bound
  exact {
    final := final
    certificate := spike2_line_terminator_selected_prefix state eventsRev hrip safe
    registers := frame
    fibRegisters := by constructor <;> rfl
    rip := by
      change state.rip + 10 + 2 + 4 + 10 + 2 + 4 = 5368713489
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := spike2_line_terminator_lowMemory state low cursorAbove (by omega)
    buffer := by
      change BufHolds (X86_64Mem.write .w8 (state.gprs .rdi + 1) 10 afterCr)
        (state.rsp + 64) (bytes ++ [13, 10])
      exact full
    cursor := by
      change state.gprs .rdi + 1 + 1 = state.gprs .rdi + 2
      simp [UInt64.add_assoc]
    cursorNat := by
      change (state.gprs .rdi + 1 + 1).toNat =
        (state.rsp + 64).toNat + (bytes ++ [13, 10]).length
      have firstBound : (state.gprs .rdi).toNat + 1 < 2 ^ 64 := by omega
      have secondBound : (state.gprs .rdi).toNat + 2 < 2 ^ 64 := by omega
      have firstNat : (state.gprs .rdi + 1).toNat =
          (state.gprs .rdi).toNat + 1 := by
        rw [UInt64.toNat_add]
        simp [Nat.mod_eq_of_lt firstBound]
      have secondNat : (state.gprs .rdi + 1 + 1).toNat =
          (state.gprs .rdi).toNat + 2 := by
        rw [UInt64.toNat_add, firstNat]
        simp [Nat.mod_eq_of_lt secondBound]
      rw [secondNat, cursorNat]
      simp
      omega }

end Spikes.Spike2Fibonacci.Windows

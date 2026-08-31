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
-/import Spikes.Spike2Fibonacci.Windows.RowOpening
import Spikes.Spike2Fibonacci.Windows.RowRegisterCursor

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowIndexOnePath :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

def spike2IndexPrefixBytes (completed : Nat) : List UInt8 :=
  [0x46, 0x69, 0x62, 0x28] ++ Stdlib.Fmt.formatDecimal (completed + 1) ++
    [0x29, 0x20, 0x3d, 0x20]

structure Spike2CursorSliceResult (completed : Nat) (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (maxFuel : Nat) where
  fuel : Nat
  final : X86_64MachineState
  fuelBound : fuel ≤ maxFuel
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713409
  cursorAboveStack : final.rsp.toNat ≤ (final.gprs .rdi).toNat
  cursorAbove : spike2RowLowMemoryTop ≤ (final.gprs .rdi).toNat
  cursorRoom : (final.gprs .rdi).toNat + 22 < 2 ^ 64
  cursor : final.gprs .rdi =
    initial.rsp + 64 + UInt64.ofNat (spike2IndexPrefixBytes completed).length
  cursorNat : (final.gprs .rdi).toNat =
    (initial.rsp + 64).toNat + (spike2IndexPrefixBytes completed).length
  buffer : BufHolds final.memory (initial.rsp + 64) (spike2IndexPrefixBytes completed)

theorem spike2_one_digit_index_buffer (completed : Nat) (state : X86_64MachineState)
    (within : completed < 9)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1))
    (rsp : state.rsp = spike2AfterPrologue.rsp)
    (holds : BufHolds state.memory (state.rsp + 64) [0x46, 0x69, 0x62, 0x28]) :
    BufHolds (spike2AfterOneDigitIndex state).memory (state.rsp + 64)
      ([0x46, 0x69, 0x62, 0x28] ++ Stdlib.Fmt.formatDecimal (completed + 1) ++
        [0x29, 0x20, 0x3d, 0x20]) := by
  have finalMemory : (spike2AfterOneDigitIndex state).memory =
      X86_64Mem.write .w8 (state.rsp + 72) 0x20
        (X86_64Mem.write .w8 (state.rsp + 71) 0x3d
          (X86_64Mem.write .w8 (state.rsp + 70) 0x20
            (X86_64Mem.write .w8 (state.rsp + 69) 0x29
              (X86_64Mem.write .w8 (state.rsp + 68)
                (state.gprs .r13 + 0x30).toUInt8.toUInt64 state.memory)))) := by rfl
  have formatted : Stdlib.Fmt.formatDecimal (completed + 1) =
      [Stdlib.Fmt.byteOfDigit (completed + 1)] := by
    unfold Stdlib.Fmt.formatDecimal
    rw [Stdlib.Fmt.digits_single _ (by omega)]
    rfl
  have digit := digit_byte_toUInt64 (completed + 1) (by omega)
  have digit8 : ((UInt64.ofNat (completed + 1) + 0x30).toUInt8).toUInt64 =
      (Stdlib.Fmt.byteOfDigit (completed + 1)).toUInt64 := by
    have := congrArg (fun value : UInt64 => value.toUInt8.toUInt64) digit
    simpa using this
  rw [finalMemory, counter, digit8, formatted]
  let start := state.rsp + 64
  have noWrap (n : Nat) (bound : n ≤ 9) : start.toNat + n < 2 ^ 64 := by
    dsimp [start]
    rw [rsp, spike2_after_prologue_rsp_eq, UInt64.toNat_add]
    simp
    omega
  let m1 := X86_64Mem.write .w8 (state.rsp + 68)
    (Stdlib.Fmt.byteOfDigit (completed + 1)).toUInt64 state.memory
  let m2 := X86_64Mem.write .w8 (state.rsp + 69) (0x29 : UInt8).toUInt64 m1
  let m3 := X86_64Mem.write .w8 (state.rsp + 70) (0x20 : UInt8).toUInt64 m2
  let m4 := X86_64Mem.write .w8 (state.rsp + 71) (0x3d : UInt8).toUInt64 m3
  have h1 : BufHolds m1 start
      ([0x46, 0x69, 0x62, 0x28] ++ [Stdlib.Fmt.byteOfDigit (completed + 1)]) := by
    apply BufHolds_write8_append _ _ _ _ _ holds
    · dsimp [start]; simp [Nat.toUInt64]; bv_decide
    · exact noWrap 4 (by decide)
  have h2 : BufHolds m2 start
      ([0x46, 0x69, 0x62, 0x28] ++ [Stdlib.Fmt.byteOfDigit (completed + 1)] ++ [0x29]) := by
    apply BufHolds_write8_append m1 start (state.rsp + 69) (0x29 : UInt8) _ h1
    · dsimp [start]; simp [Nat.toUInt64]; bv_decide
    · simpa using noWrap 5 (by decide)
  have h3 : BufHolds m3 start
      ([0x46, 0x69, 0x62, 0x28] ++ [Stdlib.Fmt.byteOfDigit (completed + 1)] ++
        [0x29] ++ [0x20]) := by
    apply BufHolds_write8_append m2 start (state.rsp + 70) (0x20 : UInt8) _ h2
    · dsimp [start]; simp [Nat.toUInt64]; bv_decide
    · simpa using noWrap 6 (by decide)
  have h4 : BufHolds m4 start
      ([0x46, 0x69, 0x62, 0x28] ++ [Stdlib.Fmt.byteOfDigit (completed + 1)] ++
        [0x29] ++ [0x20] ++ [0x3d]) := by
    apply BufHolds_write8_append m3 start (state.rsp + 71) (0x3d : UInt8) _ h3
    · dsimp [start]; simp [Nat.toUInt64]; bv_decide
    · simpa using noWrap 7 (by decide)
  have h5 := BufHolds_write8_append m4 start (state.rsp + 72) (0x20 : UInt8)
    ([0x46, 0x69, 0x62, 0x28] ++ [Stdlib.Fmt.byteOfDigit (completed + 1)] ++
      [0x29] ++ [0x20] ++ [0x3d]) h4 (by dsimp [start]; simp [Nat.toUInt64]; bv_decide)
      (by simpa using noWrap 8 (by decide))
  simpa [start, m1, m2, m3, m4, List.append_assoc] using h5

opaque spike2_one_digit_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (within : completed < 9)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1))
    (hrip : state.rip = 5368713297) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (holds : BufHolds state.memory (state.rsp + 64) [0x46, 0x69, 0x62, 0x28]) :
    Spike2CursorSliceResult completed state eventsRev 12 := by
  let header := spike2AfterIndexHeader state
  have oneDigit := spike2_index_counter_one_digit state completed within counter
  have placedEntry : state.rip = spike2IndexHeaderPlacement.entryRip := by
    simpa [spike2IndexHeaderPlacement] using hrip
  have headerRip : header.rip = 5368713303 := by
    simpa [header, Spike2IndexHeaderPlacement.destinationRip, spike2IndexHeaderPlacement] using
      spike2IndexHeaderPlacement.oneDigitDestination state placedEntry oneDigit
  have boundary := spike2_selected_silent_unaligned header 5368713303 headerRip
    (by decide) (by decide)
  have headerSelected : selectedNonInputPlatformCall header.rip header = true := by
    rw [headerRip]
    exact boundary.1
  have headerSilent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      header.rip header = none := by
    rw [headerRip]
    exact boundary.2
  have headerStep := spike2_index_header_selected spike2IndexHeaderPlacement .oneDigit state
    eventsRev placedEntry oneDigit (by simpa [header] using headerSelected)
      (by simpa [header] using headerSilent) safe
  have headerPrefix := headerStep.certificate
  have headerFrame := spike2_index_header_registerFrame state
  have headerRsp := headerFrame.rsp.trans rsp
  have headerSafe := headerFrame.fault.trans safe
  have headerLow : Spike2RowLowMemory header := low.of_memory_eq (by rfl)
  have indexPrefix := spike2_one_digit_index_selected_prefix header eventsRev headerRip headerSafe
  have indexFrame := spike2_one_digit_registerFrame header
  have indexLow := spike2_one_digit_index_lowMemory header headerLow headerRsp
  have bounds := spike2_one_digit_cursor_bounds header headerRsp
  exact {
    fuel := 12
    final := spike2AfterOneDigitIndex header
    fuelBound := by decide
    certificate := headerPrefix.append indexPrefix
    registers := headerFrame.trans indexFrame
    fibRegisters := by constructor <;> rfl
    lowMemory := indexLow
    rip := by
      unfold spike2AfterOneDigitIndex
      change header.rip + 3 + 4 + 5 + 2 + 5 + 5 + 5 + 5 + 5 + 2 +
        signExtend8To64 65 = 5368713409
      rw [headerRip]
      rfl
    cursorAboveStack := by
      rw [indexFrame.rsp, spike2_one_digit_cursor, headerRsp,
        spike2_after_prologue_rsp_eq]
      decide
    cursorAbove := bounds.1
    cursorRoom := bounds.2
    cursor := by
      rw [spike2_one_digit_cursor, headerFrame.rsp]
      simp [spike2IndexPrefixBytes, Stdlib.Fmt.formatDecimal,
        Stdlib.Fmt.digits_single (completed + 1) (by omega), Nat.toUInt64]
      bv_decide
    cursorNat := by
      rw [spike2_one_digit_cursor, headerFrame.rsp, rsp, spike2_after_prologue_rsp_eq]
      simp [spike2IndexPrefixBytes, Stdlib.Fmt.formatDecimal,
        Stdlib.Fmt.digits_single (completed + 1) (by omega), UInt64.toNat_add]
    buffer := spike2_one_digit_index_buffer completed header within
      (headerFrame.r13.trans counter) headerRsp (by
        rw [show header.memory = state.memory by rfl, headerFrame.rsp]
        exact holds) }

end Spikes.Spike2Fibonacci.Windows

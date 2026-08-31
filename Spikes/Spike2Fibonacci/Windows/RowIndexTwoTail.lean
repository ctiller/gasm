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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexTwoHead

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowIndexTwoTail :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

theorem spike2_two_digit_tail_buffer (completed : Nat) (state : X86_64MachineState)
    (lower : 9 ≤ completed) (upper : completed < 90)
    (rsp : state.rsp = spike2AfterPrologue.rsp)
    (holds : BufHolds state.memory (state.rsp + 64)
      ([0x46, 0x69, 0x62, 0x28] ++ Stdlib.Fmt.formatDecimal (completed + 1))) :
    BufHolds (spike2AfterTwoDigitIndex state).memory (state.rsp + 64)
      (spike2IndexPrefixBytes completed) := by
  have finalMemory : (spike2AfterTwoDigitIndex state).memory =
      X86_64Mem.write .w8 (state.rsp + 73) 0x20
        (X86_64Mem.write .w8 (state.rsp + 72) 0x3d
          (X86_64Mem.write .w8 (state.rsp + 71) 0x20
            (X86_64Mem.write .w8 (state.rsp + 70) 0x29 state.memory))) := by rfl
  rw [finalMemory]
  let start := state.rsp + 64
  let prefixBytes := [0x46, 0x69, 0x62, 0x28] ++ Stdlib.Fmt.formatDecimal (completed + 1)
  have prefixLength : prefixBytes.length = 6 := by
    simp [prefixBytes, formatDecimal_two_digits (completed + 1) (by omega) (by omega)]
  have holdsPrefix : BufHolds state.memory start prefixBytes := by
    exact holds
  have noWrap (n : Nat) (bound : n ≤ 10) : start.toNat + n < 2 ^ 64 := by
    dsimp [start]
    rw [rsp, spike2_after_prologue_rsp_eq, UInt64.toNat_add]
    simp
    omega
  let m1 := X86_64Mem.write .w8 (state.rsp + 70) (0x29 : UInt8).toUInt64 state.memory
  let m2 := X86_64Mem.write .w8 (state.rsp + 71) (0x20 : UInt8).toUInt64 m1
  let m3 := X86_64Mem.write .w8 (state.rsp + 72) (0x3d : UInt8).toUInt64 m2
  have h1 : BufHolds m1 start (prefixBytes ++ [0x29]) := by
    apply BufHolds_write8_append _ _ _ _ _ holdsPrefix
    · dsimp [start, prefixBytes]
      rw [formatDecimal_two_digits (completed + 1) (by omega) (by omega)]
      simp [Nat.toUInt64]
      bv_decide
    · simpa [prefixLength] using noWrap 6 (by decide)
  have h2 : BufHolds m2 start (prefixBytes ++ [0x29] ++ [0x20]) := by
    apply BufHolds_write8_append _ _ _ _ _ h1
    · dsimp [start, prefixBytes]
      rw [formatDecimal_two_digits (completed + 1) (by omega) (by omega)]
      simp [Nat.toUInt64]
      bv_decide
    · simpa [prefixLength] using noWrap 7 (by decide)
  have h3 : BufHolds m3 start (prefixBytes ++ [0x29] ++ [0x20] ++ [0x3d]) := by
    apply BufHolds_write8_append _ _ _ _ _ h2
    · dsimp [start, prefixBytes]
      rw [formatDecimal_two_digits (completed + 1) (by omega) (by omega)]
      simp [Nat.toUInt64]
      bv_decide
    · simpa [prefixLength] using noWrap 8 (by decide)
  have h4 := BufHolds_write8_append m3 start (state.rsp + 73) (0x20 : UInt8)
    (prefixBytes ++ [0x29] ++ [0x20] ++ [0x3d]) h3
    (by
      dsimp [start, prefixBytes]
      rw [formatDecimal_two_digits (completed + 1) (by omega) (by omega)]
      simp [Nat.toUInt64]
      bv_decide)
    (by simpa [prefixLength] using noWrap 9 (by decide))
  simpa [spike2IndexPrefixBytes, start, prefixBytes, m1, m2, m3, List.append_assoc] using h4

opaque spike2_two_digit_tail_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713384)
    (lower : 9 ≤ completed) (upper : completed < 90)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state)
    (holds : BufHolds state.memory (state.rsp + 64)
      ([0x46, 0x69, 0x62, 0x28] ++ Stdlib.Fmt.formatDecimal (completed + 1))) :
    Spike2CursorSliceResult completed state eventsRev 5 := by
  have tailPrefix := spike2_two_digit_tail_selected_prefix state eventsRev hrip safe
  have tailFrame := spike2_two_digit_tail_registerFrame state
  have tailLow := spike2_two_digit_tail_lowMemory state low rsp
  have bounds := spike2_two_digit_cursor_bounds state rsp
  exact {
    fuel := 5
    final := spike2AfterTwoDigitIndex state
    fuelBound := by decide
    certificate := tailPrefix
    registers := tailFrame
    fibRegisters := by constructor <;> rfl
    lowMemory := tailLow
    rip := by
      unfold spike2AfterTwoDigitIndex
      change state.rip + 5 + 5 + 5 + 5 + 5 = 5368713409
      rw [hrip]
      rfl
    cursorAboveStack := by
      rw [tailFrame.rsp, spike2_two_digit_cursor, rsp, spike2_after_prologue_rsp_eq]
      decide
    cursorAbove := bounds.1
    cursorRoom := bounds.2
    cursor := by
      rw [spike2_two_digit_cursor]
      simp [spike2IndexPrefixBytes,
        formatDecimal_two_digits (completed + 1) (by omega) (by omega), Nat.toUInt64]
      bv_decide
    cursorNat := by
      rw [spike2_two_digit_cursor, rsp, spike2_after_prologue_rsp_eq]
      simp [spike2IndexPrefixBytes,
        formatDecimal_two_digits (completed + 1) (by omega) (by omega), UInt64.toNat_add]
    buffer := spike2_two_digit_tail_buffer completed state lower upper rsp holds }

end Spikes.Spike2Fibonacci.Windows

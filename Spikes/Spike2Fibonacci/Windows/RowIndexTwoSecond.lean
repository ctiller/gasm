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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexTwoTens

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64
open Stdlib.Fmt

theorem spike2_two_digit_head_buffer (completed : Nat) (state : X86_64MachineState)
    (lower : 9 ≤ completed) (upper : completed < 90)
    (rsp : state.rsp = spike2AfterPrologue.rsp)
    (quotient : state.gprs .rax = UInt64.ofNat ((completed + 1) / 10))
    (remainder : state.gprs .rdx = UInt64.ofNat ((completed + 1) % 10))
    (holds : BufHolds state.memory (state.rsp + 64) [0x46, 0x69, 0x62, 0x28]) :
    BufHolds (spike2AfterTwoDigitHead (spike2AfterTwoDigitTens state)).memory
      (state.rsp + 64)
      ([0x46, 0x69, 0x62, 0x28] ++ formatDecimal (completed + 1)) := by
  have finalMemory :
      (spike2AfterTwoDigitHead (spike2AfterTwoDigitTens state)).memory =
        X86_64Mem.write .w8 (state.rsp + 69)
          (state.gprs .rdx + 0x30).toUInt8.toUInt64
          (X86_64Mem.write .w8 (state.rsp + 68)
            (state.gprs .rax + 0x30).toUInt8.toUInt64 state.memory) := by rfl
  have formatted := formatDecimal_two_digits (completed + 1) (by omega) (by omega)
  have qsmall : (completed + 1) / 10 < 10 := by omega
  have rsmall : (completed + 1) % 10 < 10 := Nat.mod_lt _ (by omega)
  have qdigit := digit_byte_toUInt64 ((completed + 1) / 10) qsmall
  have rdigit := digit_byte_toUInt64 ((completed + 1) % 10) rsmall
  have qdigit8 :
      (UInt64.ofNat ((completed + 1) / 10) + 0x30).toUInt8.toUInt64 =
        (byteOfDigit ((completed + 1) / 10)).toUInt64 := by
    simpa using congrArg (fun value : UInt64 => value.toUInt8.toUInt64) qdigit
  have rdigit8 :
      (UInt64.ofNat ((completed + 1) % 10) + 0x30).toUInt8.toUInt64 =
        (byteOfDigit ((completed + 1) % 10)).toUInt64 := by
    simpa using congrArg (fun value : UInt64 => value.toUInt8.toUInt64) rdigit
  rw [finalMemory, quotient, remainder, qdigit8, rdigit8, formatted]
  let start := state.rsp + 64
  have noWrap (n : Nat) (bound : n ≤ 6) : start.toNat + n < 2 ^ 64 := by
    dsimp [start]
    rw [rsp, spike2_after_prologue_rsp_eq, UInt64.toNat_add]
    simp
    omega
  let m1 := X86_64Mem.write .w8 (state.rsp + 68)
    (byteOfDigit ((completed + 1) / 10)).toUInt64 state.memory
  have h1 : BufHolds m1 start
      ([0x46, 0x69, 0x62, 0x28] ++ [byteOfDigit ((completed + 1) / 10)]) := by
    apply BufHolds_write8_append _ _ _ _ _ holds
    · dsimp [start]; simp [Nat.toUInt64]; bv_decide
    · exact noWrap 4 (by decide)
  have h2 := BufHolds_write8_append m1 start (state.rsp + 69)
    (byteOfDigit ((completed + 1) % 10))
    ([0x46, 0x69, 0x62, 0x28] ++ [byteOfDigit ((completed + 1) / 10)]) h1
    (by dsimp [start]; simp [Nat.toUInt64]; bv_decide)
    (by simpa using noWrap 5 (by decide))
  simpa [start, m1, List.append_assoc] using h2

structure Spike2TwoDigitSecondResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent)
    extends Spike2FramedSliceResult initial eventsRev 2 5368713384 where
  realizes : final = spike2AfterTwoDigitHead initial

opaque spike2_two_digit_second_slice (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713377)
    (rsp : state.rsp = spike2AfterPrologue.rsp) (safe : state.fault = none)
    (low : Spike2RowLowMemory state) :
    Spike2TwoDigitSecondResult state eventsRev := by
  let final := spike2AfterTwoDigitHead state
  have frame := spike2_two_digit_head_registerFrame state
  have finalRip : final.rip = 5368713384 := by
    change state.rip + 5 + 2 = 5368713384
    rw [hrip]
    rfl
  have finalLow := spike2_two_digit_head_lowMemory state low rsp
  have text : final.read64 5368713384 ≠ 5368713384 := by
    rw [finalLow 5368713384 (by decide)]
    exact spike2_initial_text_3384_not_selfref
  have boundary := spike2_selected_silent_nonIat final 5368713384 finalRip (by decide) text
  exact {
    final := final
    certificate := spike2_two_digit_head_selected_prefix state eventsRev hrip safe
      (by rw [finalRip]; exact boundary.1) (by rw [finalRip]; exact boundary.2)
    registers := frame
    fibRegisters := by constructor <;> rfl
    rip := finalRip
    rsp := frame.rsp.trans rsp
    fault := frame.fault.trans safe
    lowMemory := finalLow
    realizes := rfl }

end Spikes.Spike2Fibonacci.Windows

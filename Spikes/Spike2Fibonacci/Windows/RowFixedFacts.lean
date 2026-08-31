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
-/import Spikes.Spike2Fibonacci.Windows.RowRegisterFrame
import Spikes.Spike2Fibonacci.Windows.FormatterTextInit

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64
open Stdlib.Fmt

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The linked WriteFile slot retained by the row low-memory invariant. -/
theorem spike2_after_prologue_writeFileIat :
    spike2AfterPrologue.read64 5368721424 = 5368721424 := by
  decide

/-- The linked ExitProcess slot retained by the row low-memory invariant. -/
theorem spike2_after_prologue_exitProcessIat :
    spike2AfterPrologue.read64 5368721432 = 5368721432 := by
  decide

/-- The terminal branch landing is ordinary linked text rather than an IAT self-reference. -/
theorem spike2_initial_text_3544_not_selfref :
    spike2AfterPrologue.read64 5368713544 ≠ 5368713544 := by
  decide

theorem spike2_after_prologue_r13 : spike2AfterPrologue.gprs .r13 = 1 := by
  rfl

theorem spike2_after_prologue_r14 : spike2AfterPrologue.gprs .r14 = 1 := by
  rfl

theorem spike2_after_prologue_r15 : spike2AfterPrologue.gprs .r15 = 1 := by
  rfl

theorem spike2_after_prologue_fault : spike2AfterPrologue.fault = none := by
  rfl

/-- The one-digit formatter leaves enough high-stack output room for every UInt64 value. -/
theorem spike2_one_digit_cursor_bounds (state : X86_64MachineState)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    spike2RowLowMemoryTop ≤ ((spike2AfterOneDigitIndex state).gprs .rdi).toNat ∧
      ((spike2AfterOneDigitIndex state).gprs .rdi).toNat + 22 < 2 ^ 64 := by
  have cursor : (spike2AfterOneDigitIndex state).gprs .rdi = state.rsp + 73 := by
    rfl
  rw [cursor, rsp, spike2_after_prologue_rsp_eq]
  decide

/-- The two-digit formatter leaves enough high-stack output room for every UInt64 value. -/
theorem spike2_two_digit_cursor_bounds (state : X86_64MachineState)
    (rsp : state.rsp = spike2AfterPrologue.rsp) :
    spike2RowLowMemoryTop ≤ ((spike2AfterTwoDigitIndex state).gprs .rdi).toNat ∧
      ((spike2AfterTwoDigitIndex state).gprs .rdi).toNat + 22 < 2 ^ 64 := by
  have cursor : (spike2AfterTwoDigitIndex state).gprs .rdi = state.rsp + 74 := by
    rfl
  rw [cursor, rsp, spike2_after_prologue_rsp_eq]
  decide

/-- Numeric stack arena bounds shared by every decimal value. -/
theorem spike2_decimal_stack_bounds (value : UInt64) :
    5368721440 + 8 * decimalDigitCount value ≤ spike2AfterPrologue.rsp.toNat ∧
      spike2AfterPrologue.rsp.toNat < 18446744073709551608 := by
  have digits := decimalDigitCount_le_twenty value
  have rspNat : spike2AfterPrologue.rsp.toNat = 140737488289664 := by
    rw [spike2_after_prologue_rsp_eq]
    decide
  rw [rspNat]
  constructor <;> omega

end Spikes.Spike2Fibonacci.Windows

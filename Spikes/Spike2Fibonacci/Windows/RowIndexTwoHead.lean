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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexTwoSecond

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowIndexTwoHead :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2TwoDigitHeadResult (completed : Nat) (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 12
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  rip : final.rip = 5368713384
  rsp : final.rsp = spike2AfterPrologue.rsp
  fault : final.fault = none
  lowMemory : Spike2RowLowMemory final
  buffer : BufHolds final.memory (initial.rsp + 64)
    ([0x46, 0x69, 0x62, 0x28] ++ Stdlib.Fmt.formatDecimal (completed + 1))

opaque spike2_two_digit_head_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (lower : 9 ≤ completed) (upper : completed < 90)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1))
    (hrip : state.rip = 5368713297) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (holds : BufHolds state.memory (state.rsp + 64) [0x46, 0x69, 0x62, 0x28]) :
    Spike2TwoDigitHeadResult completed state eventsRev := by
  let branch := spike2_two_digit_branch_slice completed state eventsRev lower upper counter
    hrip rsp safe low
  let division := spike2_two_digit_division_slice branch.final eventsRev branch.rip branch.rsp
    branch.fault branch.lowMemory
  let tens := spike2_two_digit_tens_slice division.final eventsRev division.rip division.rsp
    division.fault division.lowMemory
  let second := spike2_two_digit_second_slice tens.final eventsRev tens.rip tens.rsp tens.fault
    tens.lowMemory
  have divisionHolds : BufHolds division.final.memory (division.final.rsp + 64)
      [0x46, 0x69, 0x62, 0x28] := by
    rw [division.memory, branch.memory, division.registers.rsp, branch.registers.rsp]
    exact holds
  have quotient : division.final.gprs .rax = UInt64.ofNat ((completed + 1) / 10) := by
    rw [division.quotient, branch.registers.r13, counter]
    simp [Nat.toUInt64, Nat.mod_eq_of_lt (by omega : completed + 1 < 2 ^ 64)]
  have remainder : division.final.gprs .rdx = UInt64.ofNat ((completed + 1) % 10) := by
    rw [division.remainder, branch.registers.r13, counter]
    simp [Nat.toUInt64, Nat.mod_eq_of_lt (by omega : completed + 1 < 2 ^ 64)]
  have formatted := spike2_two_digit_head_buffer completed division.final lower upper
    division.rsp quotient remainder divisionHolds
  exact {
    final := second.final
    certificate := by
      simpa using ((branch.certificate.append division.certificate).append
        tens.certificate).append second.certificate
    registers := ((branch.registers.trans division.registers).trans
      tens.registers).trans second.registers
    fibRegisters := ((branch.fibRegisters.trans division.fibRegisters).trans
      tens.fibRegisters).trans second.fibRegisters
    rip := second.rip
    rsp := second.rsp
    fault := second.fault
    lowMemory := second.lowMemory
    buffer := by
      rw [second.realizes, tens.realizes]
      rw [division.registers.rsp, branch.registers.rsp] at formatted
      exact formatted }

end Spikes.Spike2Fibonacci.Windows

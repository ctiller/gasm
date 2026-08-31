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

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2TwoDigitHeadResult (initial : X86_64MachineState)
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

opaque spike2_two_digit_head_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (lower : 9 ≤ completed) (upper : completed < 90)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1))
    (hrip : state.rip = 5368713297) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    Spike2TwoDigitHeadResult state eventsRev := by
  let branch := spike2_two_digit_branch_slice completed state eventsRev lower upper counter
    hrip rsp safe low
  let division := spike2_two_digit_division_slice branch.final eventsRev branch.rip branch.rsp
    branch.fault branch.lowMemory
  let tens := spike2_two_digit_tens_slice division.final eventsRev division.rip division.rsp
    division.fault division.lowMemory
  let second := spike2_two_digit_second_slice tens.final eventsRev tens.rip tens.rsp tens.fault
    tens.lowMemory
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
    lowMemory := second.lowMemory }

end Spikes.Spike2Fibonacci.Windows

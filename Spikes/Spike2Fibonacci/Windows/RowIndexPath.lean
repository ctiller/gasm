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
-/import Spikes.Spike2Fibonacci.Windows.RowIndexTwoTail

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2IndexPathResult (completed : Nat) (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  fuel : Nat
  final : X86_64MachineState
  fuelBound : fuel ≤ 23
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713409
  cursorAboveStack : final.rsp.toNat ≤ (final.gprs .rdi).toNat
  cursorAbove : spike2RowLowMemoryTop ≤ (final.gprs .rdi).toNat
  cursorRoom : (final.gprs .rdi).toNat + 22 < 2 ^ 64

opaque spike2_index_path (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (within : completed < 90)
    (holds : Spike2RowInvariant completed state eventsRev) :
    Spike2IndexPathResult completed state eventsRev := by
  let opening := spike2_row_opening completed state eventsRev within holds
  by_cases one : completed < 9
  · let path := spike2_one_digit_slice completed opening.final eventsRev one
      (opening.registers.r13.trans holds.counter) opening.rip opening.rsp opening.fault
      opening.lowMemory
    exact {
      fuel := 6 + path.fuel
      final := path.final
      fuelBound := by have := path.fuelBound; omega
      certificate := by simpa using opening.certificate.append path.certificate
      registers := opening.registers.trans path.registers
      fibRegisters := opening.fibRegisters.trans path.fibRegisters
      lowMemory := path.lowMemory
      rip := path.rip
      cursorAboveStack := path.cursorAboveStack
      cursorAbove := path.cursorAbove
      cursorRoom := path.cursorRoom }
  · have lower : 9 ≤ completed := by omega
    let head := spike2_two_digit_head_slice completed opening.final eventsRev lower within
      (opening.registers.r13.trans holds.counter) opening.rip opening.rsp opening.fault
      opening.lowMemory
    let tail := spike2_two_digit_tail_slice head.final eventsRev head.rip head.rsp head.fault
      head.lowMemory
    exact {
      fuel := 6 + 12 + tail.fuel
      final := tail.final
      fuelBound := by have := tail.fuelBound; omega
      certificate := by
        simpa using (opening.certificate.append head.certificate).append tail.certificate
      registers := (opening.registers.trans head.registers).trans tail.registers
      fibRegisters := (opening.fibRegisters.trans head.fibRegisters).trans tail.fibRegisters
      lowMemory := tail.lowMemory
      rip := tail.rip
      cursorAboveStack := tail.cursorAboveStack
      cursorAbove := tail.cursorAbove
      cursorRoom := tail.cursorRoom }

end Spikes.Spike2Fibonacci.Windows

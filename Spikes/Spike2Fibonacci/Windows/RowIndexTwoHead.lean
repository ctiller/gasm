/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowIndexTwoSecond

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2TwoDigitHeadResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 12
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
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
    rip := second.rip
    rsp := second.rsp
    fault := second.fault
    lowMemory := second.lowMemory }

end Spikes.Spike2Fibonacci.Windows

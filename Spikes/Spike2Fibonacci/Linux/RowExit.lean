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
-/

import Gasm.Targets.X86_64.SelectedLoopTermination
import Spikes.Spike2Fibonacci.Linux.NativeAdapter

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64

/-- Minimal fixed-point boundary consumed after exactly ninety Linux Fibonacci rows.  The row
    producer remains responsible for establishing these projections; the exit adapter needs no
    whole-memory equality or closed evaluator result. -/
structure Spike2LinuxExitInvariant (state : X86_64MachineState)
    (_eventsRev : List AnyEvent) : Prop where
  rip : state.rip = spike2MainLoopRip
  counter : state.gprs .r13 = (91 : UInt64)
  fault : state.fault = none

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Typed terminal edge from the ninety-row Linux loop boundary.  Four ordinary selected steps
    reach the linked `SYSCALL`; the syscall itself is retained as a classified process-exit step. -/
def spike2_exit_tail : SelectedProcessExitTail selectedNonInputPlatformCall spike2Indexed
    Spike2LinuxExitInvariant where
  maxFuel := 4
  run state eventsRev holds := by
    have header := spike2_exit_header_selected_prefix state eventsRev
      holds.rip holds.counter holds.fault
    have exitRip := spike2_after_exit_header_rip state holds.rip holds.counter
    have setup := spike2_exit_setup_selected_prefix state eventsRev exitRip holds.fault
    exact ⟨{
      fuel := 4
      final := spike2BeforeExitSyscall state
      finalEventsRev := eventsRev
      emitted := []
      code := 0
      certificate := by simpa using header.append setup
      exitStep := spike2_exit_syscall_selected_step state exitRip holds.fault },
      Nat.le_refl 4⟩

/- REF: docs/MACRO_ASSEMBLER.md#eventful-production-segments -/
/-- Close any structural prefix which reaches the ninety-row boundary into the unchanged public
    50,000-step termination judgment.  This is the final composition seam: the remaining row proof
    need only produce the prefix and the three boundary projections above. -/
theorem spike2_selected_termination_of_prefix {fuel : Nat} {state : X86_64MachineState}
    {eventsRev emitted : List AnyEvent}
    (certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
      spike2Executable.load ([] : List AnyEvent) state eventsRev emitted)
    (holds : Spike2LinuxExitInvariant state eventsRev)
    (within : fuel + 5 ≤ 50000) :
    selectedExecutionTerminates (Event := AnyEvent) true selectedNonInputPlatformCall
      spike2Indexed 50000 spike2Executable.load = true := by
  rcases spike2_exit_tail.run state eventsRev holds with ⟨result, tailBound⟩
  have usedWithin : fuel + result.fuel + 1 ≤ 50000 := by
    have : result.fuel ≤ 4 := tailBound
    omega
  let slack := 50000 - (fuel + result.fuel + 1)
  have totalFuel : fuel + result.fuel + 1 + slack = 50000 := by
    dsimp [slack]
    omega
  rw [← totalFuel]
  exact (certificate.append result.certificate).selectedExecutionTerminates_of_processExit_with_slack
    result.exitStep slack

end Spikes.Spike2Fibonacci.Linux

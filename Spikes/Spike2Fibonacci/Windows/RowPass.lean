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
-/import Spikes.Spike2Fibonacci.Windows.RowRecurrenceSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

/-- One complete output row, from the typed loop-header fixed point back to itself. -/
theorem spike2_row_pass (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (within : completed < 90)
    (holds : Spike2RowInvariant completed state eventsRev) :
    ∃ fuel final finalEventsRev emitted,
      0 < fuel ∧ fuel ≤ 285 ∧
      ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
        state eventsRev final finalEventsRev emitted ∧
      Spike2RowInvariant (completed + 1) final finalEventsRev := by
  let index := spike2_index_path completed state eventsRev within holds
  rcases spike2_decimal_slice index.final eventsRev index.rip
      (index.registers.rsp.trans holds.rsp)
      (index.registers.fault.trans holds.fault) index.lowMemory
      index.cursorAboveStack index.cursorAbove index.cursorRoom with
    ⟨decimalFuel, decimalFinal, decimalEventsRev, decimalEmitted, decimalBound,
      decimalPrefix, decimalRegisters, decimalFibRegisters, decimalLow, decimalRip, decimalCursorAbove,
      decimalCursorRoom⟩
  let output := spike2_output_setup_slice decimalFinal decimalEventsRev decimalRip
    (decimalRegisters.rsp.trans (index.registers.rsp.trans holds.rsp))
    (decimalRegisters.fault.trans (index.registers.fault.trans holds.fault)) decimalLow
    decimalCursorAbove decimalCursorRoom
  let hook := spike2_write_hook_slice output.final decimalEventsRev output.rip output.rsp
    output.writtenPointer output.fault output.lowMemory output.writeFileIat
  rcases spike2_recurrence_slice hook.final hook.finalEventsRev hook.rip hook.rsp hook.fault
      hook.lowMemory with
    ⟨final, recurrencePrefix, finalLow, finalRip, finalRsp, finalCounter, finalFibA, finalFibB,
      finalFault⟩
  let fuel := index.fuel + decimalFuel + 12 + 1 + 6
  refine ⟨fuel, final, hook.finalEventsRev, decimalEmitted ++ hook.emitted,
    ?_, ?_, ?_, ?_⟩
  · dsimp [fuel]
    have indexBound := index.fuelBound
    omega
  · dsimp [fuel]
    have indexBound := index.fuelBound
    omega
  · have composed := ((((index.certificate.append decimalPrefix).append output.certificate).append
      hook.certificate).append recurrencePrefix)
    simpa [fuel, List.append_assoc] using composed
  · refine {
      rip := finalRip
      rsp := finalRsp
      counter := ?_
      fibA := ?_
      fibB := ?_
      fault := finalFault
      lowMemory := finalLow }
    calc
      final.gprs .r13 = hook.final.gprs .r13 + 1 := finalCounter
      _ = output.final.gprs .r13 + 1 := congrArg (fun counter => counter + 1)
        hook.registers.r13
      _ = decimalFinal.gprs .r13 + 1 := congrArg (fun counter => counter + 1)
        output.registers.r13
      _ = index.final.gprs .r13 + 1 := congrArg (fun counter => counter + 1)
        decimalRegisters.r13
      _ = state.gprs .r13 + 1 := congrArg (fun counter => counter + 1)
        index.registers.r13
      _ = UInt64.ofNat (completed + 1) + 1 := congrArg (fun counter => counter + 1)
        holds.counter
      _ = UInt64.ofNat ((completed + 1) + 1) := by
        exact (UInt64.ofNat_add (completed + 1) 1).symm
    · calc
        final.gprs .r14 = hook.final.gprs .r15 := finalFibA
        _ = output.final.gprs .r15 := hook.fibRegisters.r15
        _ = decimalFinal.gprs .r15 := output.fibRegisters.r15
        _ = index.final.gprs .r15 := decimalFibRegisters.r15
        _ = state.gprs .r15 := index.fibRegisters.r15
        _ = (fibNat (completed + 2)).toUInt64 := holds.fibB
        _ = (fibNat ((completed + 1) + 1)).toUInt64 := by congr 2 <;> omega
    · calc
        final.gprs .r15 = hook.final.gprs .r14 + hook.final.gprs .r15 := finalFibB
        _ = output.final.gprs .r14 + output.final.gprs .r15 := by
          rw [hook.fibRegisters.r14, hook.fibRegisters.r15]
        _ = decimalFinal.gprs .r14 + decimalFinal.gprs .r15 := by
          rw [output.fibRegisters.r14, output.fibRegisters.r15]
        _ = index.final.gprs .r14 + index.final.gprs .r15 := by
          rw [decimalFibRegisters.r14, decimalFibRegisters.r15]
        _ = state.gprs .r14 + state.gprs .r15 := by
          rw [index.fibRegisters.r14, index.fibRegisters.r15]
        _ = (fibNat (completed + 1)).toUInt64 +
            (fibNat (completed + 2)).toUInt64 := by rw [holds.fibA, holds.fibB]
        _ = (fibNat ((completed + 1) + 2)).toUInt64 := by
          rw [show fibNat ((completed + 1) + 2) =
            fibNat (completed + 1) + fibNat (completed + 2) from by
              rw [show fibNat ((completed + 1) + 2) =
                fibNat ((completed + 1) + 1) + fibNat (completed + 1) from rfl,
                Nat.add_comm]]
          exact (UInt64.ofNat_add _ _).symm

/-- Uniform bounded-fuel structural row step for the 90-row Windows loop. -/
def spike2_row_step : SelectedFuelBoundedInvariantLoopStep selectedNonInputPlatformCall
    spike2Indexed 90 Spike2RowInvariant where
  maxFuel := 285
  run := spike2_row_pass

end Spikes.Spike2Fibonacci.Windows

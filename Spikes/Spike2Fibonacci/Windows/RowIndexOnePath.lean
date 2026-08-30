/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowOpening

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

structure Spike2CursorSliceResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (maxFuel : Nat) where
  fuel : Nat
  final : X86_64MachineState
  fuelBound : fuel ≤ maxFuel
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed fuel
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  cursorAbove : spike2RowLowMemoryTop ≤ (final.gprs .rdi).toNat
  cursorRoom : (final.gprs .rdi).toNat + 22 < 2 ^ 64

private theorem index_one_rip (state : X86_64MachineState)
    (hrip : state.rip = 5368713297)
    (oneDigit : ¬ X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state)) :
    (spike2AfterIndexHeader state).rip = 5368713303 := by
  simp only [X86BranchCondition.holds] at oneDigit
  have hcond : ((spike2AfterIndexCompare state).sf ==
      (spike2AfterIndexCompare state).of_) = false :=
    decide_eq_false_iff_not.mpr oneDigit
  unfold spike2AfterIndexHeader
  rw [show X86_64Instruction.step (jge_rel8 41) (spike2AfterIndexCompare state) =
    { spike2AfterIndexCompare state with
      rip := if (spike2AfterIndexCompare state).sf == (spike2AfterIndexCompare state).of_ then
        (spike2AfterIndexCompare state).rip + 2 + signExtend8To64 41
        else (spike2AfterIndexCompare state).rip + 2 } by rfl]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]
  unfold spike2AfterIndexCompare
  change state.rip + 4 + 2 = 5368713303
  rw [hrip]
  rfl

opaque spike2_one_digit_slice (completed : Nat) (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (within : completed < 9)
    (counter : state.gprs .r13 = UInt64.ofNat (completed + 1))
    (hrip : state.rip = 5368713297) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    Spike2CursorSliceResult state eventsRev 12 := by
  let header := spike2AfterIndexHeader state
  have oneDigit := spike2_index_counter_one_digit state completed within counter
  have headerPrefix := spike2_index_header_one_digit_selected_prefix state eventsRev
    hrip oneDigit safe
  have headerRip : header.rip = 5368713303 := index_one_rip state hrip oneDigit
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
    lowMemory := indexLow
    cursorAbove := bounds.1
    cursorRoom := bounds.2 }

end Spikes.Spike2Fibonacci.Windows

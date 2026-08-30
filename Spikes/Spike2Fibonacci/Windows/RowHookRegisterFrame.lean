/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowFixedFacts

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets.Windows
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The CALL/WriteFile hook returns to the successor and preserves the loop driver frame. -/
theorem spike2_writeFile_call_pop_registerFrame (state : X86_64MachineState) :
    let final := popReturnAddress (spike2AfterWriteFileCall state)
    final.rip = state.rip + 6 ∧ final.rsp = state.rsp ∧
      final.gprs .r13 = state.gprs .r13 ∧ final.fault = state.fault := by
  have round := push64_pop64_roundtrip state (state.rip + 6)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (state.push64 (state.rip + 6)).pop64.1 = state.rip + 6
    exact round.1
  · change (state.push64 (state.rip + 6)).pop64.2.rsp = state.rsp
    exact round.2.1
  · change (state.push64 (state.rip + 6)).pop64.2.gprs .r13 = state.gprs .r13
    exact round.2.2 .r13 (by decide)
  · rfl

theorem spike2_writeFile_hook_registerFrame (state : X86_64MachineState) :
    let final := (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1
    final.rip = state.rip + 6 ∧ final.rsp = state.rsp ∧
      final.gprs .r13 = state.gprs .r13 ∧ final.fault = state.fault := by
  have returned := spike2_writeFile_call_pop_registerFrame state
  simpa [writeFileHook, X86_64MachineState.setGpr64, X86_64MachineState.rsp] using returned

/-- The indirect CALL reads the linked WriteFile slot retained by low memory. -/
theorem spike2_writeFile_call_target (state : X86_64MachineState)
    (hrip : state.rip = 5368713517)
    (iat : state.read64 5368721424 = 5368721424) :
    (spike2AfterWriteFileCall state).rip = 5368721424 := by
  unfold spike2AfterWriteFileCall
  change state.read64 (state.rip + 6 + signExtend32To64 0x1edd) = 5368721424
  rw [hrip]
  rw [show (5368713517 : UInt64) + 6 + signExtend32To64 0x1edd = 5368721424 by decide]
  exact iat

theorem spike2_writeFile_call_safe (state : X86_64MachineState)
    (safe : state.fault = none) :
    (spike2AfterWriteFileCall state).fault = none := by
  change state.fault = none
  exact safe

theorem spike2_writeFile_iat_index (state : X86_64MachineState)
    (target : state.rip = 5368721424)
    (selfref : state.read64 5368721424 = 5368721424) :
    Gasm.Targets.Windows.findIatIndex state state.rip = some 2 := by
  rw [target]
  simp [Gasm.Targets.Windows.findIatIndex, selfref]
  decide

end Spikes.Spike2Fibonacci.Windows

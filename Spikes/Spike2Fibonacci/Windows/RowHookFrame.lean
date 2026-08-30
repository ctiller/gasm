/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowCallPush

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- Row-facing memory projection of the Win32 hook; string/event construction is kept opaque. -/
theorem spike2_writeFileHook_memory (state : X86_64MachineState) :
    (writeFileHook (Event := AnyEvent) state).1.memory =
      if state.gprs .r9 == 0 then (popReturnAddress state).memory
      else X86_64Mem.write .w32 (state.gprs .r9)
        (state.gprs .r8).toNat.toUInt64 (popReturnAddress state).memory := by
  rfl

/-- A non-null `lpNumberOfBytesWritten` above the prefix makes the hook frame-preserving. -/
theorem spike2_writeFileHook_lowMemory (state : X86_64MachineState)
    (poppedLow : Spike2RowLowMemory (popReturnAddress state))
    (pointerNonzero : (state.gprs .r9 == 0) = false)
    (pointerNoWrap : (state.gprs .r9).toNat + 4 ≤ 2 ^ 64)
    (pointerAbove : spike2RowLowMemoryTop ≤ (state.gprs .r9).toNat) :
    Spike2RowLowMemory (writeFileHook (Event := AnyEvent) state).1 := by
  have written := poppedLow.write32Raw (state.gprs .r9)
    (state.gprs .r8).toNat.toUInt64 pointerNoWrap pointerAbove
  apply written.of_memory_eq
  rw [spike2_writeFileHook_memory, pointerNonzero]
  rfl

/-- Opaque composition of the CALL push/pop and the non-null Win32 result write. -/
theorem spike2_writeFile_call_hook_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (pushNoWrap : (state.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (pushAbove : spike2RowLowMemoryTop ≤ (state.rsp - 8).toNat)
    (pointerNonzero : (state.gprs .r9 == 0) = false)
    (pointerNoWrap : (state.gprs .r9).toNat + 4 ≤ 2 ^ 64)
    (pointerAbove : spike2RowLowMemoryTop ≤ (state.gprs .r9).toNat) :
    Spike2RowLowMemory
      (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1 := by
  let called := spike2AfterWriteFileCall state
  have poppedLow := spike2_call_pop_lowMemory state holds pushNoWrap pushAbove
  apply spike2_writeFileHook_lowMemory called poppedLow
  · rw [spike2_after_writeFile_call_r9]
    exact pointerNonzero
  · rw [spike2_after_writeFile_call_r9]
    exact pointerNoWrap
  · rw [spike2_after_writeFile_call_r9]
    exact pointerAbove

end Spikes.Spike2Fibonacci.Windows

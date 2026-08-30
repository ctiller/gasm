/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowFrame

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- Raw 32-bit memory updates preserve the immutable prefix when their write starts above it. -/
theorem Spike2RowLowMemory.write32Raw {state : X86_64MachineState}
    (holds : Spike2RowLowMemory state) (address value : UInt64)
    (noWrap : address.toNat + 4 ≤ 2 ^ 64)
    (above : spike2RowLowMemoryTop ≤ address.toNat) :
    Spike2RowLowMemory
      { state with memory := X86_64Mem.write .w32 address value state.memory } := by
  intro observed below
  change X86_64Mem.read .w64 observed
      (X86_64Mem.write .w32 address value state.memory) = _
  rw [X86_64Mem.read64_write_below .w32 state.memory address observed value
    noWrap (by omega)]
  exact holds observed below

/-- The indirect call's only memory effect is its return-address push. -/
theorem spike2_after_writeFile_call_memory (state : X86_64MachineState) :
    (spike2AfterWriteFileCall state).memory =
      (state.write64 (state.rsp - 8) (state.rip + 6)).memory := by
  rfl

theorem spike2_after_writeFile_call_r9 (state : X86_64MachineState) :
    (spike2AfterWriteFileCall state).gprs .r9 = state.gprs .r9 := by
  rfl

/-- Popping the return address changes registers and RIP, not memory. -/
theorem spike2_popReturnAddress_memory (state : X86_64MachineState) :
    (popReturnAddress state).memory = state.memory := by
  rfl

/-- CALL push followed by Win32 return-address pop preserves the prefix under stack bounds. -/
theorem spike2_call_pop_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (pushNoWrap : (state.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (pushAbove : spike2RowLowMemoryTop ≤ (state.rsp - 8).toNat) :
    Spike2RowLowMemory (popReturnAddress (spike2AfterWriteFileCall state)) := by
  have pushed := holds.write64 (state.rsp - 8) (state.rip + 6) pushNoWrap pushAbove
  have called : Spike2RowLowMemory (spike2AfterWriteFileCall state) :=
    pushed.of_memory_eq (spike2_after_writeFile_call_memory state)
  exact called.of_memory_eq
    (spike2_popReturnAddress_memory (spike2AfterWriteFileCall state))

end Spikes.Spike2Fibonacci.Windows

/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowHookRegisterFrame

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets.X86_64

/-- Fixed-point contract at the typed main-loop header. -/
structure Spike2RowInvariant (completed : Nat) (state : X86_64MachineState)
    (_eventsRev : List AnyEvent) : Prop where
  rip : state.rip = spike2WindowsMainLoopRip
  rsp : state.rsp = spike2AfterPrologue.rsp
  counter : state.gprs .r13 = UInt64.ofNat (completed + 1)
  fault : state.fault = none
  lowMemory : Spike2RowLowMemory state

theorem spike2_initial_row_invariant :
    Spike2RowInvariant 0 spike2AfterPrologue ([] : List AnyEvent) where
  rip := rfl
  rsp := rfl
  counter := spike2_after_prologue_r13
  fault := spike2_after_prologue_fault
  lowMemory := spike2_after_prologue_lowMemory

end Spikes.Spike2Fibonacci.Windows

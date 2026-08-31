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
-/import Spikes.Spike2Fibonacci.Windows.RowHookRegisterFrame

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets.X86_64

/-- Fixed-point contract at the typed main-loop header. -/
structure Spike2RowInvariant (completed : Nat) (state : X86_64MachineState)
    (_eventsRev : List AnyEvent) : Prop where
  rip : state.rip = spike2WindowsMainLoopRip
  rsp : state.rsp = spike2AfterPrologue.rsp
  counter : state.gprs .r13 = UInt64.ofNat (completed + 1)
  fibA : state.gprs .r14 = (fibNat (completed + 1)).toUInt64
  fibB : state.gprs .r15 = (fibNat (completed + 2)).toUInt64
  fault : state.fault = none
  lowMemory : Spike2RowLowMemory state

theorem spike2_initial_row_invariant :
    Spike2RowInvariant 0 spike2AfterPrologue ([] : List AnyEvent) where
  rip := rfl
  rsp := rfl
  counter := spike2_after_prologue_r13
  fibA := by change spike2AfterPrologue.gprs .r14 = 1; exact spike2_after_prologue_r14
  fibB := by change spike2AfterPrologue.gprs .r15 = 1; exact spike2_after_prologue_r15
  fault := spike2_after_prologue_fault
  lowMemory := spike2_after_prologue_lowMemory

end Spikes.Spike2Fibonacci.Windows

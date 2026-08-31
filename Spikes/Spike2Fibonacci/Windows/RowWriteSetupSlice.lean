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
-/import Spikes.Spike2Fibonacci.Windows.RowLineSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2WriteSetupResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713517
  rsp : final.rsp = spike2AfterPrologue.rsp
  writtenPointer : final.gprs .r9 = final.rsp + 40
  fault : final.fault = none
  writeFileIat : final.read64 5368721424 = 5368721424

opaque spike2_write_setup_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713489) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state) :
    Spike2WriteSetupResult state eventsRev := by
  let final := spike2BeforeWriteFile state
  have frame := spike2_write_setup_registerFrame state
  have finalLow := spike2_write_setup_lowMemory state low rsp
  exact {
    final := final
    certificate := spike2_write_setup_selected_prefix state eventsRev hrip safe
    registers := frame
    fibRegisters := by constructor <;> rfl
    lowMemory := finalLow
    rip := by
      change state.rip + 3 + 5 + 3 + 3 + 5 + 9 = 5368713517
      rw [hrip]
      rfl
    rsp := frame.rsp.trans rsp
    writtenPointer := by rfl
    fault := frame.fault.trans safe
    writeFileIat := by
      rw [finalLow 5368721424 (by decide)]
      exact spike2_after_prologue_writeFileIat }

end Spikes.Spike2Fibonacci.Windows

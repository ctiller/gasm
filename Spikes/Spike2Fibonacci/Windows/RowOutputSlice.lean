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
-/import Spikes.Spike2Fibonacci.Windows.RowWriteSetupSlice

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Effects Gasm.Targets Gasm.Targets.X86_64

structure Spike2OutputSetupResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 12
    initial eventsRev final eventsRev []
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713517
  rsp : final.rsp = spike2AfterPrologue.rsp
  writtenPointer : final.gprs .r9 = final.rsp + 40
  fault : final.fault = none
  writeFileIat : final.read64 5368721424 = 5368721424

opaque spike2_output_setup_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713457) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (cursorAbove : spike2RowLowMemoryTop ≤ (state.gprs .rdi).toNat)
    (cursorRoom : (state.gprs .rdi).toNat + 2 ≤ 2 ^ 64) :
    Spike2OutputSetupResult state eventsRev := by
  let line := spike2_line_slice state eventsRev hrip rsp safe low cursorAbove cursorRoom
  let write := spike2_write_setup_slice line.final eventsRev line.rip line.rsp line.fault
    line.lowMemory
  exact {
    final := write.final
    certificate := by simpa using line.certificate.append write.certificate
    registers := line.registers.trans write.registers
    fibRegisters := line.fibRegisters.trans write.fibRegisters
    lowMemory := write.lowMemory
    rip := write.rip
    rsp := write.rsp
    writtenPointer := write.writtenPointer
    fault := write.fault
    writeFileIat := write.writeFileIat }

end Spikes.Spike2Fibonacci.Windows

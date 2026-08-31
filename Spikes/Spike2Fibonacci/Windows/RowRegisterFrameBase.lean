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
-/import Spikes.Spike2Fibonacci.Windows.RowCallFrame
import Spikes.Spike2Fibonacci.Windows.RowCounterFacts

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64

/-- Registers carried unchanged from the driver header to the Win32 call boundary. -/
structure Spike2RowRegisterFrame (initial final : X86_64MachineState) : Prop where
  rsp : final.rsp = initial.rsp
  r13 : final.gprs .r13 = initial.gprs .r13
  fault : final.fault = initial.fault

/-- Fibonacci accumulators carried unchanged through the row prefix before recurrence. -/
structure Spike2FibRegisterFrame (initial final : X86_64MachineState) : Prop where
  r14 : final.gprs .r14 = initial.gprs .r14
  r15 : final.gprs .r15 = initial.gprs .r15

theorem Spike2FibRegisterFrame.trans {first middle final : X86_64MachineState}
    (left : Spike2FibRegisterFrame first middle)
    (right : Spike2FibRegisterFrame middle final) :
    Spike2FibRegisterFrame first final where
  r14 := right.r14.trans left.r14
  r15 := right.r15.trans left.r15

theorem Spike2RowRegisterFrame.trans {first middle final : X86_64MachineState}
    (left : Spike2RowRegisterFrame first middle)
    (right : Spike2RowRegisterFrame middle final) :
    Spike2RowRegisterFrame first final where
  rsp := right.rsp.trans left.rsp
  r13 := right.r13.trans left.r13
  fault := right.fault.trans left.fault

theorem spike2_main_header_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterMainHeader state) := by
  constructor <;> rfl

theorem spike2_fib_literal_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterFibLiteral state) := by
  constructor <;> rfl

theorem spike2_index_header_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterIndexHeader state) := by
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows

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
-/import Spikes.Spike2Fibonacci.Windows.RowHookFrame

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowCallFrame :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64 Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/-- The real indirect CALL push and `WriteFile` result word both remain above linked text/IAT. -/
theorem spike2_writeFile_lowMemory (state : X86_64MachineState)
    (holds : Spike2RowLowMemory state)
    (rsp : state.rsp = spike2AfterPrologue.rsp)
    (writtenPointer : state.gprs .r9 = state.rsp + 40) :
    Spike2RowLowMemory
      (writeFileHook (Event := AnyEvent) (spike2AfterWriteFileCall state)).1 := by
  have rspConcrete : state.rsp = 140737488289664 :=
    rsp.trans spike2_after_prologue_rsp_eq
  have pointerConcrete : state.gprs .r9 = 140737488289704 := by
    rw [writtenPointer, rspConcrete]
    rfl
  have nonzero : (state.gprs .r9 == 0) = false := by
    rw [pointerConcrete]
    decide
  exact spike2_writeFile_call_hook_lowMemory state holds
    (by rw [rspConcrete]; decide) (by rw [rspConcrete]; decide) nonzero
    (by rw [pointerConcrete]; decide) (by rw [pointerConcrete]; decide)

end Spikes.Spike2Fibonacci.Windows

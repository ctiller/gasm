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
-/import Spikes.Spike2Fibonacci.Windows.RowRegisterFrameDivision

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowRegisterFrameTwoTail :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Targets.X86_64

theorem spike2_two_digit_tens_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitTens state) := by
  constructor <;> rfl

theorem spike2_two_digit_head_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitHead state) := by
  constructor <;> rfl

theorem spike2_two_digit_tail_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterTwoDigitIndex state) := by
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows

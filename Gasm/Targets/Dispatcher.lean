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
-/

import Lean
import Gasm.Core.Types
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.Network
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.Windows.Win32API
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.Linux.Syscall

namespace Gasm.Targets

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Unified platform call interceptor for x86-64 routing Linux syscalls and Windows Win32 API calls by disjoint address spaces. -/
instance [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    ExternalCallInterceptor X86_64 Event where
  interceptCall addr s :=
    if addr == linuxSyscallEntry then
      linuxSyscallIntercept addr s
    else
      win32Intercept addr s

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Selected input-independent boundary predicate for the unified native dispatcher. -/
def selectedNonInputPlatformCall (address : Address) (state : X86_64MachineState) : Bool :=
  if address == linuxSyscallEntry then selectedNonInputLinuxCall address state
  else selectedNonInputWin32Call address state

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Congruence of the actual unified native interceptor, restricted by the selected-call predicate
    checked in each artifact's termination certificate. -/
theorem platformCallInterceptor_preserves_selected_external_input_frame
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    InterceptorPreservesExternalInputFrame (Event := Event) selectedNonInputPlatformCall := by
  intro address state stdin requests hselected
  change (if address == linuxSyscallEntry then
      linuxSyscallIntercept address (state.withExternalInputs stdin requests)
    else win32Intercept address (state.withExternalInputs stdin requests)) =
      (if address == linuxSyscallEntry then linuxSyscallIntercept address state
       else win32Intercept address state).map
        (fun result => (result.1.withExternalInputs stdin requests, result.2))
  by_cases haddress : address == linuxSyscallEntry
  · simp [selectedNonInputPlatformCall, haddress] at hselected
    simp [haddress]
    exact linuxCallIntercept_preserves_selected_external_input_frame (Event := Event)
      address state stdin requests hselected
  · simp [selectedNonInputPlatformCall, haddress] at hselected
    simp [haddress]
    exact win32CallIntercept_preserves_selected_external_input_frame (Event := Event)
      address state stdin requests hselected

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64-svc-0-abi -/
/-- Platform call interceptor for AArch64 routing Linux syscalls. -/
instance [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event] :
    Gasm.Targets.AArch64.ExternalCallInterceptor AArch64 Event where
  interceptCall addr s :=
    Gasm.Targets.AArch64.Linux.linuxSyscallIntercept addr s

end Gasm.Targets

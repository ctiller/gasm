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

import Gasm.Targets.Dispatcher

/-!
# Linux eventful native-outcome bridge

Target-owned one-step facts for the production x86-64 runner.  They retain the full native
outcome and use the unified platform dispatcher; an artifact adapter supplies only an applicable
indexed lookup and concrete syscall register facts.
-/

namespace Gasm.Targets.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- A selected Linux `sys_exit` is a typed terminal production outcome, not an event-list
    projection. -/
theorem runProgramOutcomeLoop_linux_sys_exit {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event)
    (hlookup : instructionAtRipIndexed indexed state.rip = some syscall_op)
    (hnumber : state.gprs .rax = SYS_exit) :
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      .terminated (.processExit (state.gprs .rdi).toUInt32)
        (sysExitHook (Event := Event) (X86_64Instruction.step syscall_op state)).1
        (Inject.inject (ProcessEvent.exit (state.gprs .rdi).toUInt32) :: eventsRev).reverse := by
  have hstep : X86_64Instruction.step syscall_op state =
      { (state.setGpr64 .rcx (state.rip + 2)).setGpr64 .r11 state.flags with
        rip := linuxSyscallEntry } := rfl
  simp [runProgramOutcomeLoop, hlookup, hstep, nativeOutcomeTransition,
    Gasm.Targets.X86_64.ExternalCallInterceptor.interceptCall, linuxSyscallIntercept, hnumber,
    SYS_exit, sysExitHook, X86_64MachineState.setGpr64]

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- A selected stdout `sys_write` takes the real production interception path, adds its concrete
    event to the accumulator, and continues with exactly the caller's remaining fuel. -/
theorem runProgramOutcomeLoop_linux_stdout_write {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (state : X86_64MachineState) (eventsRev : List Event)
    (hlookup : instructionAtRipIndexed indexed state.rip = some syscall_op)
    (hnumber : state.gprs .rax = SYS_write)
    (hstdout : state.gprs .rdi = 1)
    (hsafe : state.fault = none) :
    runProgramOutcomeLoop indexed (fuel + 1) state eventsRev =
      runProgramOutcomeLoop indexed fuel
        (sysWriteHook (Event := Event) (X86_64Instruction.step syscall_op state)).1
        (Inject.inject (ConsoleEvent.out
          ((X86_64Instruction.step syscall_op state).readString
            ((X86_64Instruction.step syscall_op state).gprs .rsi)
            (((X86_64Instruction.step syscall_op state).gprs .rdx).toNat))) :: eventsRev) := by
  have hstep : X86_64Instruction.step syscall_op state =
      { (state.setGpr64 .rcx (state.rip + 2)).setGpr64 .r11 state.flags with
        rip := linuxSyscallEntry } := rfl
  simp [runProgramOutcomeLoop, hlookup, hstep, nativeOutcomeTransition,
    Gasm.Targets.X86_64.ExternalCallInterceptor.interceptCall, linuxSyscallIntercept,
    SYS_write, hnumber, hstdout, hsafe, sysWriteHook, X86_64MachineState.setGpr64]

end Gasm.Targets.Linux

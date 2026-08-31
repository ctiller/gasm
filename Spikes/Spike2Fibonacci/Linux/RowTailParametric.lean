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

import Spikes.Spike2Fibonacci.Linux.Row8Parametric

/-!
# Spike 2 Linux row tail from an arbitrary formatter endpoint

The original symbolic row producer fixes its formatter endpoint to two extraction and two
reverse-write passes.  This module states the unchanged CR/LF, `SYS_write`, recurrence, and
back-edge producer from an arbitrary formatter endpoint, allowing the bounded UInt64 decimal
schedule to join the row tail for every digit count.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

namespace RowTailParametric

open Row8Parametric

def afterLineTerminator (formatted : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps lineTerminatorCode formatted

def beforeWriteSyscall (formatted : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps writeSetupCode (afterLineTerminator formatted)

def beforeWriteHook (formatted : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step syscall_op (beforeWriteSyscall formatted)

def writeStep (formatted : X86_64MachineState) : X86_64MachineState × Option AnyEvent :=
  sysWriteHook (Event := AnyEvent) (beforeWriteHook formatted)

def afterWriteSyscall (formatted : X86_64MachineState) : X86_64MachineState :=
  (writeStep formatted).1

def writeEvent (formatted : X86_64MachineState) : Option AnyEvent :=
  (writeStep formatted).2

def beforeBackEdge (formatted : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps recurrenceHeadCode (afterWriteSyscall formatted)

def afterRecurrence (formatted : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967027) (beforeBackEdge formatted)

/-- Exact local evidence for the fixed 19-transition tail.  Live Fibonacci registers are framed
against the formatter endpoint rather than a two-pass predecessor. -/
structure Frame (formatted : X86_64MachineState) : Prop where
  line : SequentialBlockFrame lineTerminatorCode formatted
  writeSetup : SequentialBlockFrame writeSetupCode (afterLineTerminator formatted)
  syscallLookup : instructionAtRipIndexed spike2Indexed (beforeWriteSyscall formatted).rip =
    some syscall_op
  syscallSelected : selectedNonInputPlatformCall
    (X86_64Instruction.step syscall_op (beforeWriteSyscall formatted)).rip
    (X86_64Instruction.step syscall_op (beforeWriteSyscall formatted)) = true
  syscallIntercept : ExternalCallInterceptor.interceptCall X86_64
    (X86_64Instruction.step syscall_op (beforeWriteSyscall formatted)).rip
    (X86_64Instruction.step syscall_op (beforeWriteSyscall formatted)) =
      some (afterWriteSyscall formatted, writeEvent formatted)
  afterWriteSyscallSafe : (afterWriteSyscall formatted).fault = none
  liveR13 : (afterWriteSyscall formatted).gprs .r13 = formatted.gprs .r13
  liveR14 : (afterWriteSyscall formatted).gprs .r14 = formatted.gprs .r14
  liveR15 : (afterWriteSyscall formatted).gprs .r15 = formatted.gprs .r15
  recurrence : SequentialBlockFrame recurrenceHeadCode (afterWriteSyscall formatted)
  backRip : (beforeBackEdge formatted).rip = 4198701
  backLookup : instructionAtRipIndexed spike2Indexed (beforeBackEdge formatted).rip =
    some (jmp_rel32 4294967027)
  backOrdinary : Spike2OrdinaryCode (afterRecurrence formatted)
  backSafe : (afterRecurrence formatted).fault = none

private theorem ordinarySelected (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    selectedNonInputPlatformCall state.rip state = true := by
  simp [selectedNonInputPlatformCall, ordinary.notLinuxEntry,
    Gasm.Targets.Windows.selectedNonInputWin32Call,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem ordinarySilent (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    ExternalCallInterceptor.interceptCall X86_64 (Event := AnyEvent) state.rip state = none := by
  change (if state.rip == linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = none
  simp [ordinary.notLinuxEntry, Gasm.Targets.Windows.win32Intercept,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem syscallPrefix {formatted : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : Frame formatted) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      (beforeWriteSyscall formatted) eventsRev (afterWriteSyscall formatted)
      (accumulateEvent eventsRev (writeEvent formatted))
      (emittedBy (writeEvent formatted)) := by
  refine ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
    (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed) (.syscall)
    (hooked := afterWriteSyscall formatted) (event := writeEvent formatted) ?_ ?_ ?_ ?_ ?_
  · exact frame.syscallLookup
  · exact frame.syscallSelected
  · exact frame.syscallIntercept
  · exact frame.afterWriteSyscallSafe
  · exact .nil _ _

/- REF: docs/PROOF_TACTICS.md#iterate-certificates-not-evaluators -/
/-- The fixed row tail is independent of how many decimal passes produced `formatted`. -/
theorem selectedPrefix {formatted : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : Frame formatted) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 19
      formatted eventsRev (afterRecurrence formatted)
      (accumulateEvent eventsRev (writeEvent formatted))
      (emittedBy (writeEvent formatted)) := by
  have line := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall lineTerminatorCode spike2Indexed formatted frame.line eventsRev
  have setup := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall writeSetupCode spike2Indexed
    (afterLineTerminator formatted) frame.writeSetup eventsRev
  have syscall := syscallPrefix (eventsRev := eventsRev) frame
  have recurrence := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall recurrenceHeadCode spike2Indexed
    (afterWriteSyscall formatted) frame.recurrence
    (accumulateEvent eventsRev (writeEvent formatted))
  have back : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      (beforeBackEdge formatted) (accumulateEvent eventsRev (writeEvent formatted))
      (afterRecurrence formatted) (accumulateEvent eventsRev (writeEvent formatted)) [] := by
    refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent)
      (.rel32 4294967027) frame.backLookup ?_ ?_ frame.backSafe (.nil _ _)
    · exact ordinarySelected _ frame.backOrdinary
    · exact ordinarySilent _ frame.backOrdinary
  have beforeCall := line.append setup
  have afterCall := syscall.append (recurrence.append back)
  simpa [lineTerminatorCode, writeSetupCode, recurrenceHeadCode, afterLineTerminator,
    beforeWriteSyscall, beforeBackEdge, afterRecurrence] using beforeCall.append afterCall

end RowTailParametric

end Spikes.Spike2Fibonacci.Linux

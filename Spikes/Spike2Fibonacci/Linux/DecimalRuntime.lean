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

import Spikes.Spike2Fibonacci.Linux.DecimalLayout

/-!
# Linux execution facts for the Spike 2 decimal loops

The x86 dispatcher shares a machine representation with Windows.  A normal Linux text address
is silent and selected only when its current memory does *not* make it a Win32 IAT slot.  That
fact is deliberately carried as program-owned execution evidence below; address coincidence is
not treated as an interceptor proof.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalMacro

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/-- Program-owned proof that a reached Linux instruction state is neither the Linux syscall
entry nor a dynamically-discovered Win32 IAT slot.  It is intentionally stateful: final RIP
placement alone cannot establish either dispatcher fact. -/
structure Spike2OrdinaryCode (state : X86_64MachineState) : Prop where
  notLinuxEntry : state.rip ≠ linuxSyscallEntry
  notWin32Iat : state.read64 state.rip ≠ state.rip

private theorem spike2OrdinaryCode_selected (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    selectedNonInputPlatformCall state.rip state = true := by
  simp [selectedNonInputPlatformCall, ordinary.notLinuxEntry,
    Gasm.Targets.Windows.selectedNonInputWin32Call,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem spike2OrdinaryCode_silent (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    ExternalCallInterceptor.interceptCall X86_64 (Event := AnyEvent) state.rip state = none := by
  change (if state.rip == linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = none
  simp [ordinary.notLinuxEntry, Gasm.Targets.Windows.win32Intercept,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

/-- All actual post-step states whose selection/silence facts make up one extraction pass. -/
structure Spike2ExtractionOrdinary (backDisp : UInt8) (initial : X86_64MachineState) : Prop where
  xor : Spike2OrdinaryCode (extractionStates initial).1
  divide : Spike2OrdinaryCode (extractionStates initial).2.1
  ascii : Spike2OrdinaryCode (extractionStates initial).2.2.1
  push : Spike2OrdinaryCode (extractionStates initial).2.2.2.1
  count : Spike2OrdinaryCode (extractionStates initial).2.2.2.2.1
  compare : Spike2OrdinaryCode (extractionStates initial).2.2.2.2.2
  branch : Spike2OrdinaryCode (X86_64Instruction.step (jne_rel8 backDisp)
    (extractionStates initial).2.2.2.2.2)

/-- All actual post-step states whose selection/silence facts make up one write pass. -/
structure Spike2WriteOrdinary (backDisp : UInt8) (initial : X86_64MachineState) : Prop where
  pop : Spike2OrdinaryCode (writeStates initial).1
  store : Spike2OrdinaryCode (writeStates initial).2.1
  cursor : Spike2OrdinaryCode (writeStates initial).2.2.1
  count : Spike2OrdinaryCode (writeStates initial).2.2.2
  branch : Spike2OrdinaryCode (X86_64Instruction.step (jne_rel8 backDisp)
    (writeStates initial).2.2.2)

/-- Derive the exact dispatcher runtime witness required by the linked extraction bridge. -/
theorem Spike2ExtractionOrdinary.runtimeEvidence (backDisp : UInt8)
    (initial : X86_64MachineState) (ordinary : Spike2ExtractionOrdinary backDisp initial) :
    ExtractionRuntimeEvidence (Event := AnyEvent) selectedNonInputPlatformCall backDisp initial where
  silentXor := spike2OrdinaryCode_silent _ ordinary.xor
  silentDiv := spike2OrdinaryCode_silent _ ordinary.divide
  silentAscii := spike2OrdinaryCode_silent _ ordinary.ascii
  silentPush := spike2OrdinaryCode_silent _ ordinary.push
  silentCount := spike2OrdinaryCode_silent _ ordinary.count
  silentCmp := spike2OrdinaryCode_silent _ ordinary.compare
  silentBranch := spike2OrdinaryCode_silent _ ordinary.branch
  selectedXor := spike2OrdinaryCode_selected _ ordinary.xor
  selectedDiv := spike2OrdinaryCode_selected _ ordinary.divide
  selectedAscii := spike2OrdinaryCode_selected _ ordinary.ascii
  selectedPush := spike2OrdinaryCode_selected _ ordinary.push
  selectedCount := spike2OrdinaryCode_selected _ ordinary.count
  selectedCmp := spike2OrdinaryCode_selected _ ordinary.compare
  selectedBranch := spike2OrdinaryCode_selected _ ordinary.branch

/-- Derive the exact dispatcher runtime witness required by the linked write bridge. -/
theorem Spike2WriteOrdinary.runtimeEvidence (backDisp : UInt8)
    (initial : X86_64MachineState) (ordinary : Spike2WriteOrdinary backDisp initial) :
    WriteRuntimeEvidence (Event := AnyEvent) selectedNonInputPlatformCall backDisp initial where
  silentPop := spike2OrdinaryCode_silent _ ordinary.pop
  silentStore := spike2OrdinaryCode_silent _ ordinary.store
  silentCursor := spike2OrdinaryCode_silent _ ordinary.cursor
  silentCount := spike2OrdinaryCode_silent _ ordinary.count
  silentBranch := spike2OrdinaryCode_silent _ ordinary.branch
  selectedPop := spike2OrdinaryCode_selected _ ordinary.pop
  selectedStore := spike2OrdinaryCode_selected _ ordinary.store
  selectedCursor := spike2OrdinaryCode_selected _ ordinary.cursor
  selectedCount := spike2OrdinaryCode_selected _ ordinary.count
  selectedBranch := spike2OrdinaryCode_selected _ ordinary.branch

/-- Construct an actual-index selected extraction pass once the program invariant supplies its
stateful stack/counter/fault and ordinary-code facts. -/
theorem spike2ExtractionLinkedLayout_selectedPass (initial : X86_64MachineState)
    (entry : initial.rip = spike2ExtractionLinkedLayout.address .clearHigh)
    (safety : ExtractionSafety 0 initial)
    (executionSafety : ExtractionExecutionSafety 236 initial)
    (ordinary : Spike2ExtractionOrdinary 236 initial)
    (branch : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2) :
    Gasm.Targets.X86_64.DecimalSchedule.SelectedExtractionPass (Event := AnyEvent)
      selectedNonInputPlatformCall spike2Indexed 236 0
      initial :=
  spike2ExtractionLinkedLayout.toSelectedPass initial entry safety executionSafety
    (ordinary.runtimeEvidence _ _) branch

/-- Construct an actual-index selected write pass once the program invariant supplies its
stateful stack/output/fault and ordinary-code facts. -/
theorem spike2WriteLinkedLayout_selectedPass (initial : X86_64MachineState)
    (entry : initial.rip = spike2WriteLinkedLayout.address .pop)
    (safety : WriteSafety 0 0 initial)
    (executionSafety : WriteExecutionSafety 243 initial)
    (ordinary : Spike2WriteOrdinary 243 initial)
    (branch : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2) :
    Gasm.Targets.X86_64.DecimalSchedule.SelectedWritePass (Event := AnyEvent)
      selectedNonInputPlatformCall spike2Indexed 243 0 0
      initial :=
  spike2WriteLinkedLayout.toSelectedPass initial entry safety executionSafety
    (ordinary.runtimeEvidence _ _) branch

end Spikes.Spike2Fibonacci.Linux

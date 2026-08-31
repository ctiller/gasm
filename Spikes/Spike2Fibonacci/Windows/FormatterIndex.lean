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
import Spikes.Spike2Fibonacci.Windows.FormatterBranch
import Spikes.Spike2Fibonacci.Windows.FormatterLiteral

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForFormatterIndex :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows Gasm.Targets.Linux Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions Gasm.Targets.X86_64.MacroAssembler

private theorem sequentialCmpIndex : SequentialInstruction (cmp_r64_imm8 .r13 10) where
  encoding := .compareImm8 .r13 10
  safeFallthrough := by intro _ _; rfl

/-- The branch state after comparing the formatter index against ten. -/
def spike2AfterIndexCompare (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (cmp_r64_imm8 .r13 10) state

/-- The local index-format branch following the `Fib(` literal. -/
def spike2AfterIndexHeader (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41) (spike2AfterIndexCompare state)

/-- Logical successors of the index-width test. Program proofs reason about these constructors;
    only the placement realization below mentions concrete addresses or instruction lengths. -/
inductive Spike2IndexBranch where
  | oneDigit
  | twoDigit

def Spike2IndexBranch.Chosen (branch : Spike2IndexBranch)
    (state : X86_64MachineState) : Prop :=
  match branch with
  | .oneDigit => ¬ X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state)
  | .twoDigit => X86BranchCondition.greaterEqual.holds (spike2AfterIndexCompare state)

/-- Artifact-owned placement of the comparison and its two logical successors. This is the only
    Spike 2 index-branch object permitted to know instruction widths and relative displacement. -/
structure Spike2IndexHeaderPlacement where
  entryRip : UInt64
  compareRip : UInt64
  oneDigitRip : UInt64
  twoDigitRip : UInt64
  compareLookup : instructionAtRipIndexed spike2Indexed entryRip =
    some (cmp_r64_imm8 .r13 10)
  branchLookup : instructionAtRipIndexed spike2Indexed compareRip = some (jge_rel8 41)
  compareNotLinux : compareRip ≠ linuxSyscallEntry
  compareUnaligned : compareRip % 8 ≠ 0
  compareDestination : ∀ state, state.rip = entryRip →
    (spike2AfterIndexCompare state).rip = compareRip
  oneDigitDestination : ∀ state, state.rip = entryRip →
    Spike2IndexBranch.oneDigit.Chosen state →
    (spike2AfterIndexHeader state).rip = oneDigitRip
  twoDigitDestination : ∀ state, state.rip = entryRip →
    Spike2IndexBranch.twoDigit.Chosen state →
    (spike2AfterIndexHeader state).rip = twoDigitRip

/-- Concrete placement realization for the linked Windows artifact. -/
def spike2IndexHeaderPlacement : Spike2IndexHeaderPlacement where
  entryRip := 5368713297
  compareRip := 5368713301
  oneDigitRip := 5368713303
  twoDigitRip := 5368713344
  compareLookup := by rfl
  branchLookup := by rfl
  compareNotLinux := by decide
  compareUnaligned := by decide
  compareDestination := by
    intro state hrip
    unfold spike2AfterIndexCompare
    rw [show (X86_64Instruction.step (cmp_r64_imm8 .r13 10) state).rip = state.rip + 4 by rfl,
      hrip]
    decide
  oneDigitDestination := by
    intro state hrip oneDigit
    unfold Spike2IndexBranch.Chosen at oneDigit
    simp only [X86BranchCondition.holds] at oneDigit
    unfold spike2AfterIndexHeader
    rw [step_jge_rel8_fallthrough_rip _ _ (decide_eq_false_iff_not.mpr oneDigit)]
    unfold spike2AfterIndexCompare
    change state.rip + 4 + 2 = 5368713303
    rw [hrip]
    decide
  twoDigitDestination := by
    intro state hrip twoDigit
    unfold Spike2IndexBranch.Chosen at twoDigit
    simp only [X86BranchCondition.holds] at twoDigit
    unfold spike2AfterIndexHeader
    rw [step_jge_rel8_taken_rip _ _ (decide_eq_true_iff.mpr twoDigit)]
    unfold spike2AfterIndexCompare
    change state.rip + 4 + 2 + signExtend8To64 41 = 5368713344
    rw [hrip]
    rfl

def Spike2IndexHeaderPlacement.destinationRip
    (placement : Spike2IndexHeaderPlacement) : Spike2IndexBranch → UInt64
  | .oneDigit => placement.oneDigitRip
  | .twoDigit => placement.twoDigitRip

/-- A selected branch result. Downstream proofs see the logical successor and its placement, never
    the instruction-length arithmetic used to establish that placement. -/
structure Spike2IndexHeaderResult (placement : Spike2IndexHeaderPlacement)
    (branch : Spike2IndexBranch) (state : X86_64MachineState) (eventsRev : List AnyEvent) where
  chosen : branch.Chosen state
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 2
    state eventsRev (spike2AfterIndexHeader state) eventsRev []
  rip : (spike2AfterIndexHeader state).rip = placement.destinationRip branch

theorem spike2_index_header_selected (placement : Spike2IndexHeaderPlacement)
    (branch : Spike2IndexBranch) (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = placement.entryRip) (chosen : branch.Chosen state)
    (selectedAt : selectedNonInputPlatformCall (spike2AfterIndexHeader state).rip
      (spike2AfterIndexHeader state) = true)
    (silent : @ExternalCallInterceptor.interceptCall X86_64 AnyEvent _
      (spike2AfterIndexHeader state).rip (spike2AfterIndexHeader state) = none)
    (safe : state.fault = none) : Spike2IndexHeaderResult placement branch state eventsRev := by
  have compareRip := placement.compareDestination state hrip
  have compareSafe : (spike2AfterIndexCompare state).fault = none := by
    change state.fault = none
    exact safe
  have compare := spike2_selected_local_prefix (cmp_r64_imm8 .r13 10) sequentialCmpIndex
    state eventsRev (by rw [hrip]; exact placement.compareLookup) placement.compareRip compareRip
    placement.compareNotLinux placement.compareUnaligned compareSafe
  have branchLookup : instructionAtRipIndexed spike2Indexed
      (spike2AfterIndexCompare state).rip = some (jge_rel8 41) := by
    rw [compareRip]
    exact placement.branchLookup
  cases branch with
  | oneDigit =>
      have finalRip := placement.oneDigitDestination state hrip chosen
      have branchPrefix := spike2_selected_conditional_fallthrough_prefix (.jge8 41)
        (spike2AfterIndexCompare state) chosen eventsRev branchLookup selectedAt silent (by
          change state.fault = none
          exact safe)
      exact {
        chosen := chosen
        certificate := by
          simpa [spike2AfterIndexHeader, spike2AfterIndexCompare] using compare.append branchPrefix
        rip := finalRip }
  | twoDigit =>
      have finalRip := placement.twoDigitDestination state hrip chosen
      have branchPrefix := spike2_selected_conditional_prefix (.jge8 41)
        (spike2AfterIndexCompare state) chosen eventsRev branchLookup selectedAt silent (by
          change state.fault = none
          exact safe)
      exact {
        chosen := chosen
        certificate := by
          simpa [spike2AfterIndexHeader, spike2AfterIndexCompare] using compare.append branchPrefix
        rip := finalRip }

end Spikes.Spike2Fibonacci.Windows

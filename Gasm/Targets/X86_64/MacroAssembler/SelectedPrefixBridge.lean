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

import Gasm.Targets.X86_64.EventfulSegment
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge

namespace Gasm.Targets.X86_64.MacroAssembler

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Every state reached after one instruction in a concrete sequential block is admitted by the
    caller's selection policy.  Keeping this property prefix-parametric prevents clients from
    constructing a deeply nested `SelectedPrefix.ordinary` term over repeatedly normalized
    concrete machine states. -/
def SelectedAfterEach
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (code : List X86_64Instr) (initial : X86_64MachineState) : Prop :=
  ∀ beforeCode instruction suffix, code = beforeCode ++ instruction :: suffix →
    let after := X86_64Instruction.step instruction (runLocalSteps beforeCode initial)
    selected after.rip after = true

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- All authority-bearing evidence for one ordinary step in a concrete sequential trace.  The
consumer supplies this compact record once per reached prefix; it need not separately traverse the
same fixed code list for placement, selection, silence, and safety. -/
structure SelectedSequentialStepEvidence {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr))
    (initial : X86_64MachineState) (beforeCode : List X86_64Instr)
    (instruction : X86_64Instr) : Prop where
  encoding : SequentialInstruction instruction
  lookup : instructionAtRipIndexed indexed (runLocalSteps beforeCode initial).rip = some instruction
  selectedAt : let after := X86_64Instruction.step instruction (runLocalSteps beforeCode initial)
    selected after.rip after = true
  silent : let after := X86_64Instruction.step instruction (runLocalSteps beforeCode initial)
    @ExternalCallInterceptor.interceptCall X86_64 Event _ after.rip after = none
  safe : (X86_64Instruction.step instruction (runLocalSteps beforeCode initial)).fault = none

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Construct an opaque selected prefix from one bundled evidence record per ordinary step. -/
theorem selectedPrefixOfSequentialEvidence {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (code : List X86_64Instr) (indexed : List (UInt64 × X86_64Instr))
    (initial : X86_64MachineState)
    (evidence : ∀ beforeCode instruction suffix,
      code = beforeCode ++ instruction :: suffix →
      SelectedSequentialStepEvidence (Event := Event) selected indexed initial beforeCode instruction)
    (eventsRev : List Event) :
    ProductionPrefix.SelectedPrefix selected indexed code.length initial eventsRev
      (runLocalSteps code initial) eventsRev [] := by
  let rec build (beforeCode remaining : List X86_64Instr)
      (split : code = beforeCode ++ remaining) :
      ProductionPrefix.SelectedPrefix selected indexed remaining.length
        (runLocalSteps beforeCode initial) eventsRev
        (runLocalSteps code initial) eventsRev [] := by
    cases remaining with
    | nil =>
        rw [show code = beforeCode by simpa using split]
        exact .nil _ _
    | cons instruction rest =>
        have stepEvidence := evidence beforeCode instruction rest split
        have nextSplit : code = (beforeCode ++ [instruction]) ++ rest := by
          simpa [List.append_assoc] using split
        have tail : ProductionPrefix.SelectedPrefix selected indexed rest.length
            (X86_64Instruction.step instruction (runLocalSteps beforeCode initial)) eventsRev
            (runLocalSteps code initial) eventsRev [] := by
          simpa [runLocalSteps_append, runLocalSteps] using
            build (beforeCode ++ [instruction]) rest nextSplit
        exact .ordinary stepEvidence.encoding stepEvidence.lookup stepEvidence.selectedAt
          stepEvidence.silent stepEvidence.safe tail
  simpa [runLocalSteps] using build [] code (by simp)

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Construct selected production evidence for a whole safe sequential block.

The theorem preserves every authority-bearing premise of `SelectedPrefix.ordinary`: instruction
classification, artifact lookup, selector admission, host silence, and step safety.  Its result is
opaque across module boundaries, so downstream proofs do not retain an instruction-by-instruction
constructor spine or duplicate normalization of closed intermediate machine states. -/
theorem selectedPrefixOfSafeSequential {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (code : List X86_64Instr)
    (sequential : ∀ instruction ∈ code, SequentialInstruction instruction)
    (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (initial : X86_64MachineState)
    (safe : SafeSequentialOn code initial)
    (placement : ContextualStraightLinePlacement indexed bodyBase code initial)
    (selectedAfterEach : SelectedAfterEach selected code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (eventsRev : List Event) :
    ProductionPrefix.SelectedPrefix selected indexed code.length initial eventsRev
      (runLocalSteps code initial) eventsRev [] := by
  let rec build (beforeCode remaining : List X86_64Instr)
      (split : code = beforeCode ++ remaining) :
      ProductionPrefix.SelectedPrefix selected indexed remaining.length
        (runLocalSteps beforeCode initial) eventsRev
        (runLocalSteps code initial) eventsRev [] := by
    cases remaining with
    | nil =>
        rw [show code = beforeCode by simpa using split]
        exact .nil _ _
    | cons instruction rest =>
        have member : instruction ∈ code := by
          rw [split]
          exact List.mem_append_right _ (by simp)
        have encoding := sequential instruction member
        have lookup := placement.lookup beforeCode instruction rest split
        have selectedAt := selectedAfterEach beforeCode instruction rest split
        have silentAt := silent beforeCode instruction rest split
        have safeAt := safe beforeCode instruction rest split
        have nextSplit : code = (beforeCode ++ [instruction]) ++ rest := by
          simpa [List.append_assoc] using split
        have tail : ProductionPrefix.SelectedPrefix selected indexed rest.length
            (X86_64Instruction.step instruction (runLocalSteps beforeCode initial)) eventsRev
            (runLocalSteps code initial) eventsRev [] := by
          simpa [runLocalSteps_append, runLocalSteps] using
            build (beforeCode ++ [instruction]) rest nextSplit
        exact ProductionPrefix.SelectedPrefix.ordinary
          encoding lookup selectedAt silentAt safeAt tail
  simpa [runLocalSteps] using build [] code (by simp)

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- Link-time specialization of `selectedPrefixOfSafeSequential`.

Clients keep the block at a symbolic `bodyBase` while proving its local transition, safety,
selection, and silence laws.  This bridge alone combines those laws with the final artifact's
global layout and contiguous-subsequence certificate.  Consequently no client must normalize a
large concrete instruction index once for every reached instruction address. -/
theorem selectedPrefixOfSafeSequentialSubsequence {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (code : List X86_64Instr)
    (sequential : ∀ instruction ∈ code, SequentialInstruction instruction)
    (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (initial : X86_64MachineState)
    (safe : SafeSequentialOn code initial)
    (entryRip : initial.rip = bodyBase)
    (layout : IndexedLayoutCertificate indexed)
    (subsequence : ContiguousInstructionSubsequence indexed bodyBase code)
    (selectedAfterEach : SelectedAfterEach selected code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (eventsRev : List Event) :
    ProductionPrefix.SelectedPrefix selected indexed code.length initial eventsRev
      (runLocalSteps code initial) eventsRev [] := by
  have placement := ContextualStraightLinePlacement.ofSafeSubsequence
    indexed bodyBase code initial sequential safe entryRip layout subsequence
  exact selectedPrefixOfSafeSequential selected code sequential indexed bodyBase initial safe
    placement selectedAfterEach silent eventsRev

end Gasm.Targets.X86_64.MacroAssembler

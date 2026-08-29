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

import Gasm.Targets.X86_64.MacroAssembler
import Gasm.Targets.X86_64.Semantics

namespace Gasm.Targets.X86_64.MacroAssembler

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- The admitted ordinary instruction forms preserve the architectural fault outcome. This is
    separate from their nominal control-flow classification. -/
theorem ControlFlowFree.step_fault_eq {instruction : X86_64Instr}
    (ordinary : ControlFlowFree instruction) (state : X86_64MachineState) :
    (X86_64Instruction.step instruction state).fault = state.fault := by
  cases ordinary <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- A successful admitted ordinary step advances to its decoded sequential successor. Fault
    behavior remains an explicit, independent outcome in the platform evaluator. -/
theorem ControlFlowFree.step_rip_eq {instruction : X86_64Instr}
    (ordinary : ControlFlowFree instruction) (state : X86_64MachineState) :
    (X86_64Instruction.step instruction state).rip =
      state.rip + (X86_64Instruction.encode instruction).size.toUInt64 := by
  cases ordinary <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
theorem runLocalSteps_fault_eq (code : List X86_64Instr)
    (ordinary : ∀ instruction ∈ code, ControlFlowFree instruction)
    (state : X86_64MachineState) :
    (runLocalSteps code state).fault = state.fault := by
  induction code generalizing state with
  | nil => rfl
  | cons first rest ih =>
      simp only [runLocalSteps]
      calc
        (runLocalSteps rest (X86_64Instruction.step first state)).fault =
            (X86_64Instruction.step first state).fault :=
          ih (fun instruction hi => ordinary instruction (by simp [hi])) _
        _ = state.fault := ControlFlowFree.step_fault_eq (ordinary first (by simp)) state

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- Encoded byte span, computed in the same modular address arithmetic as target lookup. -/
def instructionSpan : List X86_64Instr → UInt64
  | [] => 0
  | instruction :: rest =>
      (X86_64Instruction.encode instruction).size.toUInt64 + instructionSpan rest

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
theorem indexInstructions_loop_append (baseRip : UInt64)
    (first second : List X86_64Instr) :
    indexInstructions.loop baseRip (first ++ second) =
      indexInstructions.loop baseRip first ++
        indexInstructions.loop (baseRip + instructionSpan first) second := by
  induction first generalizing baseRip with
  | nil => simp [indexInstructions.loop, instructionSpan]
  | cons instruction rest ih =>
      simp only [List.cons_append, indexInstructions.loop, instructionSpan, List.cons.injEq,
        true_and]
      rw [ih]
      simp [UInt64.add_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
theorem indexInstructions_prefix_mem (bodyBase : UInt64)
    (code beforeCode : List X86_64Instr) (instruction : X86_64Instr)
    (suffix : List X86_64Instr) (split : code = beforeCode ++ instruction :: suffix) :
    (bodyBase + instructionSpan beforeCode, instruction) ∈ indexInstructions bodyBase code := by
  rw [split, indexInstructions, indexInstructions_loop_append]
  simp [indexInstructions.loop]

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
theorem runLocalSteps_rip_eq (code : List X86_64Instr)
    (ordinary : ∀ instruction ∈ code, ControlFlowFree instruction)
    (state : X86_64MachineState) :
    (runLocalSteps code state).rip = state.rip + instructionSpan code := by
  induction code generalizing state with
  | nil => simp [runLocalSteps, instructionSpan]
  | cons first rest ih =>
      simp only [runLocalSteps, instructionSpan]
      rw [ih (fun instruction hi => ordinary instruction (by simp [hi])),
        ControlFlowFree.step_rip_eq (ordinary first (by simp))]
      simp [UInt64.add_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- One final-artifact index certificate. Linkers derive it once from layout injectivity; body
    consumers reuse it for every included straight-line subsequence. -/
structure IndexedLayoutCertificate (indexed : List (UInt64 × X86_64Instr)) : Prop where
  resolves : ∀ entry ∈ indexed,
    instructionAtRipIndexed indexed entry.1 = some entry.2

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- A body's serialized instruction index is included in the final artifact index. This is the
    layout-stable fact regenerated after relayout or differential byte changes. -/
structure ContiguousInstructionSubsequence (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (code : List X86_64Instr) : Prop where
  included : ∀ entry ∈ indexInstructions bodyBase code, entry ∈ indexed

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- Linker-facing constructor: an instruction-list decomposition and the encoded prefix span imply
    inclusion of the body's complete index in the final artifact index. -/
theorem ContiguousInstructionSubsequence.ofDecomposition
    (artifactBase bodyBase : UInt64) (instructions beforeCode code afterCode : List X86_64Instr)
    (stream_eq : instructions = beforeCode ++ code ++ afterCode)
    (bodyBase_eq : bodyBase = artifactBase + instructionSpan beforeCode) :
    ContiguousInstructionSubsequence (indexInstructions artifactBase instructions) bodyBase code := by
  subst instructions
  subst bodyBase
  constructor
  intro entry memberBody
  simp only [indexInstructions] at memberBody ⊢
  rw [List.append_assoc]
  rw [indexInstructions_loop_append artifactBase beforeCode (code ++ afterCode)]
  apply List.mem_append_right
  rw [indexInstructions_loop_append (artifactBase + instructionSpan beforeCode) code afterCode]
  exact List.mem_append_left _ memberBody

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Exact target-owned placement evidence for a straight-line body inside a larger indexed stream.
    It connects each locally executed prefix to production instruction lookup. -/
structure ContextualStraightLinePlacement (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (code : List X86_64Instr) (initial : X86_64MachineState) : Prop where
  entryRip : initial.rip = bodyBase
  lookup : ∀ beforeCode instruction suffix, code = beforeCode ++ instruction :: suffix →
    instructionAtRipIndexed indexed (runLocalSteps beforeCode initial).rip = some instruction

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- Construct contextual lookup evidence from reusable final-layout resolution and one contiguous
    body inclusion proof. No per-prefix lookup proof is required from consumers. -/
theorem ContextualStraightLinePlacement.ofSubsequence
    (indexed : List (UInt64 × X86_64Instr)) (bodyBase : UInt64)
    (code : List X86_64Instr) (initial : X86_64MachineState)
    (ordinary : ∀ instruction ∈ code, ControlFlowFree instruction)
    (entryRip : initial.rip = bodyBase)
    (layout : IndexedLayoutCertificate indexed)
    (subsequence : ContiguousInstructionSubsequence indexed bodyBase code) :
    ContextualStraightLinePlacement indexed bodyBase code initial where
  entryRip := entryRip
  lookup := by
    intro beforeCode instruction suffix split
    have memberBody := indexInstructions_prefix_mem bodyBase code beforeCode instruction suffix split
    have memberArtifact := subsequence.included _ memberBody
    have resolves := layout.resolves _ memberArtifact
    rw [runLocalSteps_rip_eq beforeCode]
    · simpa [entryRip] using resolves
    · intro selected hi
      apply ordinary selected
      rw [split]
      exact List.mem_append_left _ hi

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- The selected runtime does not reinterpret an admitted ordinary step as an external call.
    This is required only at states reachable through prefixes of this concrete segment. -/
def RuntimeSilentOn {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (code : List X86_64Instr) (initial : X86_64MachineState) : Prop :=
  ∀ beforeCode instruction suffix, code = beforeCode ++ instruction :: suffix →
    let before := runLocalSteps beforeCode initial
    let after := X86_64Instruction.step instruction before
    interceptor.interceptCall after.rip after = none

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
private theorem runProgramOutcomeLoop_refinesLocal {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (code : List X86_64Instr)
    (ordinary : ∀ instruction ∈ code, ControlFlowFree instruction)
    (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (initial : X86_64MachineState)
    (placement : ContextualStraightLinePlacement indexed bodyBase code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (initialSafe : initial.fault = none)
    (continuationFuel : Nat) (eventsRev : List Event)
    (beforeCode remaining : List X86_64Instr)
    (split : code = beforeCode ++ remaining) :
    runProgramOutcomeLoop (Event := Event) indexed
        (remaining.length + continuationFuel) (runLocalSteps beforeCode initial) eventsRev =
      runProgramOutcomeLoop (Event := Event) indexed continuationFuel
        (runLocalSteps code initial) eventsRev := by
  induction remaining generalizing beforeCode with
  | nil =>
      rw [show code = beforeCode by simpa using split]
      simp
  | cons instruction rest ih =>
      have hlookup := placement.lookup beforeCode instruction rest split
      have instructionOrdinary : ControlFlowFree instruction := by
        apply ordinary instruction
        rw [split]
        simp
      have prefixSafe : (runLocalSteps beforeCode initial).fault = none := by
        have prefixOrdinary : ∀ i ∈ beforeCode, ControlFlowFree i := by
          intro i hi
          apply ordinary i
          rw [split]
          exact List.mem_append_left _ hi
        rw [runLocalSteps_fault_eq beforeCode prefixOrdinary]
        exact initialSafe
      have hsilent := silent beforeCode instruction rest split
      have nextSplit : code = (beforeCode ++ [instruction]) ++ rest := by
        simpa [List.append_assoc] using split
      simp only [List.length_cons]
      rw [show Nat.succ rest.length + continuationFuel =
        (rest.length + continuationFuel) + 1 by omega]
      rw [runProgramOutcomeLoop_step_none indexed (rest.length + continuationFuel)
        (runLocalSteps beforeCode initial) eventsRev instruction hlookup hsilent]
      · simpa [runLocalSteps_append, runLocalSteps] using
          ih (beforeCode ++ [instruction]) nextSplit
      · rw [ControlFlowFree.step_fault_eq instructionOrdinary]
        exact prefixSafe

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Reusable contextual refinement: the body consumes exactly its instruction count in production
    runner steps, then the caller-selected continuation resumes from the proved fallthrough state. -/
theorem runProgramOutcomeLoop_prefix {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (code : List X86_64Instr)
    (ordinary : ∀ instruction ∈ code, ControlFlowFree instruction)
    (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (initial : X86_64MachineState)
    (placement : ContextualStraightLinePlacement indexed bodyBase code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (initialSafe : initial.fault = none)
    (continuationFuel : Nat) (eventsRev : List Event) :
    runProgramOutcomeLoop (Event := Event) indexed
        (code.length + continuationFuel) initial eventsRev =
      runProgramOutcomeLoop (Event := Event) indexed continuationFuel
        (runLocalSteps code initial) eventsRev := by
  simpa [runLocalSteps] using
    runProgramOutcomeLoop_refinesLocal (Event := Event) code ordinary indexed bodyBase initial
      placement silent initialSafe continuationFuel eventsRev [] code (by simp)

end Gasm.Targets.X86_64.MacroAssembler

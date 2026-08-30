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
/-- A target-classified sequential instruction advances to fallthrough whenever its concrete step
    is safe. The safety premise is relevant for `DIV`; always-safe ordinary forms discharge it
    without exposing an extra program proof obligation. -/
theorem SequentialInstruction.step_rip_eq_of_safe {instruction : X86_64Instr}
    (sequential : SequentialInstruction instruction) (state : X86_64MachineState)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    (X86_64Instruction.step instruction state).rip =
      state.rip + (X86_64Instruction.encode instruction).size.toUInt64 := by
  exact sequential.safeFallthrough state safe

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Existing always-safe macro instructions canonically satisfy the broader sequential law. -/
theorem ControlFlowFree.sequential {instruction : X86_64Instr}
    (ordinary : ControlFlowFree instruction) : SequentialInstruction instruction where
  encoding := by cases ordinary <;> constructor
  safeFallthrough := fun state _ => ordinary.step_rip_eq state

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- The 32-bit immediate move used by native ABI setup is a safe sequential instruction.  It is
    kept separate from the smaller macro-only `ControlFlowFree` classification, whose existing
    constructors intentionally cover only the original reusable segment vocabulary. -/
theorem mov_r32_sequential (dst : Reg32) (value : UInt32) :
    SequentialInstruction (mov_r32 dst value) where
  encoding := .mov32 dst value
  safeFallthrough := by
    intro state _
    cases dst <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- The selected full-width errno-range comparison is a safe fallthrough instruction.  The
    resource-rejection proof uses this one additional ordinary form; branch classification remains
    separate and target-owned. -/
theorem cmp_r64_imm32_sequential (dst : Reg64) (value : UInt32) :
    SequentialInstruction (cmp_r64_imm32 dst value) where
  encoding := .compareImm32 dst value
  safeFallthrough := by
    intro state _
    rfl

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Every concrete instruction step reached inside a sequential segment is safe. Fault-capable
    instructions pay this obligation at the block that establishes their operand invariant. -/
def SafeSequentialOn (code : List X86_64Instr) (initial : X86_64MachineState) : Prop :=
  ∀ beforeCode instruction suffix, code = beforeCode ++ instruction :: suffix →
    (X86_64Instruction.step instruction (runLocalSteps beforeCode initial)).fault = none

theorem SafeSequentialOn.prefixSafe {code : List X86_64Instr} {initial : X86_64MachineState}
    (safe : SafeSequentialOn code initial) (initialSafe : initial.fault = none)
    (beforeCode remaining : List X86_64Instr) (split : code = beforeCode ++ remaining) :
    (runLocalSteps beforeCode initial).fault = none := by
  rcases beforeCode.eq_nil_or_concat with hnil | ⟨xs, last, hconcat⟩
  · subst beforeCode
    exact initialSafe
  · subst beforeCode
    have hlast := safe xs last remaining (by
      simpa [List.append_assoc] using split)
    simpa [List.concat_eq_append, runLocalSteps_append, runLocalSteps] using hlast

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

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Safe sequential segments have the same exact encoded-span placement law as always-safe macro
    segments. Safety is proved once at each reachable prefix, so a `DIV` precondition is not
    replayed by every whole-program consumer. -/
theorem runLocalSteps_rip_eq_sequential (code : List X86_64Instr)
    (sequential : ∀ instruction ∈ code, SequentialInstruction instruction)
    (initial : X86_64MachineState) (safe : SafeSequentialOn code initial) :
    (runLocalSteps code initial).rip = initial.rip + instructionSpan code := by
  induction code generalizing initial with
  | nil => simp [runLocalSteps, instructionSpan]
  | cons first rest ih =>
      have firstSequential := sequential first (by simp)
      have firstSafe := safe [] first rest (by simp)
      have restSequential : ∀ instruction ∈ rest, SequentialInstruction instruction := by
        intro instruction member
        exact sequential instruction (by simp [member])
      have restSafe : SafeSequentialOn rest (X86_64Instruction.step first initial) := by
        intro beforeCode instruction suffix split
        have wholeSplit : first :: rest = (first :: beforeCode) ++ instruction :: suffix := by
          simp only [List.cons_append, List.cons.injEq, true_and]
          exact split
        simpa [runLocalSteps] using safe (first :: beforeCode) instruction suffix wholeSplit
      simp only [runLocalSteps, instructionSpan]
      rw [ih restSequential _ restSafe,
        firstSequential.step_rip_eq_of_safe initial firstSafe]
      simp [UInt64.add_assoc]

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- One final-artifact index certificate. Linkers derive it once from layout injectivity; body
    consumers reuse it for every included straight-line subsequence. -/
structure IndexedLayoutCertificate (indexed : List (UInt64 × X86_64Instr)) : Prop where
  resolves : ∀ entry ∈ indexed,
    instructionAtRipIndexed indexed entry.1 = some entry.2

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- An indexed instruction stream with unique byte addresses is a complete lookup table.  This is
    deliberately structural: consumers prove address uniqueness from their linker range facts,
    then reuse this theorem without reducing the complete emitted instruction list. -/
theorem IndexedLayoutCertificate.ofNoDupAddresses
    (indexed : List (UInt64 × X86_64Instr))
    (unique : (indexed.map Prod.fst).Nodup) :
    IndexedLayoutCertificate indexed := by
  constructor
  intro entry member
  induction indexed with
  | nil => simp at member
  | cons head rest ih =>
      rcases head with ⟨address, instruction⟩
      have unique' : (rest.map Prod.fst).Nodup := by
        exact (List.pairwise_cons.mp unique).2
      simp only [List.map_cons, List.mem_cons] at member unique
      rcases member with hhead | hrest
      · cases hhead
        simp [instructionAtRipIndexed]
      · have hne : ¬ address = entry.1 := by
          intro heq
          have memberAddress : entry.1 ∈ rest.map Prod.fst :=
            List.mem_map.mpr ⟨entry, hrest, rfl⟩
          exact ((List.pairwise_cons.mp unique).1 entry.1 memberAddress) heq
        have hneBool : (address == entry.1) = false := by
          exact decide_eq_false_iff_not.mpr hne
        rw [instructionAtRipIndexed, hneBool]
        exact ih unique' hrest

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

/- REF: docs/MACRO_ASSEMBLER.md#placement-construction -/
/-- Placement constructor for sequential blocks containing state-conditionally safe operations.
    Final-artifact inclusion remains global; the block contributes only its local safety law. -/
theorem ContextualStraightLinePlacement.ofSafeSubsequence
    (indexed : List (UInt64 × X86_64Instr)) (bodyBase : UInt64)
    (code : List X86_64Instr) (initial : X86_64MachineState)
    (sequential : ∀ instruction ∈ code, SequentialInstruction instruction)
    (safe : SafeSequentialOn code initial)
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
    have prefixSequential : ∀ selected ∈ beforeCode, SequentialInstruction selected := by
      intro selected member
      apply sequential selected
      rw [split]
      exact List.mem_append_left _ member
    have prefixSafe : SafeSequentialOn beforeCode initial := by
      intro earlier selected later prefixSplit
      apply safe earlier selected (later ++ instruction :: suffix)
      rw [split, prefixSplit]
      simp [List.append_assoc]
    rw [runLocalSteps_rip_eq_sequential beforeCode prefixSequential initial prefixSafe]
    simpa [entryRip] using resolves

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

private theorem runProgramOutcomeLoop_refinesSafeSequential {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (code : List X86_64Instr)
    (sequential : ∀ instruction ∈ code, SequentialInstruction instruction)
    (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (initial : X86_64MachineState)
    (safe : SafeSequentialOn code initial)
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
      have prefixSafe := safe.prefixSafe initialSafe beforeCode (instruction :: rest) split
      have stepSafe := safe beforeCode instruction rest split
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
      · exact stepSafe

/- REF: docs/MACRO_ASSEMBLER.md#platform-execution-bridge -/
/-- Production refinement for a sequential block with explicit reachable-step safety. This is the
    scalable bridge used by formatting and arithmetic blocks: safe division is proved by the
    block invariant, while fetch placement and host silence remain reusable artifact/runtime facts. -/
theorem runProgramOutcomeLoop_prefix_safe {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (code : List X86_64Instr)
    (sequential : ∀ instruction ∈ code, SequentialInstruction instruction)
    (indexed : List (UInt64 × X86_64Instr))
    (bodyBase : UInt64) (initial : X86_64MachineState)
    (safe : SafeSequentialOn code initial)
    (placement : ContextualStraightLinePlacement indexed bodyBase code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (initialSafe : initial.fault = none)
    (continuationFuel : Nat) (eventsRev : List Event) :
    runProgramOutcomeLoop (Event := Event) indexed
        (code.length + continuationFuel) initial eventsRev =
      runProgramOutcomeLoop (Event := Event) indexed continuationFuel
        (runLocalSteps code initial) eventsRev := by
  simpa [runLocalSteps] using
    runProgramOutcomeLoop_refinesSafeSequential (Event := Event) code sequential indexed
      bodyBase initial safe placement silent initialSafe continuationFuel eventsRev [] code (by simp)

end Gasm.Targets.X86_64.MacroAssembler

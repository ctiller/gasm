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

import Gasm.Targets.AArch64.MacroAssembler
import Gasm.Targets.AArch64.Semantics

namespace Gasm.Targets.AArch64.MacroAssembler

open Gasm.Targets.AArch64
open Gasm.Targets.AArch64.Instructions

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-platform-execution-bridge -/
/-- Exact lookup of each reached local prefix in the final production instruction index. The
    artifact/linker supplies this evidence; the macro certificate cannot manufacture placement. -/
structure ContextualStraightLinePlacement
    (indexed : List (UInt64 × AnyAArch64Instruction)) (code : List Instruction)
    (initial : AArch64MachineState) : Prop where
  lookup : ∀ (index : Nat) (inBounds : index < code.length),
    instructionAtPcIndexed indexed (runLocalSteps (code.take index) initial).pc =
      some (code[index]'inBounds).emit

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-platform-execution-bridge -/
/-- The selected host profile does not reinterpret an interior arithmetic instruction as a host
    call. This remains runtime/profile evidence, not an implication of straight-line syntax. -/
def RuntimeSilentOn {Event : Type} [interceptor : ExternalCallInterceptor AArch64 Event]
    (code : List Instruction) (initial : AArch64MachineState) : Prop :=
  ∀ (index : Nat) (inBounds : index < code.length),
    let before := runLocalSteps (code.take index) initial
    let after := (code[index]'inBounds).step before
    interceptor.interceptCall after.pc after = none

private theorem runAArch64OutcomeLoop_refinesLocal {Event : Type}
    [ExternalCallInterceptor AArch64 Event]
    (code : List Instruction)
    (indexed : List (UInt64 × AnyAArch64Instruction))
    (initial : AArch64MachineState)
    (placement : ContextualStraightLinePlacement indexed code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (initialSafe : initial.fault = none) (initialRunning : initial.terminated = false)
    (continuationFuel : Nat) (eventsRev : List Event)
    (beforeCode remaining : List Instruction)
    (split : code = beforeCode ++ remaining) :
    runAArch64OutcomeLoop (Event := Event) indexed
        (remaining.length + continuationFuel) (runLocalSteps beforeCode initial) eventsRev =
      runAArch64OutcomeLoop (Event := Event) indexed continuationFuel
        (runLocalSteps code initial) eventsRev := by
  induction remaining generalizing beforeCode with
  | nil =>
      rw [show code = beforeCode by simpa using split]
      simp
  | cons instruction rest ih =>
      let before := runLocalSteps beforeCode initial
      have inBounds : beforeCode.length < code.length := by simp [split]
      have hlookup := placement.lookup beforeCode.length inBounds
      have takePrefix : code.take beforeCode.length = beforeCode := by simp [split]
      have selected : code[beforeCode.length]'inBounds = instruction := by simp [split]
      rw [takePrefix, selected] at hlookup
      change instructionAtPcIndexed indexed before.pc = some instruction.emit at hlookup
      have beforeFault : before.fault.isSome = false := by
        simp only [before]
        rw [runLocalSteps_preservesFault beforeCode initial, initialSafe]
        rfl
      have beforeRunning : before.terminated = false := by
        simp only [before]
        rw [runLocalSteps_preservesTerminated beforeCode initial, initialRunning]
      have stepFault : (instruction.step before).fault.isSome = false := by
        have preserved := runLocalSteps_preservesFault [instruction] before
        simpa [runLocalSteps, beforeFault] using congrArg Option.isSome preserved
      have stepRunning : (instruction.step before).terminated = false := by
        have preserved := runLocalSteps_preservesTerminated [instruction] before
        simpa [runLocalSteps, beforeRunning] using preserved
      have hsilent := silent beforeCode.length inBounds
      rw [takePrefix, selected] at hsilent
      change ExternalCallInterceptor.interceptCall AArch64
        (instruction.step before).pc (instruction.step before) = none at hsilent
      have nextSplit : code = (beforeCode ++ [instruction]) ++ rest := by
        simpa [List.append_assoc] using split
      simp only [List.length_cons]
      rw [show Nat.succ rest.length + continuationFuel =
        (rest.length + continuationFuel) + 1 by omega]
      have oneStep :
          runAArch64OutcomeLoop (Event := Event) indexed
              ((rest.length + continuationFuel) + 1) before eventsRev =
            runAArch64OutcomeLoop (Event := Event) indexed
              (rest.length + continuationFuel) (instruction.step before) eventsRev := by
        rw [runAArch64OutcomeLoop]
        simp only [beforeFault, beforeRunning, Bool.false_eq_true, ↓reduceIte, hlookup]
        rw [Instruction.step_emit]
        simp only [stepFault, stepRunning, Bool.false_eq_true, ↓reduceIte, hsilent]
      rw [oneStep]
      simpa [before, runLocalSteps_append, runLocalSteps] using
        ih (beforeCode ++ [instruction]) nextSplit

/- REF: docs/MACRO_ASSEMBLER.md#aarch64-platform-execution-bridge -/
/-- A safe, nonintercepted straight-line body consumes exactly its instruction count in the real
    AArch64 outcome runner and resumes the caller's unchanged continuation. It does not itself
    establish the continuation, termination, admissibility, exports, or final artifact identity. -/
theorem runAArch64OutcomeLoop_prefix {Event : Type}
    [ExternalCallInterceptor AArch64 Event]
    (code : List Instruction)
    (indexed : List (UInt64 × AnyAArch64Instruction))
    (initial : AArch64MachineState)
    (placement : ContextualStraightLinePlacement indexed code initial)
    (silent : RuntimeSilentOn (Event := Event) code initial)
    (initialSafe : initial.fault = none) (initialRunning : initial.terminated = false)
    (continuationFuel : Nat) (eventsRev : List Event) :
    runAArch64OutcomeLoop (Event := Event) indexed
        (code.length + continuationFuel) initial eventsRev =
      runAArch64OutcomeLoop (Event := Event) indexed continuationFuel
        (runLocalSteps code initial) eventsRev := by
  simpa [runLocalSteps] using
    runAArch64OutcomeLoop_refinesLocal (Event := Event) code indexed initial placement silent
      initialSafe initialRunning continuationFuel eventsRev [] code (by simp)

end Gasm.Targets.AArch64.MacroAssembler

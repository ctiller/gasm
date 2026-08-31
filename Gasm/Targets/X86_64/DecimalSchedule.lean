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

import Gasm.Targets.X86_64.DecimalPass
import Stdlib.Fmt.UInt64DecimalSchedule

/-!
# x86-64 realization of the bounded UInt64 decimal schedule

The reusable one-pass instruction contracts live in `DecimalPass`; this module composes them into
the portable bounded extraction/write schedule.

This layer connects the artifact-indexed production passes to the portable extraction and reverse
schedule. The layer retains exact target execution and selected-call evidence; it creates no evaluator,
artifact, export, or `VerifiedProgram` authority.
-/

namespace Gasm.Targets.X86_64.DecimalSchedule

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalStepFacts
open Stdlib.Fmt

/-- The extraction half of a decimal schedule advances only through an exact selected seven-step
pass.  Its bound is the portable digit count, so it cannot introduce a logical zero-fuel pass. -/
structure DecimalExtractionPhase {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (value : UInt64)
    (invariant : Nat → X86_64MachineState → List Event → Prop) : Prop where
  run : ∀ completed state eventsRev,
    completed < decimalDigitCount value → invariant completed state eventsRev →
      ∃ backDisp stackLower,
        SelectedExtractionPass (Event := Event) selected indexed backDisp stackLower state ∧
        invariant (completed + 1) (extractionFinal backDisp state) eventsRev

namespace DecimalExtractionPhase

theorem toSelectedBoundedInvariantLoopStep {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {value : UInt64}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (phase : DecimalExtractionPhase selected indexed value invariant) :
    SelectedBoundedInvariantLoopStep selected indexed (decimalDigitCount value) invariant where
  run completed state eventsRev within holds := by
    rcases phase.run completed state eventsRev within holds with ⟨backDisp, stackLower, pass, next⟩
    exact ⟨7, extractionFinal backDisp state, eventsRev, [], by decide, pass.selectedPrefix, next⟩

end DecimalExtractionPhase

/-- The reverse-write half advances only through an exact selected five-step pop/write pass. -/
structure DecimalWritePhase {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (value : UInt64)
    (invariant : Nat → X86_64MachineState → List Event → Prop) : Prop where
  run : ∀ completed state eventsRev,
    completed < decimalDigitCount value → invariant completed state eventsRev →
      ∃ backDisp stackUpper outputLimit,
        SelectedWritePass (Event := Event) selected indexed backDisp stackUpper outputLimit state ∧
        invariant (completed + 1) (writeFinal backDisp state) eventsRev

namespace DecimalWritePhase

theorem toSelectedBoundedInvariantLoopStep {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {value : UInt64}
    {invariant : Nat → X86_64MachineState → List Event → Prop}
    (phase : DecimalWritePhase selected indexed value invariant) :
    SelectedBoundedInvariantLoopStep selected indexed (decimalDigitCount value) invariant where
  run completed state eventsRev within holds := by
    rcases phase.run completed state eventsRev within holds with
      ⟨backDisp, stackUpper, outputLimit, pass, next⟩
    exact ⟨5, writeFinal backDisp state, eventsRev, [], by decide, pass.selectedPrefix, next⟩

end DecimalWritePhase

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- A target realization of the shared bounded UInt64 decimal schedule.

The only constructor is the exact two-phase schedule: each portable digit is extracted by a
selected seven-instruction pass, then written by a selected five-instruction pass.  Consequently
no arbitrary selected prefix or final-state predicate can be packaged as a realization. -/
inductive UInt64DecimalScheduleRealization {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (capacity : Nat) (value : UInt64)
    (initial : X86_64MachineState) (initialEventsRev : List Event)
    (callerFrame : CallerFrame) : Prop where
  | ofPhases
      {extractInvariant writeInvariant : Nat → X86_64MachineState → List Event → Prop}
      (extraction : DecimalExtractionPhase selected indexed value extractInvariant)
      (write : DecimalWritePhase selected indexed value writeInvariant)
      (extractInitial : extractInvariant 0 initial initialEventsRev)
      (startWrite : ∀ middle eventsRev,
        extractInvariant (decimalDigitCount value) middle eventsRev →
          writeInvariant 0 middle eventsRev)
      (capacityFits : decimalDigitCount value ≤ capacity)
      (outputAddressNoWrap : (initial.gprs .rdi).toNat + decimalDigitCount value ≤ 2 ^ 64)
      (completed : ∀ final finalEventsRev,
        writeInvariant (decimalDigitCount value) final finalEventsRev →
          finalEventsRev = initialEventsRev ∧
          final.rsp = initial.rsp ∧
          final.gprs .rdi = initial.gprs .rdi + UInt64.ofNat (decimalDigitCount value) ∧
          final.gprs .rcx = 0 ∧
          decimalBytesAt final.memory (initial.gprs .rdi) (decimalDigitCount value) =
            formatDecimal value.toNat ∧
          final.gprs .r12 = initial.gprs .r12 ∧ final.gprs .r13 = initial.gprs .r13 ∧
          final.gprs .r14 = initial.gprs .r14 ∧ final.gprs .r15 = initial.gprs .r15 ∧
          callerFrame initial final) :
      UInt64DecimalScheduleRealization selected indexed capacity value initial initialEventsRev
        callerFrame

namespace UInt64DecimalScheduleRealization

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Success capacity is part of the realization certificate, rather than a phantom parameter. -/
theorem capacityFits {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {capacity : Nat} {value : UInt64}
    {initial : X86_64MachineState} {initialEventsRev : List Event} {callerFrame : CallerFrame}
    (realization : UInt64DecimalScheduleRealization selected indexed capacity value initial
      initialEventsRev callerFrame) : decimalDigitCount value ≤ capacity := by
  rcases realization with ⟨_, _, _, _, capacityFits, _, _⟩
  exact capacityFits

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- The successful write range is certified not to wrap the output address. -/
theorem outputAddressNoWrap {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {capacity : Nat} {value : UInt64}
    {initial : X86_64MachineState} {initialEventsRev : List Event} {callerFrame : CallerFrame}
    (realization : UInt64DecimalScheduleRealization selected indexed capacity value initial
      initialEventsRev callerFrame) :
    (initial.gprs .rdi).toNat + decimalDigitCount value ≤ 2 ^ 64 := by
  rcases realization with ⟨_, _, _, _, _, outputAddressNoWrap, _⟩
  exact outputAddressNoWrap

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- The sole realization constructor exposes its exact selected execution prefix here.  Extraction
and reverse-write each run once per portable digit, and the phases join only with
`SelectedPrefix.append`. -/
theorem selectedPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {capacity : Nat} {value : UInt64}
    {initial : X86_64MachineState} {initialEventsRev : List Event} {callerFrame : CallerFrame}
    (realization : UInt64DecimalScheduleRealization selected indexed capacity value initial
      initialEventsRev callerFrame) :
    ∃ requiredFuel final finalEventsRev emitted,
      ProductionPrefix.SelectedPrefix selected indexed requiredFuel initial initialEventsRev
        final finalEventsRev emitted ∧
      finalEventsRev = initialEventsRev ∧
      final.rsp = initial.rsp ∧
      final.gprs .rdi = initial.gprs .rdi + UInt64.ofNat (decimalDigitCount value) ∧
      final.gprs .rcx = 0 ∧
      decimalBytesAt final.memory (initial.gprs .rdi) (decimalDigitCount value) =
        formatDecimal value.toNat ∧
      final.gprs .r12 = initial.gprs .r12 ∧ final.gprs .r13 = initial.gprs .r13 ∧
      final.gprs .r14 = initial.gprs .r14 ∧ final.gprs .r15 = initial.gprs .r15 ∧
      callerFrame initial final := by
  rcases realization with ⟨extraction, write, extractInitial, startWrite, capacityFits,
      outputAddressNoWrap, completed⟩
  let extractStep := extraction.toSelectedBoundedInvariantLoopStep
  rcases extractStep.iterate initial initialEventsRev extractInitial with
    ⟨middle, middleEventsRev, extractionEvents, extractionFuel, extractionPrefix, middleInvariant⟩
  let writeStep := write.toSelectedBoundedInvariantLoopStep
  rcases writeStep.iterate middle middleEventsRev (startWrite middle middleEventsRev middleInvariant) with
    ⟨final, finalEventsRev, writeEvents, writeFuel, writePrefix, finalInvariant⟩
  rcases completed final finalEventsRev finalInvariant with
    ⟨eventsPreserved, restoredRsp, advancedCursor, clearedCount, formatBytes, preservesR12, preservesR13,
      preservesR14, preservesR15, callerFramePreserved⟩
  exact ⟨extractionFuel + writeFuel, final, finalEventsRev,
    extractionEvents ++ writeEvents, extractionPrefix.append writePrefix,
    eventsPreserved, restoredRsp, advancedCursor, clearedCount, formatBytes, preservesR12, preservesR13,
    preservesR14, preservesR15, callerFramePreserved⟩

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- The selected prefix can be forgotten only at a consumer that explicitly needs the ordinary
production runner. -/
theorem toProductionPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {capacity : Nat} {value : UInt64}
    {initial : X86_64MachineState} {initialEventsRev : List Event} {callerFrame : CallerFrame}
    (realization : UInt64DecimalScheduleRealization selected indexed capacity value initial
      initialEventsRev callerFrame) :
    ∃ requiredFuel final finalEventsRev emitted,
      ProductionPrefix indexed requiredFuel initial initialEventsRev final finalEventsRev emitted ∧
      final.rsp = initial.rsp ∧
      final.gprs .rdi = initial.gprs .rdi + UInt64.ofNat (decimalDigitCount value) ∧
      final.gprs .rcx = 0 ∧
      decimalBytesAt final.memory (initial.gprs .rdi) (decimalDigitCount value) =
        formatDecimal value.toNat ∧
      final.gprs .r12 = initial.gprs .r12 ∧
      final.gprs .r13 = initial.gprs .r13 ∧
      final.gprs .r14 = initial.gprs .r14 ∧
      final.gprs .r15 = initial.gprs .r15 ∧
      callerFrame initial final := by
  rcases realization.selectedPrefix with
    ⟨requiredFuel, final, finalEventsRev, emitted, selectedPrefix, _eventsPreserved, restoredRsp, advancedCursor,
      clearedCount, formatBytes, preservesR12, preservesR13, preservesR14, preservesR15,
      callerFramePreserved⟩
  exact ⟨requiredFuel, final, finalEventsRev, emitted, selectedPrefix.toProductionPrefix,
    restoredRsp, advancedCursor, clearedCount, formatBytes, preservesR12, preservesR13,
    preservesR14, preservesR15, callerFramePreserved⟩

end UInt64DecimalScheduleRealization

end Gasm.Targets.X86_64.DecimalSchedule

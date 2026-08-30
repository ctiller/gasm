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

import Gasm.Targets.X86_64.DecimalSegments
import Stdlib.Fmt.UInt64DecimalSchedule

/-!
# x86-64 realization of the bounded UInt64 decimal schedule

This layer connects the artifact-indexed production passes to the portable extraction/reverse
schedule. It retains exact target execution and selected-call evidence; it creates no evaluator,
artifact, export, or `VerifiedProgram` authority.
-/

namespace Gasm.Targets.X86_64.DecimalSchedule

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Stdlib.Fmt

private theorem divByTenCoreQuotient (state : X86_64MachineState)
    (highZero : state.gprs .rdx = 0) (divisorTen : state.gprs .r10 = 10) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs .rax =
      UInt64.ofNat ((state.gprs .rax).toNat / 10) := by
  simp only [X86_64Instruction.step]
  rw [divisorTen, highZero]
  have bound : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF := by
    have := (state.gprs .rax).toNat_lt
    omega
  have notOverflow : ¬ 0xFFFFFFFFFFFFFFFF < (state.gprs .rax).toNat / 10 :=
    Nat.not_lt_of_ge bound
  simp [notOverflow, X86_64MachineState.setGpr64]

private theorem divByTenCoreRemainder (state : X86_64MachineState)
    (highZero : state.gprs .rdx = 0) (divisorTen : state.gprs .r10 = 10) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs .rdx =
      UInt64.ofNat ((state.gprs .rax).toNat % 10) := by
  simp only [X86_64Instruction.step]
  rw [divisorTen, highZero]
  have bound : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF := by
    have := (state.gprs .rax).toNat_lt
    omega
  have notOverflow : ¬ 0xFFFFFFFFFFFFFFFF < (state.gprs .rax).toNat / 10 :=
    Nat.not_lt_of_ge bound
  simp [notOverflow, X86_64MachineState.setGpr64]

private theorem xorEdxCoreZero (state : X86_64MachineState) :
    (X86_64Instruction.step (XorR32R32.mk .edx .edx) state).gprs .rdx = 0 := by
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64]

private theorem divCorePreservesGpr (state : X86_64MachineState) (r : Reg64)
    (notRax : r ≠ .rax) (notRdx : r ≠ .rdx) :
    (X86_64Instruction.step (DivR64.mk .r10) state).gprs r = state.gprs r := by
  simp only [X86_64Instruction.step]
  split
  · rfl
  · split
    · rfl
    · simp [X86_64MachineState.setGpr64, notRax, notRdx]

private theorem divCorePreservesMemory (state : X86_64MachineState) :
    (X86_64Instruction.step (DivR64.mk .r10) state).memory = state.memory := by
  simp only [X86_64Instruction.step]
  split
  · rfl
  · split <;> rfl

theorem extractionAfterDiv_preservesGpr (initial : X86_64MachineState) (r : Reg64)
    (notRax : r ≠ .rax) (notRdx : r ≠ .rdx) :
    (extractionStates initial).2.1.gprs r = initial.gprs r := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).gprs r = initial.gprs r
  rw [divCorePreservesGpr core r notRax notRdx]
  let input : X86_64MachineState :=
    { initial with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step XorR32R32 instX86_64InstructionXorR32R32
    { dst := .edx, src := .edx } input).gprs r = initial.gprs r
  dsimp only [input]
  simp [X86_64Instruction.step, X86_64MachineState.setGpr32,
    X86_64MachineState.setFlagsLogic, reg32To64, notRdx]

theorem extractionAfterDiv_preservesMemory (initial : X86_64MachineState) :
    (extractionStates initial).2.1.memory = initial.memory := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).memory = initial.memory
  rw [divCorePreservesMemory core]
  rfl

theorem extractionAfterDiv_quotient (initial : X86_64MachineState)
    (divisorTen : initial.gprs .r10 = 10) :
    (extractionStates initial).2.1.gprs .rax =
      UInt64.ofNat ((initial.gprs .rax).toNat / 10) := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).gprs .rax = UInt64.ofNat ((initial.gprs .rax).toNat / 10)
  rw [divByTenCoreQuotient core]
  · rfl
  · change (X86_64Instruction.step (xor_r32 .edx .edx) initial).gprs .rdx = 0
    let input : X86_64MachineState :=
      { initial with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step XorR32R32 instX86_64InstructionXorR32R32
      { dst := .edx, src := .edx } input).gprs .rdx = 0
    exact xorEdxCoreZero input
  · exact divisorTen

theorem extractionAfterDiv_remainder (initial : X86_64MachineState)
    (divisorTen : initial.gprs .r10 = 10) :
    (extractionStates initial).2.1.gprs .rdx =
      UInt64.ofNat ((initial.gprs .rax).toNat % 10) := by
  unfold extractionStates
  let afterXor := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let core : X86_64MachineState :=
    { afterXor with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).gprs .rdx = UInt64.ofNat ((initial.gprs .rax).toNat % 10)
  rw [divByTenCoreRemainder core]
  · rfl
  · change (X86_64Instruction.step (xor_r32 .edx .edx) initial).gprs .rdx = 0
    let input : X86_64MachineState :=
      { initial with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step XorR32R32 instX86_64InstructionXorR32R32
      { dst := .edx, src := .edx } input).gprs .rdx = 0
    exact xorEdxCoreZero input
  · exact divisorTen

/-- Architectural consequences of one extraction pass. Memory is stated as the exact PUSH
update; callers may derive any disjoint frame observation from that equation. -/
structure ExtractionPassEffect (backDisp : UInt8)
    (initial final : X86_64MachineState) : Prop where
  final_eq : final = extractionFinal backDisp initial
  quotient : final.gprs .rax = UInt64.ofNat ((initial.gprs .rax).toNat / 10)
  asciiRemainder : final.gprs .rdx = UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30
  count : final.gprs .rcx = initial.gprs .rcx + 1
  stackPointer : final.rsp = initial.rsp - 8
  memory : final.memory = X86_64Mem.write .w64 (initial.rsp - 8)
    (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 0x30) initial.memory
  preservesR12 : final.gprs .r12 = initial.gprs .r12
  preservesR13 : final.gprs .r13 = initial.gprs .r13
  preservesR14 : final.gprs .r14 = initial.gprs .r14
  preservesR15 : final.gprs .r15 = initial.gprs .r15
  fault : final.fault = none

/-- Architectural consequences of one pop/write pass. Memory is the exact one-byte store. -/
structure WritePassEffect (backDisp : UInt8)
    (initial final : X86_64MachineState) : Prop where
  final_eq : final = writeFinal backDisp initial
  poppedDigit : final.gprs .rdx = initial.read64 initial.rsp
  cursor : final.gprs .rdi = initial.gprs .rdi + 1
  count : final.gprs .rcx = initial.gprs .rcx - 1
  stackPointer : final.rsp = initial.rsp + 8
  memory : final.memory = X86_64Mem.write .w8 (initial.gprs .rdi)
    (initial.read64 initial.rsp).toUInt8.toUInt64 initial.memory
  preservesR12 : final.gprs .r12 = initial.gprs .r12
  preservesR13 : final.gprs .r13 = initial.gprs .r13
  preservesR14 : final.gprs .r14 = initial.gprs .r14
  preservesR15 : final.gprs .r15 = initial.gprs .r15
  fault : final.fault = none

theorem extractionPassEffect (backDisp : UInt8) (stackLower : UInt64)
    (initial : X86_64MachineState) (pre : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety backDisp initial) :
    ExtractionPassEffect backDisp initial (extractionFinal backDisp initial) := by
  constructor
  · rfl
  · rw [show (extractionFinal backDisp initial).gprs .rax =
        (extractionStates initial).2.1.gprs .rax by rfl]
    exact extractionAfterDiv_quotient initial pre.divisorTen
  · rw [show (extractionFinal backDisp initial).gprs .rdx =
        (extractionStates initial).2.1.gprs .rdx + 0x30 by rfl]
    rw [extractionAfterDiv_remainder initial pre.divisorTen]
  · rw [show (extractionFinal backDisp initial).gprs .rcx =
        (extractionStates initial).2.1.gprs .rcx + 1 by rfl]
    rw [extractionAfterDiv_preservesGpr initial .rcx (by decide) (by decide)]
  · rw [show (extractionFinal backDisp initial).rsp =
        (extractionStates initial).2.1.rsp - 8 by rfl]
    change (extractionStates initial).2.1.gprs .rsp - 8 = initial.gprs .rsp - 8
    rw [extractionAfterDiv_preservesGpr initial .rsp (by decide) (by decide)]
  · rw [show (extractionFinal backDisp initial).memory =
        X86_64Mem.write .w64 ((extractionStates initial).2.1.rsp - 8)
          ((extractionStates initial).2.1.gprs .rdx + 0x30)
          (extractionStates initial).2.1.memory by rfl]
    rw [extractionAfterDiv_preservesMemory initial]
    rw [extractionAfterDiv_remainder initial pre.divisorTen]
    change X86_64Mem.write .w64
      ((extractionStates initial).2.1.gprs .rsp - 8)
      (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 48) initial.memory =
      X86_64Mem.write .w64 (initial.gprs .rsp - 8)
      (UInt64.ofNat ((initial.gprs .rax).toNat % 10) + 48) initial.memory
    rw [extractionAfterDiv_preservesGpr initial .rsp (by decide) (by decide)]
  · rw [show (extractionFinal backDisp initial).gprs .r12 =
        (extractionStates initial).2.1.gprs .r12 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r12 (by decide) (by decide)
  · rw [show (extractionFinal backDisp initial).gprs .r13 =
        (extractionStates initial).2.1.gprs .r13 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r13 (by decide) (by decide)
  · rw [show (extractionFinal backDisp initial).gprs .r14 =
        (extractionStates initial).2.1.gprs .r14 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r14 (by decide) (by decide)
  · rw [show (extractionFinal backDisp initial).gprs .r15 =
        (extractionStates initial).2.1.gprs .r15 by rfl]
    exact extractionAfterDiv_preservesGpr initial .r15 (by decide) (by decide)
  · exact safe.branchSafe

theorem writePassEffect (backDisp : UInt8) (stackUpper bufferLimit : UInt64)
    (initial : X86_64MachineState) (_pre : WriteSafety stackUpper bufferLimit initial)
    (safe : WriteExecutionSafety backDisp initial) :
    WritePassEffect backDisp initial (writeFinal backDisp initial) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact safe.branchSafe

/-- Any caller-selected byte outside the exact pushed word is preserved. The no-wrap premise is
the memory hook's real range law, not an informal stack-frame assertion. -/
theorem ExtractionPassEffect.preservesMemoryAt {backDisp : UInt8}
    {initial final : X86_64MachineState}
    (effect : ExtractionPassEffect backDisp initial final) (address : UInt64)
    (noWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (outside : address.toNat < (initial.rsp - 8).toNat ∨
      (initial.rsp - 8).toNat + 8 ≤ address.toNat) :
    X86_64Mem.readByte final.memory address = X86_64Mem.readByte initial.memory address := by
  rw [effect.memory]
  exact X86_64Mem.readByte_write_disjoint .w64 _ _ _ _ noWrap outside

/-- Any caller-selected byte other than the exact output cursor is preserved by one write pass. -/
theorem WritePassEffect.preservesMemoryAt {backDisp : UInt8}
    {initial final : X86_64MachineState}
    (effect : WritePassEffect backDisp initial final) (address : UInt64)
    (noWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (outside : address.toNat < (initial.gprs .rdi).toNat ∨
      (initial.gprs .rdi).toNat + 1 ≤ address.toNat) :
    X86_64Mem.readByte final.memory address = X86_64Mem.readByte initial.memory address := by
  rw [effect.memory]
  exact X86_64Mem.readByte_write_disjoint .w8 _ _ _ _ noWrap outside

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- The byte observation made by a decimal caller.  This is intentionally a finite list, rather
than an equality of whole memories: the formatter owns its scratch words and the requested
output interval, while callers retain their own frame relation for everything else. -/
def decimalBytesAt (memory : X86_64Memory) (start : UInt64) (count : Nat) : List UInt8 :=
  (List.range count).map fun offset => X86_64Mem.readByte memory (start + UInt64.ofNat offset)

/-- A caller-chosen relation over the entry and return machine states.  The realization records
one of these relations exactly; it does not guess that a whole memory equality is a usable frame
when its selected output and scratch intervals are intentionally modified. -/
abbrev CallerFrame := X86_64MachineState → X86_64MachineState → Prop

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- The decimal schedule itself supplies the non-wrapping `RCX` increment side condition.  A
reachable extraction pass records the completed digit count, and a UInt64 has at most twenty
decimal digits; no target adapter may instead accept an independently asserted per-pass bound. -/
theorem countCanIncrement_of_decimalBound (value : UInt64) (completed : Nat)
    (state : X86_64MachineState) (counter : state.gprs .rcx = UInt64.ofNat completed)
    (within : completed < decimalDigitCount value) :
    (state.gprs .rcx).toNat < 0xFFFFFFFFFFFFFFFF := by
  rw [counter]
  have digitsBound := decimalDigitCount_le_twenty value
  have completedBound : completed ≤ 20 := by omega
  change completed % (2 ^ 64) < 0xFFFFFFFFFFFFFFFF
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/- REF: docs/STDLIB_FMT.md#55-bounded-uint64-decimal-contract -/
/-- Assemble an extraction safety certificate without making the target restate the `RCX`
non-wrap fact for every pass.  The completed schedule index and the shared UInt64 bound supply
that component. -/
theorem extractionSafety_of_decimalBound (value : UInt64) (completed : Nat)
    (stackLower : UInt64) (state : X86_64MachineState)
    (divisorTen : state.gprs .r10 = 10)
    (stack : StackPushCapacity stackLower state) (initialFault : state.fault = none)
    (counter : state.gprs .rcx = UInt64.ofNat completed)
    (within : completed < decimalDigitCount value) :
    ExtractionSafety stackLower state :=
  ⟨divisorTen, stack,
    countCanIncrement_of_decimalBound value completed state counter within, initialFault⟩

/-- One selected extraction pass is tied to the literal seven-instruction adapter, its indexed
placement/silence facts, and the architectural pass effect. -/
structure SelectedExtractionPass {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (backDisp : UInt8) (stackLower : UInt64)
    (initial : X86_64MachineState) : Prop where
  placement : ExtractionSelectedPlacement (Event := Event) selected indexed backDisp initial
  safety : ExtractionSafety stackLower initial
  executionSafety : ExtractionExecutionSafety backDisp initial
  branch : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2 ∨
    ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2
  effect : ExtractionPassEffect backDisp initial (extractionFinal backDisp initial)

namespace SelectedExtractionPass

theorem selectedPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8} {stackLower : UInt64}
    {initial : X86_64MachineState} {eventsRev : List Event}
    (pass : SelectedExtractionPass (Event := Event) selected indexed backDisp stackLower initial) :
    ProductionPrefix.SelectedPrefix selected indexed 7 initial eventsRev (extractionFinal backDisp initial)
      eventsRev [] := by
  rcases pass.branch with taken | fallthrough
  · exact extractionSelectedPrefixTaken pass.placement pass.safety pass.executionSafety taken
  · exact extractionSelectedPrefixFallthrough pass.placement pass.safety pass.executionSafety fallthrough

end SelectedExtractionPass

/-- One selected write pass is tied to the literal five-instruction adapter and exact output,
stack, selector, and silence evidence. -/
structure SelectedWritePass {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Gasm.Core.Address → X86_64MachineState → Bool)
    (indexed : List (UInt64 × X86_64Instr)) (backDisp : UInt8)
    (stackUpper outputLimit : UInt64) (initial : X86_64MachineState) : Prop where
  placement : WriteSelectedPlacement (Event := Event) selected indexed backDisp initial
  safety : WriteSafety stackUpper outputLimit initial
  executionSafety : WriteExecutionSafety backDisp initial
  branch : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2 ∨
    ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2
  effect : WritePassEffect backDisp initial (writeFinal backDisp initial)

namespace SelectedWritePass

theorem selectedPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8} {stackUpper outputLimit : UInt64}
    {initial : X86_64MachineState} {eventsRev : List Event}
    (pass : SelectedWritePass (Event := Event) selected indexed backDisp stackUpper outputLimit initial) :
    ProductionPrefix.SelectedPrefix selected indexed 5 initial eventsRev
      (writeFinal backDisp initial) eventsRev [] := by
  rcases pass.branch with taken | fallthrough
  · exact writeSelectedPrefixTaken pass.placement pass.safety pass.executionSafety taken
  · exact writeSelectedPrefixFallthrough pass.placement pass.safety pass.executionSafety fallthrough

end SelectedWritePass

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
    ⟨restoredRsp, advancedCursor, clearedCount, formatBytes, preservesR12, preservesR13,
      preservesR14, preservesR15, callerFramePreserved⟩
  exact ⟨extractionFuel + writeFuel, final, finalEventsRev,
    extractionEvents ++ writeEvents, extractionPrefix.append writePrefix,
    restoredRsp, advancedCursor, clearedCount, formatBytes, preservesR12, preservesR13,
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
    ⟨requiredFuel, final, finalEventsRev, emitted, selectedPrefix, restoredRsp, advancedCursor,
      clearedCount, formatBytes, preservesR12, preservesR13, preservesR14, preservesR15,
      callerFramePreserved⟩
  exact ⟨requiredFuel, final, finalEventsRev, emitted, selectedPrefix.toProductionPrefix,
    restoredRsp, advancedCursor, clearedCount, formatBytes, preservesR12, preservesR13,
    preservesR14, preservesR15, callerFramePreserved⟩

end UInt64DecimalScheduleRealization

end Gasm.Targets.X86_64.DecimalSchedule

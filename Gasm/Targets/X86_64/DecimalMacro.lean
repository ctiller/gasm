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

import Gasm.Targets.X86_64.CFGLinker
import Gasm.Targets.X86_64.DecimalSchedule

/-!
# Symbolic decimal-pass coordinates and final-link refinement

Decimal invariants should describe registers, flags, memory, faults, and effect state without
threading final linked RIP values through every arithmetic proof.  This module therefore gives the
two existing handwritten decimal passes nominal local control points.  A symbolic state contains a
control point and the RIP-independent part of an x86 state.  Only `LinkedLayout.materialize`
chooses a concrete RIP.

`LinkedLayout` is local linker evidence, not an artifact, execution, export, or `VerifiedProgram`
certificate.  It connects each selected symbolic instruction to one exact address, production
lookup, and the bytes of a caller-supplied linked text.  Relayout invalidates this evidence but not
an invariant stated over `MachineData`.

The current passes select one relative conditional branch.  Its taken and fallthrough refinements
are explicit below.  They select no instruction that reads RIP as data, no CALL (and hence no return
address), and no external call or syscall.  Adding any of those forms must add its corresponding
local semantic, ABI/return, interceptor/event, and obligation-transfer premises; this module does
not infer them from address coincidence.
-/

namespace Gasm.Targets.X86_64.DecimalMacro

open Gasm.Core
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule
open Gasm.Targets.X86_64.CFGLinker

/-- The part of an x86 state observed by the decimal data invariant.  RIP is deliberately absent:
it is a symbolic control coordinate until final linking. -/
structure MachineData where
  gprs : Reg64 → UInt64
  flags : UInt64
  memory : X86_64Memory
  stdinBuffer : ByteArray
  incomingRequests : List ByteArray
  fault : Option X86_64Fault

namespace MachineData

/-- Forget only concrete instruction placement. -/
def ofMachineState (state : X86_64MachineState) : MachineData where
  gprs := state.gprs
  flags := state.flags
  memory := state.memory
  stdinBuffer := state.stdinBuffer
  incomingRequests := state.incomingRequests
  fault := state.fault

/-- Materialize RIP at the one boundary that connects symbolic simulation to linked text. -/
def atRip (data : MachineData) (rip : UInt64) : X86_64MachineState where
  rip := rip
  gprs := data.gprs
  flags := data.flags
  memory := data.memory
  stdinBuffer := data.stdinBuffer
  incomingRequests := data.incomingRequests
  fault := data.fault

@[simp] theorem ofMachineState_atRip (data : MachineData) (rip : UInt64) :
    ofMachineState (data.atRip rip) = data := rfl

@[simp] theorem atRip_rip (data : MachineData) (rip : UInt64) : (data.atRip rip).rip = rip := rfl

/-- Forgetting and rematerializing the original RIP reconstructs the complete machine state. -/
@[simp] theorem atRip_ofMachineState (state : X86_64MachineState) :
    (ofMachineState state).atRip state.rip = state := rfl

end MachineData

/-- A local state whose control identity is nominal and whose machine payload has no concrete RIP. -/
structure SymbolicState (Point : Type) where
  point : Point
  data : MachineData

/-- Coordinates of the seven selected instructions and the fallthrough boundary of extraction. -/
inductive ExtractionPoint where
  | clearHigh | divide | ascii | push | increment | compare | branch | exit
  deriving DecidableEq, Repr

/-- Coordinates of the five selected instructions and the fallthrough boundary of writing. -/
inductive WritePoint where
  | pop | store | advance | decrement | branch | exit
  deriving DecidableEq, Repr

/-- Exact instruction selected at an extraction coordinate.  `exit` is a control boundary, not an
instruction. -/
def extractionInstruction (backDisp : UInt8) : ExtractionPoint → Option X86_64Instr
  | .clearHigh => some (xor_r32 .edx .edx)
  | .divide => some (div_r64 .r10)
  | .ascii => some (add_r64_imm8 .rdx 0x30)
  | .push => some (push_r64 .rdx)
  | .increment => some (add_r64_imm8 .rcx 1)
  | .compare => some (cmp_r64_imm8 .rax 0)
  | .branch => some (jne_rel8 backDisp)
  | .exit => none

/-- Exact instruction selected at a write coordinate. -/
def writeInstruction (backDisp : UInt8) : WritePoint → Option X86_64Instr
  | .pop => some (pop_r64 .rdx)
  | .store => some (mov_mem8 .rdi .rdx)
  | .advance => some (add_r64_imm8 .rdi 1)
  | .decrement => some (sub_r64_imm8 .rcx 1)
  | .branch => some (jne_rel8 backDisp)
  | .exit => none

/-- One final-link refinement from nominal local points to exact text addresses.  It is indexed by
the actual linked text and production instruction index, so changing placement or bytes requires a
new refinement while symbolic invariant proofs remain unchanged. -/
structure LinkedLayout (Point : Type)
    (text : LinkedText) (indexed : List (UInt64 × X86_64Instr))
    (instruction : Point → Option X86_64Instr) where
  address : Point → UInt64
  addressInjective : Function.Injective address
  index_eq : indexed = text.indexed
  textNoWrap : text.base.toNat + encodedSpan text.instructions ≤ 2 ^ 64
  lookup : ∀ point selected, instruction point = some selected →
    instructionAtRipIndexed indexed (address point) = some selected
  bytes : ∀ point selected, instruction point = some selected →
    text.bytesAt (address point) (X86_64Instruction.encode selected).size =
      X86_64Instruction.encode selected
  noWrap : ∀ point selected, instruction point = some selected →
    (address point).toNat + (X86_64Instruction.encode selected).size ≤ 2 ^ 64
  covered : ∀ point selected, instruction point = some selected →
    text.base.toNat ≤ (address point).toNat ∧
      (address point).toNat + (X86_64Instruction.encode selected).size ≤
        text.base.toNat + encodedSpan text.instructions

namespace LinkedLayout

/-- Materialize a symbolic state at its exact linked address. -/
def materialize {Point : Type}
    {text : LinkedText} {indexed : List (UInt64 × X86_64Instr)}
    {instruction : Point → Option X86_64Instr}
    (layout : LinkedLayout Point text indexed instruction) (state : SymbolicState Point) :
    X86_64MachineState :=
  state.data.atRip (layout.address state.point)

/-- Production lookup resolves the exact instruction attached to a materialized coordinate. -/
theorem lookup_materialize {Point : Type}
    {text : LinkedText} {indexed : List (UInt64 × X86_64Instr)}
    {instruction : Point → Option X86_64Instr}
    (layout : LinkedLayout Point text indexed instruction) (state : SymbolicState Point)
    (selected : X86_64Instr) (atPoint : instruction state.point = some selected) :
    instructionAtRipIndexed indexed (layout.materialize state).rip = some selected := by
  change instructionAtRipIndexed indexed (layout.address state.point) = some selected
  exact layout.lookup state.point selected atPoint

/-- Materialization changes no data-invariant field. -/
@[simp] theorem data_materialize {Point : Type}
    {text : LinkedText} {indexed : List (UInt64 × X86_64Instr)}
    {instruction : Point → Option X86_64Instr}
    (layout : LinkedLayout Point text indexed instruction) (state : SymbolicState Point) :
    MachineData.ofMachineState (layout.materialize state) = state.data := rfl

end LinkedLayout

/-- Final-link evidence for extraction's one selected relative branch. -/
structure ExtractionLinkedLayout (text : LinkedText)
    (indexed : List (UInt64 × X86_64Instr)) (backDisp : UInt8)
    extends LinkedLayout ExtractionPoint text indexed (extractionInstruction backDisp) where
  clearHighNext : address .clearHigh + 2 = address .divide
  divideNext : address .divide + 3 = address .ascii
  asciiNext : address .ascii + 4 = address .push
  pushNext : address .push + 1 = address .increment
  incrementNext : address .increment + 4 = address .compare
  compareNext : address .compare + 4 = address .branch
  takenTarget : address .branch + 2 + signExtend8To64 backDisp = address .clearHigh
  falseFallthrough : address .branch + 2 = address .exit

/-- Final-link evidence for writing's one selected relative branch. -/
structure WriteLinkedLayout (text : LinkedText)
    (indexed : List (UInt64 × X86_64Instr)) (backDisp : UInt8)
    extends LinkedLayout WritePoint text indexed (writeInstruction backDisp) where
  popNext : address .pop + 1 = address .store
  storeNext : address .store + 2 = address .advance
  advanceNext : address .advance + 4 = address .decrement
  decrementNext : address .decrement + 4 = address .branch
  takenTarget : address .branch + 2 + signExtend8To64 backDisp = address .pop
  falseFallthrough : address .branch + 2 = address .exit

/-- State-dependent runtime facts left after linked lookup and relative placement are discharged
once.  A platform derives these facts from its selected-address and interceptor policy at states
reachable from the decimal invariant. -/
structure ExtractionRuntimeEvidence {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Address → X86_64MachineState → Bool) (backDisp : UInt8)
    (initial : X86_64MachineState) : Prop where
  silentXor : interceptor.interceptCall (extractionStates initial).1.rip
    (extractionStates initial).1 = none
  silentDiv : interceptor.interceptCall (extractionStates initial).2.1.rip
    (extractionStates initial).2.1 = none
  silentAscii : interceptor.interceptCall (extractionStates initial).2.2.1.rip
    (extractionStates initial).2.2.1 = none
  silentPush : interceptor.interceptCall (extractionStates initial).2.2.2.1.rip
    (extractionStates initial).2.2.2.1 = none
  silentCount : interceptor.interceptCall (extractionStates initial).2.2.2.2.1.rip
    (extractionStates initial).2.2.2.2.1 = none
  silentCmp : interceptor.interceptCall (extractionStates initial).2.2.2.2.2.rip
    (extractionStates initial).2.2.2.2.2 = none
  silentBranch : interceptor.interceptCall
    (X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2).rip
    (X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2) = none
  selectedXor : selected (extractionStates initial).1.rip (extractionStates initial).1 = true
  selectedDiv : selected (extractionStates initial).2.1.rip (extractionStates initial).2.1 = true
  selectedAscii : selected (extractionStates initial).2.2.1.rip
    (extractionStates initial).2.2.1 = true
  selectedPush : selected (extractionStates initial).2.2.2.1.rip
    (extractionStates initial).2.2.2.1 = true
  selectedCount : selected (extractionStates initial).2.2.2.2.1.rip
    (extractionStates initial).2.2.2.2.1 = true
  selectedCmp : selected (extractionStates initial).2.2.2.2.2.rip
    (extractionStates initial).2.2.2.2.2 = true
  selectedBranch : selected (X86_64Instruction.step (jne_rel8 backDisp)
    (extractionStates initial).2.2.2.2.2).rip
    (X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2) = true

/-- Runtime-only facts for the reverse-write pass. -/
structure WriteRuntimeEvidence {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (selected : Address → X86_64MachineState → Bool) (backDisp : UInt8)
    (initial : X86_64MachineState) : Prop where
  silentPop : interceptor.interceptCall (writeStates initial).1.rip (writeStates initial).1 = none
  silentStore : interceptor.interceptCall (writeStates initial).2.1.rip
    (writeStates initial).2.1 = none
  silentCursor : interceptor.interceptCall (writeStates initial).2.2.1.rip
    (writeStates initial).2.2.1 = none
  silentCount : interceptor.interceptCall (writeStates initial).2.2.2.rip
    (writeStates initial).2.2.2 = none
  silentBranch : interceptor.interceptCall
    (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2).rip
    (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2) = none
  selectedPop : selected (writeStates initial).1.rip (writeStates initial).1 = true
  selectedStore : selected (writeStates initial).2.1.rip (writeStates initial).2.1 = true
  selectedCursor : selected (writeStates initial).2.2.1.rip (writeStates initial).2.2.1 = true
  selectedCount : selected (writeStates initial).2.2.2.rip (writeStates initial).2.2.2 = true
  selectedBranch : selected (X86_64Instruction.step (jne_rel8 backDisp)
    (writeStates initial).2.2.2).rip
    (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2) = true

private theorem divFallthrough (state : X86_64MachineState)
    (safe : (X86_64Instruction.step (div_r64 .r10) state).fault = none) :
    (X86_64Instruction.step (div_r64 .r10) state).rip = state.rip + 3 := by
  let core : X86_64MachineState :=
    { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).fault = none at safe
  change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
    { divisor := .r10 } core).rip = state.rip + 3
  simp only [X86_64Instruction.step] at safe ⊢
  split at safe
  · contradiction
  · rename_i hnonzero
    split at safe
    · contradiction
    · rename_i hfits
      simp [hnonzero, hfits, core]

namespace ExtractionLinkedLayout

/-- The symbolic successor equations and target-owned runtime facts construct the accepted
state-indexed placement used by `DecimalSchedule`; no consumer re-proves artifact lookup. -/
theorem toSelectedPlacement {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Address → X86_64MachineState → Bool} {text : LinkedText}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    (layout : ExtractionLinkedLayout text indexed backDisp)
    (initial : X86_64MachineState)
    (entry : initial.rip = layout.address .clearHigh)
    (safe : ExtractionExecutionSafety backDisp initial)
    (runtime : ExtractionRuntimeEvidence (Event := Event) selected backDisp initial) :
    ExtractionSelectedPlacement (Event := Event) selected indexed backDisp initial := by
  have h1 : (extractionStates initial).1.rip = layout.address .divide := by
    rw [show (extractionStates initial).1.rip = initial.rip + 2 by rfl, entry,
      layout.clearHighNext]
  have h2 : (extractionStates initial).2.1.rip = layout.address .ascii := by
    have stepRip := divFallthrough (extractionStates initial).1 safe.divSafe
    change (X86_64Instruction.step (div_r64 .r10) (extractionStates initial).1).rip =
      layout.address .ascii
    rw [stepRip, h1, layout.divideNext]
  have h3 : (extractionStates initial).2.2.1.rip = layout.address .push := by
    rw [show (extractionStates initial).2.2.1.rip =
      (extractionStates initial).2.1.rip + 4 by rfl, h2, layout.asciiNext]
  have h4 : (extractionStates initial).2.2.2.1.rip = layout.address .increment := by
    rw [show (extractionStates initial).2.2.2.1.rip =
      (extractionStates initial).2.2.1.rip + 1 by rfl, h3, layout.pushNext]
  have h5 : (extractionStates initial).2.2.2.2.1.rip = layout.address .compare := by
    rw [show (extractionStates initial).2.2.2.2.1.rip =
      (extractionStates initial).2.2.2.1.rip + 4 by rfl, h4, layout.incrementNext]
  have h6 : (extractionStates initial).2.2.2.2.2.rip = layout.address .branch := by
    rw [show (extractionStates initial).2.2.2.2.2.rip =
      (extractionStates initial).2.2.2.2.1.rip + 4 by rfl, h5, layout.compareNext]
  refine {
    lookupXor := ?_, lookupDiv := ?_, lookupAscii := ?_, lookupPush := ?_,
    lookupCount := ?_, lookupCmp := ?_, lookupBranch := ?_,
    silentXor := runtime.silentXor, silentDiv := runtime.silentDiv,
    silentAscii := runtime.silentAscii, silentPush := runtime.silentPush,
    silentCount := runtime.silentCount, silentCmp := runtime.silentCmp,
    silentBranch := runtime.silentBranch, backTarget := ?_,
    selectedXor := runtime.selectedXor, selectedDiv := runtime.selectedDiv,
    selectedAscii := runtime.selectedAscii, selectedPush := runtime.selectedPush,
    selectedCount := runtime.selectedCount, selectedCmp := runtime.selectedCmp,
    selectedBranch := runtime.selectedBranch }
  · rw [entry]; exact layout.lookup .clearHigh _ rfl
  · rw [h1]; exact layout.lookup .divide _ rfl
  · rw [h2]; exact layout.lookup .ascii _ rfl
  · rw [h3]; exact layout.lookup .push _ rfl
  · rw [h4]; exact layout.lookup .increment _ rfl
  · rw [h5]; exact layout.lookup .compare _ rfl
  · rw [h6]; exact layout.lookup .branch _ rfl
  · rw [h6, entry]; exact layout.takenTarget

/-- Representative schedule consumer: linked symbolic placement and invariant-state runtime facts
produce the existing selected pass, including its architectural effect. -/
theorem toSelectedPass {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Address → X86_64MachineState → Bool} {text : LinkedText}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8} {stackLower : UInt64}
    (layout : ExtractionLinkedLayout text indexed backDisp)
    (initial : X86_64MachineState) (entry : initial.rip = layout.address .clearHigh)
    (safety : ExtractionSafety stackLower initial)
    (executionSafety : ExtractionExecutionSafety backDisp initial)
    (runtime : ExtractionRuntimeEvidence (Event := Event) selected backDisp initial)
    (branch : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2) :
    SelectedExtractionPass (Event := Event) selected indexed backDisp stackLower initial where
  placement := layout.toSelectedPlacement initial entry executionSafety runtime
  safety := safety
  executionSafety := executionSafety
  branch := branch
  effect := extractionPassEffect backDisp stackLower initial safety executionSafety

end ExtractionLinkedLayout

namespace WriteLinkedLayout

/-- Write-pass counterpart of `ExtractionLinkedLayout.toSelectedPlacement`. -/
theorem toSelectedPlacement {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Address → X86_64MachineState → Bool} {text : LinkedText}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    (layout : WriteLinkedLayout text indexed backDisp) (initial : X86_64MachineState)
    (entry : initial.rip = layout.address .pop)
    (runtime : WriteRuntimeEvidence (Event := Event) selected backDisp initial) :
    WriteSelectedPlacement (Event := Event) selected indexed backDisp initial := by
  have h1 : (writeStates initial).1.rip = layout.address .store := by
    rw [show (writeStates initial).1.rip = initial.rip + 1 by rfl, entry, layout.popNext]
  have h2 : (writeStates initial).2.1.rip = layout.address .advance := by
    rw [show (writeStates initial).2.1.rip = (writeStates initial).1.rip + 2 by rfl,
      h1, layout.storeNext]
  have h3 : (writeStates initial).2.2.1.rip = layout.address .decrement := by
    rw [show (writeStates initial).2.2.1.rip = (writeStates initial).2.1.rip + 4 by rfl,
      h2, layout.advanceNext]
  have h4 : (writeStates initial).2.2.2.rip = layout.address .branch := by
    rw [show (writeStates initial).2.2.2.rip = (writeStates initial).2.2.1.rip + 4 by rfl,
      h3, layout.decrementNext]
  refine {
    lookupPop := ?_, lookupStore := ?_, lookupCursor := ?_, lookupCount := ?_,
    lookupBranch := ?_, silentPop := runtime.silentPop, silentStore := runtime.silentStore,
    silentCursor := runtime.silentCursor, silentCount := runtime.silentCount,
    silentBranch := runtime.silentBranch, backTarget := ?_,
    selectedPop := runtime.selectedPop, selectedStore := runtime.selectedStore,
    selectedCursor := runtime.selectedCursor, selectedCount := runtime.selectedCount,
    selectedBranch := runtime.selectedBranch }
  · rw [entry]; exact layout.lookup .pop _ rfl
  · rw [h1]; exact layout.lookup .store _ rfl
  · rw [h2]; exact layout.lookup .advance _ rfl
  · rw [h3]; exact layout.lookup .decrement _ rfl
  · rw [h4]; exact layout.lookup .branch _ rfl
  · rw [h4, entry]; exact layout.takenTarget

/-- Representative write-side `DecimalSchedule` consumer. -/
theorem toSelectedPass {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {selected : Address → X86_64MachineState → Bool} {text : LinkedText}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {stackUpper outputLimit : UInt64}
    (layout : WriteLinkedLayout text indexed backDisp) (initial : X86_64MachineState)
    (entry : initial.rip = layout.address .pop)
    (safety : WriteSafety stackUpper outputLimit initial)
    (executionSafety : WriteExecutionSafety backDisp initial)
    (runtime : WriteRuntimeEvidence (Event := Event) selected backDisp initial)
    (branch : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2) :
    SelectedWritePass (Event := Event) selected indexed backDisp stackUpper outputLimit initial where
  placement := layout.toSelectedPlacement initial entry runtime
  safety := safety
  executionSafety := executionSafety
  branch := branch
  effect := writePassEffect backDisp stackUpper outputLimit initial safety executionSafety

end WriteLinkedLayout

end Gasm.Targets.X86_64.DecimalMacro

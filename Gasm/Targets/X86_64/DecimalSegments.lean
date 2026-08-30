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
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Div
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Pop
import Gasm.Targets.X86_64.Instructions.Push
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Xor

/-!
# Artifact-indexed x86-64 decimal loop passes

This module certifies the two instruction passes used by division/push/pop decimal formatters.
The certificates follow the actual production instruction index and `X86_64Instruction.step`;
they are not a detached evaluator, artifact certificate, or whole-program authority.

Placement is deliberately separate from the pass relation. Relayout replaces the lookup and
branch-target evidence while retaining the state relation. Stack and output bounds are explicit
selected-frame premises even though the current machine memory cell is total.
-/

namespace Gasm.Targets.X86_64.DecimalSegments

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/-- Exact instruction family selected for one quotient/remainder extraction pass. -/
def extractionCode (backDisp : UInt8) : List X86_64Instr := [
  xor_r32 .edx .edx,
  div_r64 .r10,
  add_r64_imm8 .rdx 0x30,
  push_r64 .rdx,
  add_r64_imm8 .rcx 1,
  cmp_r64_imm8 .rax 0,
  jne_rel8 backDisp
]

/-- Exact instruction family selected for one stack-pop/buffer-write pass. -/
def writeCode (backDisp : UInt8) : List X86_64Instr := [
  pop_r64 .rdx,
  mov_mem8 .rdi .rdx,
  add_r64_imm8 .rdi 1,
  sub_r64_imm8 .rcx 1,
  jne_rel8 backDisp
]

/-- The seven concrete states reached by the extraction pass before its final JNE. -/
def extractionStates (initial : X86_64MachineState) :
    X86_64MachineState × X86_64MachineState × X86_64MachineState ×
    X86_64MachineState × X86_64MachineState × X86_64MachineState :=
  let s1 := X86_64Instruction.step (xor_r32 .edx .edx) initial
  let s2 := X86_64Instruction.step (div_r64 .r10) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdx 0x30) s2
  let s4 := X86_64Instruction.step (push_r64 .rdx) s3
  let s5 := X86_64Instruction.step (add_r64_imm8 .rcx 1) s4
  let s6 := X86_64Instruction.step (cmp_r64_imm8 .rax 0) s5
  (s1, s2, s3, s4, s5, s6)

/-- The five concrete states reached by the write pass before its final JNE. -/
def writeStates (initial : X86_64MachineState) :
    X86_64MachineState × X86_64MachineState × X86_64MachineState × X86_64MachineState :=
  let s1 := X86_64Instruction.step (pop_r64 .rdx) initial
  let s2 := X86_64Instruction.step (mov_mem8 .rdi .rdx) s1
  let s3 := X86_64Instruction.step (add_r64_imm8 .rdi 1) s2
  let s4 := X86_64Instruction.step (sub_r64_imm8 .rcx 1) s3
  (s1, s2, s3, s4)

/-- Non-wrapping capacity for one selected stack push. -/
def StackPushCapacity (lower : UInt64) (state : X86_64MachineState) : Prop :=
  lower.toNat + 8 ≤ state.rsp.toNat

/-- Non-wrapping capacity for one selected stack pop. -/
def StackPopCapacity (upper : UInt64) (state : X86_64MachineState) : Prop :=
  state.rsp.toNat + 8 ≤ upper.toNat

/-- Non-wrapping capacity for one selected byte write. -/
def BufferWriteCapacity (limit : UInt64) (state : X86_64MachineState) : Prop :=
  (state.gprs .rdi).toNat < limit.toNat

/-- Exact safety premises for the selected DIV and PUSH pass. The quotient bound is explicit:
`DIV` faults both on zero divisors and on quotient overflow. -/
structure ExtractionSafety (stackLower : UInt64) (state : X86_64MachineState) : Prop where
  divisorTen : state.gprs .r10 = 10
  quotientFits : (state.gprs .rax).toNat / 10 ≤ 0xFFFFFFFFFFFFFFFF
  stack : StackPushCapacity stackLower state
  initialFault : state.fault = none

/-- Exact selected frame premises for the POP/store pass. -/
structure WriteSafety (stackUpper bufferLimit : UInt64) (state : X86_64MachineState) : Prop where
  stack : StackPopCapacity stackUpper state
  buffer : BufferWriteCapacity bufferLimit state
  countPositive : state.gprs .rcx ≠ 0
  initialFault : state.fault = none

/-- Artifact-indexed placement for one extraction pass. Every lookup is against the caller's
final instruction index at the state that the preceding concrete step actually reaches. -/
structure ExtractionPlacement {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (backDisp : UInt8)
    (initial : X86_64MachineState) : Prop where
  lookupXor : instructionAtRipIndexed indexed initial.rip = some (xor_r32 .edx .edx)
  lookupDiv : instructionAtRipIndexed indexed (extractionStates initial).1.rip = some (div_r64 .r10)
  lookupAscii : instructionAtRipIndexed indexed (extractionStates initial).2.1.rip =
    some (add_r64_imm8 .rdx 0x30)
  lookupPush : instructionAtRipIndexed indexed (extractionStates initial).2.2.1.rip =
    some (push_r64 .rdx)
  lookupCount : instructionAtRipIndexed indexed (extractionStates initial).2.2.2.1.rip =
    some (add_r64_imm8 .rcx 1)
  lookupCmp : instructionAtRipIndexed indexed (extractionStates initial).2.2.2.2.1.rip =
    some (cmp_r64_imm8 .rax 0)
  lookupBranch : instructionAtRipIndexed indexed (extractionStates initial).2.2.2.2.2.rip =
    some (jne_rel8 backDisp)
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
  backTarget : (extractionStates initial).2.2.2.2.2.rip + 2 + signExtend8To64 backDisp = initial.rip

/-- Artifact-indexed placement for one pop/write pass. -/
structure WritePlacement {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (backDisp : UInt8)
    (initial : X86_64MachineState) : Prop where
  lookupPop : instructionAtRipIndexed indexed initial.rip = some (pop_r64 .rdx)
  lookupStore : instructionAtRipIndexed indexed (writeStates initial).1.rip = some (mov_mem8 .rdi .rdx)
  lookupCursor : instructionAtRipIndexed indexed (writeStates initial).2.1.rip =
    some (add_r64_imm8 .rdi 1)
  lookupCount : instructionAtRipIndexed indexed (writeStates initial).2.2.1.rip =
    some (sub_r64_imm8 .rcx 1)
  lookupBranch : instructionAtRipIndexed indexed (writeStates initial).2.2.2.rip =
    some (jne_rel8 backDisp)
  silentPop : interceptor.interceptCall (writeStates initial).1.rip (writeStates initial).1 = none
  silentStore : interceptor.interceptCall (writeStates initial).2.1.rip (writeStates initial).2.1 = none
  silentCursor : interceptor.interceptCall (writeStates initial).2.2.1.rip
    (writeStates initial).2.2.1 = none
  silentCount : interceptor.interceptCall (writeStates initial).2.2.2.rip
    (writeStates initial).2.2.2 = none
  silentBranch : interceptor.interceptCall
    (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2).rip
    (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2) = none
  backTarget : (writeStates initial).2.2.2.rip + 2 + signExtend8To64 backDisp = initial.rip

/-- Exact nonfaulting facts for the concrete extraction trace. These are deliberately separate
from placement: a linked instruction can still be unsafe in a particular machine state. -/
structure ExtractionExecutionSafety (backDisp : UInt8)
    (initial : X86_64MachineState) : Prop where
  xorSafe : (extractionStates initial).1.fault = none
  divSafe : (extractionStates initial).2.1.fault = none
  asciiSafe : (extractionStates initial).2.2.1.fault = none
  pushSafe : (extractionStates initial).2.2.2.1.fault = none
  countSafe : (extractionStates initial).2.2.2.2.1.fault = none
  cmpSafe : (extractionStates initial).2.2.2.2.2.fault = none
  branchSafe :
    (X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2).fault = none

/-- Exact nonfaulting facts for the concrete pop/write trace. -/
structure WriteExecutionSafety (backDisp : UInt8)
    (initial : X86_64MachineState) : Prop where
  popSafe : (writeStates initial).1.fault = none
  storeSafe : (writeStates initial).2.1.fault = none
  cursorSafe : (writeStates initial).2.2.1.fault = none
  countSafe : (writeStates initial).2.2.2.fault = none
  branchSafe :
    (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2).fault = none

/-- Final concrete state of an extraction pass. -/
def extractionFinal (backDisp : UInt8) (initial : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2

/-- Final concrete state of a pop/write pass. -/
def writeFinal (backDisp : UInt8) (initial : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2

private theorem sequentialXorEdx : SequentialInstruction (xor_r32 .edx .edx) where
  encoding := .xor32 .edx .edx
  safeFallthrough := by intro _ _; rfl

private theorem divCoreFallthrough (state : X86_64MachineState)
    (safe : (X86_64Instruction.step (DivR64.mk .r10) state).fault = none) :
    (X86_64Instruction.step (DivR64.mk .r10) state).rip = state.rip + 3 := by
  simp only [X86_64Instruction.step] at safe ⊢
  split at safe
  · contradiction
  · rename_i hnonzero
    split at safe
    · contradiction
    · rename_i hfits
      simp [hnonzero, hfits]

private theorem sequentialDivR10 : SequentialInstruction (div_r64 .r10) where
  encoding := .div .r10
  safeFallthrough := by
    intro state safe
    let core : X86_64MachineState :=
      { state with stdinBuffer := ByteArray.empty, incomingRequests := [] }
    change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
      { divisor := .r10 } core).fault = none at safe
    change (@X86_64Instruction.step DivR64 instX86_64InstructionDivR64
      { divisor := .r10 } core).rip = state.rip + 3
    exact divCoreFallthrough core safe

private theorem sequentialAddRdxAscii : SequentialInstruction (add_r64_imm8 .rdx 0x30) where
  encoding := .addImm8 .rdx 0x30
  safeFallthrough := by intro _ _; rfl

private theorem sequentialPushRdx : SequentialInstruction (push_r64 .rdx) where
  encoding := .push .rdx
  safeFallthrough := by intro _ _; rfl

private theorem sequentialAddRcx : SequentialInstruction (add_r64_imm8 .rcx 1) where
  encoding := .addImm8 .rcx 1
  safeFallthrough := by intro _ _; rfl

private theorem sequentialCmpRax : SequentialInstruction (cmp_r64_imm8 .rax 0) where
  encoding := .compareImm8 .rax 0
  safeFallthrough := by intro _ _; rfl

private theorem sequentialPopRdx : SequentialInstruction (pop_r64 .rdx) where
  encoding := .pop .rdx
  safeFallthrough := by intro _ _; rfl

private theorem sequentialStoreDigit : SequentialInstruction (mov_mem8 .rdi .rdx) where
  encoding := .movMem8 .rdi .rdx
  safeFallthrough := by intro _ _; rfl

private theorem sequentialAddRdi : SequentialInstruction (add_r64_imm8 .rdi 1) where
  encoding := .addImm8 .rdi 1
  safeFallthrough := by intro _ _; rfl

private theorem sequentialSubRcx : SequentialInstruction (sub_r64_imm8 .rcx 1) where
  encoding := .subImm8 .rcx 1
  safeFallthrough := by intro _ _; rfl

/-- One taken extraction pass is seven literal steps of the production runner. -/
theorem extractionPrefixTaken {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {initial : X86_64MachineState} {eventsRev : List Event} {stackLower : UInt64}
    (placement : ExtractionPlacement (Event := Event) indexed backDisp initial)
    (_pre : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety backDisp initial)
    (taken : X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2) :
    ProductionPrefix indexed 7 initial eventsRev
      (X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2)
      eventsRev [] := by
  refine .ordinary sequentialXorEdx placement.lookupXor placement.silentXor safe.xorSafe ?_
  refine .ordinary sequentialDivR10 placement.lookupDiv placement.silentDiv safe.divSafe ?_
  refine .ordinary sequentialAddRdxAscii placement.lookupAscii placement.silentAscii safe.asciiSafe ?_
  refine .ordinary sequentialPushRdx placement.lookupPush placement.silentPush safe.pushSafe ?_
  refine .ordinary sequentialAddRcx placement.lookupCount placement.silentCount safe.countSafe ?_
  refine .ordinary sequentialCmpRax placement.lookupCmp placement.silentCmp safe.cmpSafe ?_
  refine .conditionalTaken (.jne8 backDisp) taken placement.lookupBranch
    placement.silentBranch safe.branchSafe ?_
  exact .nil _ _

/-- One terminating extraction pass is the same exact production trace with JNE fallthrough. -/
theorem extractionPrefixFallthrough {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {initial : X86_64MachineState} {eventsRev : List Event} {stackLower : UInt64}
    (placement : ExtractionPlacement (Event := Event) indexed backDisp initial)
    (_pre : ExtractionSafety stackLower initial)
    (safe : ExtractionExecutionSafety backDisp initial)
    (fallthrough : ¬ X86BranchCondition.notEqual.holds (extractionStates initial).2.2.2.2.2) :
    ProductionPrefix indexed 7 initial eventsRev
      (X86_64Instruction.step (jne_rel8 backDisp) (extractionStates initial).2.2.2.2.2)
      eventsRev [] := by
  refine .ordinary sequentialXorEdx placement.lookupXor placement.silentXor safe.xorSafe ?_
  refine .ordinary sequentialDivR10 placement.lookupDiv placement.silentDiv safe.divSafe ?_
  refine .ordinary sequentialAddRdxAscii placement.lookupAscii placement.silentAscii safe.asciiSafe ?_
  refine .ordinary sequentialPushRdx placement.lookupPush placement.silentPush safe.pushSafe ?_
  refine .ordinary sequentialAddRcx placement.lookupCount placement.silentCount safe.countSafe ?_
  refine .ordinary sequentialCmpRax placement.lookupCmp placement.silentCmp safe.cmpSafe ?_
  refine .conditionalFallthrough (.jne8 backDisp) fallthrough placement.lookupBranch
    placement.silentBranch safe.branchSafe ?_
  exact .nil _ _

/-- One continuing pop/write pass is five literal steps of the production runner. -/
theorem writePrefixTaken {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {initial : X86_64MachineState} {eventsRev : List Event}
    {stackUpper bufferLimit : UInt64}
    (placement : WritePlacement (Event := Event) indexed backDisp initial)
    (_pre : WriteSafety stackUpper bufferLimit initial)
    (safe : WriteExecutionSafety backDisp initial)
    (taken : X86BranchCondition.notEqual.holds (writeStates initial).2.2.2) :
    ProductionPrefix indexed 5 initial eventsRev
      (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2)
      eventsRev [] := by
  refine .ordinary sequentialPopRdx placement.lookupPop placement.silentPop safe.popSafe ?_
  refine .ordinary sequentialStoreDigit placement.lookupStore placement.silentStore safe.storeSafe ?_
  refine .ordinary sequentialAddRdi placement.lookupCursor placement.silentCursor safe.cursorSafe ?_
  refine .ordinary sequentialSubRcx placement.lookupCount placement.silentCount safe.countSafe ?_
  refine .conditionalTaken (.jne8 backDisp) taken placement.lookupBranch
    placement.silentBranch safe.branchSafe ?_
  exact .nil _ _

/-- One terminating pop/write pass is the same exact production trace with JNE fallthrough. -/
theorem writePrefixFallthrough {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {initial : X86_64MachineState} {eventsRev : List Event}
    {stackUpper bufferLimit : UInt64}
    (placement : WritePlacement (Event := Event) indexed backDisp initial)
    (_pre : WriteSafety stackUpper bufferLimit initial)
    (safe : WriteExecutionSafety backDisp initial)
    (fallthrough : ¬ X86BranchCondition.notEqual.holds (writeStates initial).2.2.2) :
    ProductionPrefix indexed 5 initial eventsRev
      (X86_64Instruction.step (jne_rel8 backDisp) (writeStates initial).2.2.2)
      eventsRev [] := by
  refine .ordinary sequentialPopRdx placement.lookupPop placement.silentPop safe.popSafe ?_
  refine .ordinary sequentialStoreDigit placement.lookupStore placement.silentStore safe.storeSafe ?_
  refine .ordinary sequentialAddRdi placement.lookupCursor placement.silentCursor safe.cursorSafe ?_
  refine .ordinary sequentialSubRcx placement.lookupCount placement.silentCount safe.countSafe ?_
  refine .conditionalFallthrough (.jne8 backDisp) fallthrough placement.lookupBranch
    placement.silentBranch safe.branchSafe ?_
  exact .nil _ _

/-- A too-small stack interval cannot satisfy a push-capacity premise. -/
theorem not_stackPushCapacity_of_lt {lower : UInt64} {state : X86_64MachineState}
    (small : state.rsp.toNat < lower.toNat + 8) : ¬ StackPushCapacity lower state := by
  intro capacity
  exact (Nat.not_lt_of_ge capacity) small

/-- A pop whose upper endpoint lies before the next stack pointer is rejected. -/
theorem not_stackPopCapacity_of_lt {upper : UInt64} {state : X86_64MachineState}
    (small : upper.toNat < state.rsp.toNat + 8) : ¬ StackPopCapacity upper state := by
  intro capacity
  exact (Nat.not_lt_of_ge capacity) small

/-- A cursor at or beyond its selected output limit is rejected. -/
theorem not_bufferWriteCapacity_of_ge {limit : UInt64} {state : X86_64MachineState}
    (outside : limit.toNat ≤ (state.gprs .rdi).toNat) : ¬ BufferWriteCapacity limit state := by
  intro capacity
  exact (Nat.not_lt_of_ge outside) capacity

/-- A placement with the wrong encoded back edge cannot construct the selected pass. -/
theorem noExtractionPlacement_of_badTarget {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {initial : X86_64MachineState}
    (bad : (extractionStates initial).2.2.2.2.2.rip + 2 + signExtend8To64 backDisp ≠ initial.rip) :
    ¬ ExtractionPlacement (Event := Event) indexed backDisp initial := by
  intro placement
  exact bad placement.backTarget

/-- The analogous negative control for a detached/wrong pop-write back edge. -/
theorem noWritePlacement_of_badTarget {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {initial : X86_64MachineState}
    (bad : (writeStates initial).2.2.2.rip + 2 + signExtend8To64 backDisp ≠ initial.rip) :
    ¬ WritePlacement (Event := Event) indexed backDisp initial := by
  intro placement
  exact bad placement.backTarget

namespace Fixture

inductive Event

@[instance_reducible] private def silentInterceptor : ExternalCallInterceptor X86_64 Event where
  interceptCall := fun _ _ => none

local instance : ExternalCallInterceptor X86_64 Event := silentInterceptor

def extractionInitial : X86_64MachineState :=
  { (((((default : X86_64MachineState).setGpr64 .rax 123).setGpr64 .r10 10).setGpr64
      .rcx 0).setGpr64 .rsp 0x1000).setGpr64 .rdi 0x2000 with rip := 0 }

def extractionIndexed : List (UInt64 × X86_64Instr) :=
  indexInstructions 0 (extractionCode 0xEC)

theorem extractionSafetyFixture : ExtractionSafety 0 extractionInitial := by
  constructor
  · rfl
  · decide
  · change 8 ≤ 4096
    omega
  · rfl

theorem extractionExecutionSafetyFixture : ExtractionExecutionSafety 0xEC extractionInitial := by
  constructor <;> rfl

theorem extractionPlacementFixture :
    ExtractionPlacement (Event := Event) extractionIndexed 0xEC extractionInitial := by
  constructor <;> rfl

def writeInitial : X86_64MachineState :=
  { ((((default : X86_64MachineState).setGpr64 .rsp 0x1000).setGpr64 .rdi 0x2000).setGpr64
      .rcx 1).write64 0x1000 0x35 with rip := 0 }

def writeIndexed : List (UInt64 × X86_64Instr) :=
  indexInstructions 0 (writeCode 0xF3)

theorem writeSafetyFixture : WriteSafety 0x1008 0x2001 writeInitial := by
  constructor
  · change 4096 + 8 ≤ 4104
    omega
  · change 8192 < 8193
    omega
  · decide
  · rfl

theorem writeExecutionSafetyFixture : WriteExecutionSafety 0xF3 writeInitial := by
  constructor <;> rfl

theorem writePlacementFixture :
    WritePlacement (Event := Event) writeIndexed 0xF3 writeInitial := by
  constructor <;> rfl

end Fixture

end Gasm.Targets.X86_64.DecimalSegments

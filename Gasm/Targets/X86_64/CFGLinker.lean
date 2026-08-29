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

import Gasm.Core.CFGBuilder
import Gasm.Targets.X86_64.CFGBridge
import Gasm.Targets.X86_64.Decoder

namespace Gasm.Targets.X86_64.CFGLinker

open Gasm.Core
open Gasm.Core.CFGBuilder
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Serialize exactly the instruction stream represented by a linked text image. -/
def encodeText (instructions : List X86_64Instr) : ByteArray :=
  instructions.foldl (fun bytes instruction =>
    bytes ++ X86_64Instruction.encode instruction) ByteArray.empty

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- A concrete text image, before any claim that it is a complete executable artifact. -/
structure LinkedText where
  base : UInt64
  instructions : List X86_64Instr

namespace LinkedText

def indexed (text : LinkedText) : List (UInt64 × X86_64Instr) :=
  indexInstructions text.base text.instructions

def bytes (text : LinkedText) : ByteArray :=
  encodeText text.instructions

def bytesAt (text : LinkedText) (address : UInt64) (size : Nat) : ByteArray :=
  text.bytes.extract (address.toNat - text.base.toNat)
    (address.toNat - text.base.toNat + size)

end LinkedText

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Sum of encoded instruction sizes, used for half-open block ranges and relocation sites. -/
def encodedSpan (instructions : List X86_64Instr) : Nat :=
  instructions.foldl (fun size instruction =>
    size + (X86_64Instruction.encode instruction).size) 0

/-- Existing emitted-block evidence specialized to one linked text image. `Unit` is only the
    universe-small carrier required by the older bridge; the indexed text is captured exactly. -/
abbrev TextEmittedBlock {BlockId : Type} (text : LinkedText)
    (block : BasicBlock X86_64 BlockId) : Type 1 :=
  EmittedBasicBlock (Artifact := Unit) (BlockId := BlockId)
    (fun _ : Unit => text.indexed) () block

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Two half-open encoded ranges do not overlap. -/
def RangesDisjoint (leftStart : UInt64) (leftSize : Nat)
    (rightStart : UInt64) (rightSize : Nat) : Prop :=
  leftStart.toNat + leftSize ≤ rightStart.toNat ∨
    rightStart.toNat + rightSize ≤ leftStart.toNat

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Target/linker-owned placement of every exact block definition in a closed CFG. Besides unique
    starts, it requires non-overlapping encoded ranges, an artifact-global instruction lookup law,
    and membership of every block's exact instruction boundaries in the final linked index. -/
structure ClosedCFGLayout {BlockId : Type}
    (graph : TypedControlFlowGraph X86_64 BlockId) (text : LinkedText) where
  alignment : Nat
  alignmentPositive : 0 < alignment
  textNoWrap : text.base.toNat + encodedSpan text.instructions ≤ 2 ^ 64
  indexedLayout : IndexedLayoutCertificate text.indexed
  emitted : (block : BasicBlock X86_64 BlockId) → block ∈ graph.blocks →
    TextEmittedBlock text block
  aligned : ∀ (block : BasicBlock X86_64 BlockId) (member : block ∈ graph.blocks),
    (emitted block member).bodyBase.toNat % alignment = 0
  rangeCovered : ∀ (block : BasicBlock X86_64 BlockId) (member : block ∈ graph.blocks),
    text.base.toNat ≤ (emitted block member).bodyBase.toNat ∧
      (emitted block member).bodyBase.toNat +
        encodedSpan ((emitted block member).bodyCode ++
          [(emitted block member).terminatorInstruction]) ≤
        text.base.toNat + encodedSpan text.instructions
  uniqueStarts : ∀ (left right : BasicBlock X86_64 BlockId)
      (leftMember : left ∈ graph.blocks) (rightMember : right ∈ graph.blocks),
    (emitted left leftMember).bodyBase = (emitted right rightMember).bodyBase →
      left.entry.id = right.entry.id
  rangesDisjoint : ∀ (left right : BasicBlock X86_64 BlockId)
      (leftMember : left ∈ graph.blocks) (rightMember : right ∈ graph.blocks),
    left.entry.id ≠ right.entry.id →
      RangesDisjoint (emitted left leftMember).bodyBase
        (encodedSpan ((emitted left leftMember).bodyCode ++
          [(emitted left leftMember).terminatorInstruction]))
        (emitted right rightMember).bodyBase
        (encodedSpan ((emitted right rightMember).bodyCode ++
          [(emitted right rightMember).terminatorInstruction]))
  boundariesIncluded : ∀ (block : BasicBlock X86_64 BlockId)
      (member : block ∈ graph.blocks) (entry : UInt64 × X86_64Instr),
    entry ∈ indexInstructions (emitted block member).bodyBase
      ((emitted block member).bodyCode ++
        [(emitted block member).terminatorInstruction]) →
      entry ∈ text.indexed
  bytesAtBoundary : ∀ (block : BasicBlock X86_64 BlockId)
      (member : block ∈ graph.blocks) (before : List X86_64Instr)
      (instruction : X86_64Instr) (after : List X86_64Instr),
    (emitted block member).bodyCode ++
        [(emitted block member).terminatorInstruction] = before ++ instruction :: after →
      text.bytesAt
          ((emitted block member).bodyBase + instructionSpan before)
          (X86_64Instruction.encode instruction).size =
        X86_64Instruction.encode instruction

namespace ClosedCFGLayout

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Every certified local instruction boundary resolves through production indexed lookup. -/
theorem lookupBoundary {BlockId : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    (layout : ClosedCFGLayout graph text) (block : BasicBlock X86_64 BlockId)
    (member : block ∈ graph.blocks) (entry : UInt64 × X86_64Instr)
    (localMember : entry ∈ indexInstructions (layout.emitted block member).bodyBase
      ((layout.emitted block member).bodyCode ++
        [(layout.emitted block member).terminatorInstruction])) :
    instructionAtRipIndexed text.indexed entry.1 = some entry.2 :=
  layout.indexedLayout.resolves entry
    (layout.boundariesIncluded block member entry localMember)

end ClosedCFGLayout

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Link-time rejection is distinct from every runtime fault/outcome. -/
inductive Rel32LinkError where
  | zeroAlignment
  | targetMisaligned
  | sourceAddressWrap
  | displacementOutOfRange
  deriving DecidableEq, Repr

private def intToInt32 (value : Int) : Int32 :=
  if value ≥ 0 then Int32.ofNat value.toNat
  else -Int32.ofNat (-value).toNat

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Fallible rel32 selection. It rejects invalid alignment, a wrapped next-instruction address, and
    every mathematical displacement outside the signed 32-bit interval before conversion. -/
def checkedRel32 (alignment : Nat) (source target : UInt64) :
    Except Rel32LinkError Int32 :=
  if alignment = 0 then .error .zeroAlignment
  else if target.toNat % alignment ≠ 0 then .error .targetMisaligned
  else if source.toNat + 5 ≥ 2 ^ 64 then .error .sourceAddressWrap
  else
    let difference : Int := (target.toNat : Int) - (source.toNat + 5 : Nat)
    if difference < -(2 ^ 31 : Int) ∨ difference ≥ (2 ^ 31 : Int) then
      .error .displacementOutOfRange
    else
      .ok (intToInt32 difference)

example : checkedRel32 1 0x1000 0x1010 = .ok 11 := by rfl
example : checkedRel32 16 0x1003 0x1010 = .ok 8 := by rfl
example : checkedRel32 16 0x1000 0x1008 = .error .targetMisaligned := by rfl
example : checkedRel32 1 0 (0x80000005 : UInt64) = .error .displacementOutOfRange := by rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Relocation evidence imposed only when a direct symbolic JMP is selected. It binds the retained
    exact target definition, checked displacement, exact linked bytes, production decoder, source
    lookup, target instruction boundary, and concrete branch destination. -/
structure DirectJumpRelocation {BlockId ExitState : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    (layout : ClosedCFGLayout graph text) (exit : ComposedState X86_64 ExitState)
    (target : BlockRef X86_64 BlockId) (edge : BlockEdge (BlockId := BlockId) exit)
    (targetExact : edge.target = target.entry) where
  sourceBlock : BasicBlock X86_64 BlockId
  sourceMember : sourceBlock ∈ graph.blocks
  logicalState : ComposedState X86_64 sourceBlock.entry.State
  logicalAccepted : sourceBlock.entry.accepts logicalState
  selectedEdge : sourceBlock.body logicalState logicalAccepted =
    ⟨ExitState, exit, CpuTerminator.jmp edge⟩
  targetMember : target.Interned graph.blocks
  sourceAddress : UInt64
  sourceAtTerminator : sourceAddress =
    (layout.emitted sourceBlock sourceMember).bodyBase +
      instructionSpan (layout.emitted sourceBlock sourceMember).bodyCode
  displacement : Int32
  checked : checkedRel32 layout.alignment sourceAddress
    (layout.emitted target.definition targetMember).bodyBase = .ok displacement
  emittedInstruction :
    (layout.emitted sourceBlock sourceMember).terminatorInstruction =
      jmp_rel32 displacement
  decoded : decodeX86_64Instr (text.bytesAt sourceAddress 5) 0 =
    .ok (jmp_rel32 displacement, 5)
  targetInstruction : X86_64Instr
  targetSuffix : List X86_64Instr
  targetStartsWith :
    (layout.emitted target.definition targetMember).bodyCode ++
      [(layout.emitted target.definition targetMember).terminatorInstruction] =
        targetInstruction :: targetSuffix
  destination : ∀ state : X86_64MachineState, state.rip = sourceAddress →
    (X86_64Instruction.step (jmp_rel32 displacement) state).rip =
      (layout.emitted target.definition targetMember).bodyBase

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- The reusable connection delivered by a selected direct-JMP relocation. It deliberately states
    no whole-program termination, admissibility, host outcome, or runtime-fault claim. -/
structure DirectJumpConnection {BlockId ExitState : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    (layout : ClosedCFGLayout graph text)
    (exit : ComposedState X86_64 ExitState) (target : BlockRef X86_64 BlockId)
    (edge : BlockEdge (BlockId := BlockId) exit) where
  targetDefinition : target.definition ∈ graph.blocks
  targetEntry : edge.target = target.entry
  sourceBlock : BasicBlock X86_64 BlockId
  sourceMember : sourceBlock ∈ graph.blocks
  logicalState : ComposedState X86_64 sourceBlock.entry.State
  logicalAccepted : sourceBlock.entry.accepts logicalState
  selectedEdge : sourceBlock.body logicalState logicalAccepted =
    ⟨ExitState, exit, CpuTerminator.jmp edge⟩
  sourceAddress : UInt64
  sourcePlacement : sourceAddress =
    (layout.emitted sourceBlock sourceMember).bodyBase +
      instructionSpan (layout.emitted sourceBlock sourceMember).bodyCode
  targetAddress : UInt64
  targetPlacement : targetAddress =
    (layout.emitted target.definition targetDefinition).bodyBase
  displacement : Int32
  checked : ∃ alignment > 0,
    checkedRel32 alignment sourceAddress targetAddress = .ok displacement
  bytes : ByteArray
  bytesFromText : bytes = text.bytesAt sourceAddress 5
  exactBytes : bytes = X86_64Instruction.encode (jmp_rel32 displacement)
  decoded : decodeX86_64Instr bytes 0 = .ok (jmp_rel32 displacement, 5)
  sourceLookup : instructionAtRipIndexed text.indexed sourceAddress =
    some (jmp_rel32 displacement)
  targetInstruction : X86_64Instr
  targetLookup : instructionAtRipIndexed text.indexed targetAddress = some targetInstruction
  concreteDestination : ∀ state : X86_64MachineState, state.rip = sourceAddress →
    (X86_64Instruction.step (jmp_rel32 displacement) state).rip = targetAddress
  ghostWorldTransfer : JumpFramePreserved exit edge.targetState

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Exact symbolic-edge-to-linked-text theorem. Frontend CFG and edge proofs are reused unchanged;
    only `DirectJumpRelocation` must be regenerated after layout changes. -/
def DirectJumpRelocation.connect {BlockId ExitState : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    {layout : ClosedCFGLayout graph text} {exit : ComposedState X86_64 ExitState}
    {target : BlockRef X86_64 BlockId} {edge : BlockEdge (BlockId := BlockId) exit}
    {targetExact : edge.target = target.entry}
    (relocation : DirectJumpRelocation layout exit target edge targetExact) :
    DirectJumpConnection (graph := graph) (text := text) layout exit target edge where
  targetDefinition := relocation.targetMember
  targetEntry := targetExact
  sourceBlock := relocation.sourceBlock
  sourceMember := relocation.sourceMember
  logicalState := relocation.logicalState
  logicalAccepted := relocation.logicalAccepted
  selectedEdge := relocation.selectedEdge
  sourceAddress := relocation.sourceAddress
  sourcePlacement := relocation.sourceAtTerminator
  targetAddress := (layout.emitted target.definition relocation.targetMember).bodyBase
  targetPlacement := rfl
  displacement := relocation.displacement
  checked := ⟨layout.alignment, layout.alignmentPositive, relocation.checked⟩
  bytes := text.bytesAt relocation.sourceAddress 5
  bytesFromText := rfl
  exactBytes := by
    have bytesAt := layout.bytesAtBoundary relocation.sourceBlock relocation.sourceMember
      (layout.emitted relocation.sourceBlock relocation.sourceMember).bodyCode
      (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
      [] (by simp)
    rw [← relocation.sourceAtTerminator, relocation.emittedInstruction] at bytesAt
    change text.bytesAt relocation.sourceAddress 5 =
      X86_64Instruction.encode (jmp_rel32 relocation.displacement) at bytesAt
    exact bytesAt
  decoded := relocation.decoded
  sourceLookup := by
    have localMember := indexInstructions_prefix_mem
      (layout.emitted relocation.sourceBlock relocation.sourceMember).bodyBase
      ((layout.emitted relocation.sourceBlock relocation.sourceMember).bodyCode ++
        [(layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction])
      (layout.emitted relocation.sourceBlock relocation.sourceMember).bodyCode
      (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
      [] (by simp)
    have lookup := layout.lookupBoundary relocation.sourceBlock relocation.sourceMember _ localMember
    have lookup' : instructionAtRipIndexed text.indexed
        ((layout.emitted relocation.sourceBlock relocation.sourceMember).bodyBase +
          instructionSpan (layout.emitted relocation.sourceBlock relocation.sourceMember).bodyCode) =
        some (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction := by
      simpa only [Prod.fst, Prod.snd] using lookup
    rw [relocation.sourceAtTerminator]
    rw [relocation.emittedInstruction] at lookup'
    exact lookup'
  targetInstruction := relocation.targetInstruction
  targetLookup := by
    have localMember := indexInstructions_prefix_mem
      (layout.emitted target.definition relocation.targetMember).bodyBase
      ((layout.emitted target.definition relocation.targetMember).bodyCode ++
        [(layout.emitted target.definition relocation.targetMember).terminatorInstruction])
      [] relocation.targetInstruction relocation.targetSuffix relocation.targetStartsWith
    simpa [instructionSpan] using
      layout.lookupBoundary target.definition relocation.targetMember _ localMember
  concreteDestination := relocation.destination
  ghostWorldTransfer := edge.framePreserved

end Gasm.Targets.X86_64.CFGLinker

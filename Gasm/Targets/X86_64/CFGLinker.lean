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
/-- Size-aware fallible rel32 selection. Displacement is measured from the exact next RIP. It
    rejects invalid alignment, a wrapped next-instruction address, and every mathematical
    displacement outside the signed 32-bit interval before conversion. -/
def checkedRel32ForSize (instructionSize alignment : Nat) (source target : UInt64) :
    Except Rel32LinkError Int32 :=
  if alignment = 0 then .error .zeroAlignment
  else if target.toNat % alignment ≠ 0 then .error .targetMisaligned
  else if source.toNat + instructionSize ≥ 2 ^ 64 then .error .sourceAddressWrap
  else
    let difference : Int := (target.toNat : Int) - (source.toNat + instructionSize : Nat)
    if difference < -(2 ^ 31 : Int) ∨ difference ≥ (2 ^ 31 : Int) then
      .error .displacementOutOfRange
    else
      .ok (intToInt32 difference)

/- REF: docs/MACRO_ASSEMBLER.md#typed-direct-jump-linking -/
/-- Existing five-byte direct-JMP specialization. -/
def checkedRel32 (alignment : Nat) (source target : UInt64) :
    Except Rel32LinkError Int32 :=
  checkedRel32ForSize 5 alignment source target

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Six-byte near-JCC specialization. -/
def checkedNearJccRel32 (alignment : Nat) (source target : UInt64) :
    Except Rel32LinkError Int32 :=
  checkedRel32ForSize 6 alignment source target

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- A successful size-aware check proves that its next RIP does not wrap. -/
theorem checkedRel32ForSize_nextRip_noWrap {instructionSize alignment : Nat}
    {source target : UInt64} {displacement : Int32}
    (checked : checkedRel32ForSize instructionSize alignment source target = .ok displacement) :
    source.toNat + instructionSize < 2 ^ 64 := by
  unfold checkedRel32ForSize at checked
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  split at checked
  · contradiction
  · omega

example : checkedRel32 1 0x1000 0x1010 = .ok 11 := by rfl
example : checkedRel32 16 0x1003 0x1010 = .ok 8 := by rfl
example : checkedRel32 16 0x1000 0x1008 = .error .targetMisaligned := by rfl
example : checkedRel32 1 0 (0x80000005 : UInt64) = .error .displacementOutOfRange := by rfl
example : checkedNearJccRel32 1 0x1000 0x1010 = .ok 10 := by rfl

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

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- The currently admitted single-instruction near-JCC encodings. Kinds for which the ISA module
    exposes only a short form return `none`; the linker must reject rather than silently narrow. -/
def nearJccInstruction : X86BranchCondition → Int32 → Option X86_64Instr
  | .equal, displacement => some (je_rel32 displacement)
  | .notEqual, displacement => some (jne_rel32 displacement)
  | .less, _ => none
  | .lessEqual, displacement => some (jle_rel32 displacement)
  | .greater, _ => none
  | .greaterEqual, displacement => some (jge_rel32 displacement)
  | .below, displacement => some (jb_rel32 displacement)
  | .above, displacement => some (ja_rel32 displacement)
  | .aboveOrEqual, displacement => some (jae_rel32 displacement)

example : nearJccInstruction .equal 7 = some (je_rel32 7) := rfl
example : nearJccInstruction .less 7 = none := rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Successful near selection is always one of the existing sealed target-owned conditional
    encodings; no frontend-defined instruction classification is accepted. -/
theorem nearJccInstruction_encoding {kind : X86BranchCondition} {displacement : Int32}
    {instruction : X86_64Instr}
    (selected : nearJccInstruction kind displacement = some instruction) :
    ConditionalJumpEncoding instruction kind := by
  cases kind <;> simp [nearJccInstruction] at selected
  all_goals subst instruction; constructor

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Every admitted near-JCC occupies exactly six bytes. -/
theorem nearJccInstruction_size {kind : X86BranchCondition} {displacement : Int32}
    {instruction : X86_64Instr}
    (selected : nearJccInstruction kind displacement = some instruction) :
    (X86_64Instruction.encode instruction).size = 6 := by
  cases kind <;> simp [nearJccInstruction] at selected
  all_goals subst instruction <;> rfl

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Linker evidence for the real one-instruction JCC shape: the true successor is encoded by one
    checked rel32 and the false successor is exactly the six-byte fallthrough. Both exact target
    definitions remain visible. -/
structure ConditionalJumpRelocation {BlockId ExitState : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    (layout : ClosedCFGLayout graph text) (exit : ComposedState X86_64 ExitState)
    (condition : ConditionCode X86_64)
    (targetTrue targetFalse : BlockRef X86_64 BlockId)
    (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine))
    (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine))
    (trueExact : edgeTrue.target = targetTrue.entry)
    (falseExact : edgeFalse.target = targetFalse.entry) where
  sourceBlock : BasicBlock X86_64 BlockId
  sourceMember : sourceBlock ∈ graph.blocks
  logicalState : ComposedState X86_64 sourceBlock.entry.State
  logicalAccepted : sourceBlock.entry.accepts logicalState
  selectedEdges : sourceBlock.body logicalState logicalAccepted =
    ⟨ExitState, exit, CpuTerminator.jcc condition edgeTrue edgeFalse⟩
  trueMember : targetTrue.Interned graph.blocks
  falseMember : targetFalse.Interned graph.blocks
  sourceAddress : UInt64
  sourceAtTerminator : sourceAddress =
    (layout.emitted sourceBlock sourceMember).bodyBase +
      instructionSpan (layout.emitted sourceBlock sourceMember).bodyCode
  kind : X86BranchCondition
  conditionAgreement : ∀ state : X86_64MachineState,
    condition.holds state ↔ kind.holds state
  displacement : Int32
  checkedTaken : checkedNearJccRel32 layout.alignment sourceAddress
    (layout.emitted targetTrue.definition trueMember).bodyBase = .ok displacement
  emittedInstruction : nearJccInstruction kind displacement =
    some (layout.emitted sourceBlock sourceMember).terminatorInstruction
  falseFallthrough : sourceAddress + 6 =
    (layout.emitted targetFalse.definition falseMember).bodyBase
  trueEdgeAtStart : edgeTrue.targetState.machine.rip =
    (layout.emitted targetTrue.definition trueMember).bodyBase
  falseEdgeAtStart : edgeFalse.targetState.machine.rip =
    (layout.emitted targetFalse.definition falseMember).bodyBase
  decoded : decodeX86_64Instr (text.bytesAt sourceAddress 6) 0 =
    .ok ((layout.emitted sourceBlock sourceMember).terminatorInstruction, 6)
  trueInstruction : X86_64Instr
  trueSuffix : List X86_64Instr
  trueStartsWith :
    (layout.emitted targetTrue.definition trueMember).bodyCode ++
      [(layout.emitted targetTrue.definition trueMember).terminatorInstruction] =
        trueInstruction :: trueSuffix
  falseInstruction : X86_64Instr
  falseSuffix : List X86_64Instr
  falseStartsWith :
    (layout.emitted targetFalse.definition falseMember).bodyCode ++
      [(layout.emitted targetFalse.definition falseMember).terminatorInstruction] =
        falseInstruction :: falseSuffix
  takenDestination : ∀ state : X86_64MachineState,
    state.rip = sourceAddress → kind.holds state →
      (X86_64Instruction.step
        (layout.emitted sourceBlock sourceMember).terminatorInstruction state).rip =
        (layout.emitted targetTrue.definition trueMember).bodyBase
  fallthroughDestination : ∀ state : X86_64MachineState,
    state.rip = sourceAddress → ¬ kind.holds state →
      (X86_64Instruction.step
        (layout.emitted sourceBlock sourceMember).terminatorInstruction state).rip =
        (layout.emitted targetFalse.definition falseMember).bodyBase

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Layout-indexed, non-authoritative result of connecting one selected symbolic JCC. -/
structure ConditionalJumpConnection {BlockId ExitState : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    (layout : ClosedCFGLayout graph text) (exit : ComposedState X86_64 ExitState)
    (condition : ConditionCode X86_64)
    (targetTrue targetFalse : BlockRef X86_64 BlockId)
    (edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine))
    (edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine)) where
  sourceBlock : BasicBlock X86_64 BlockId
  sourceMember : sourceBlock ∈ graph.blocks
  logicalState : ComposedState X86_64 sourceBlock.entry.State
  logicalAccepted : sourceBlock.entry.accepts logicalState
  selectedEdges : sourceBlock.body logicalState logicalAccepted =
    ⟨ExitState, exit, CpuTerminator.jcc condition edgeTrue edgeFalse⟩
  trueDefinition : targetTrue.definition ∈ graph.blocks
  falseDefinition : targetFalse.definition ∈ graph.blocks
  trueEntry : edgeTrue.target = targetTrue.entry
  falseEntry : edgeFalse.target = targetFalse.entry
  sourceAddress : UInt64
  sourcePlacement : sourceAddress =
    (layout.emitted sourceBlock sourceMember).bodyBase +
      instructionSpan (layout.emitted sourceBlock sourceMember).bodyCode
  trueAddress : UInt64
  truePlacement : trueAddress =
    (layout.emitted targetTrue.definition trueDefinition).bodyBase
  falseAddress : UInt64
  falsePlacement : falseAddress =
    (layout.emitted targetFalse.definition falseDefinition).bodyBase
  kind : X86BranchCondition
  conditionAgreement : ∀ state : X86_64MachineState,
    condition.holds state ↔ kind.holds state
  displacement : Int32
  checkedTaken : checkedNearJccRel32 layout.alignment sourceAddress trueAddress = .ok displacement
  sourceNextNoWrap : sourceAddress.toNat + 6 < 2 ^ 64
  falseFallthrough : sourceAddress + 6 = falseAddress
  trueEdgeAtStart : edgeTrue.targetState.machine.rip = trueAddress
  falseEdgeAtStart : edgeFalse.targetState.machine.rip = falseAddress
  instruction : X86_64Instr
  encoding : ConditionalJumpEncoding instruction kind
  bytes : ByteArray
  bytesFromText : bytes = text.bytesAt sourceAddress 6
  exactBytes : bytes = X86_64Instruction.encode instruction
  decoded : decodeX86_64Instr bytes 0 = .ok (instruction, 6)
  sourceLookup : instructionAtRipIndexed text.indexed sourceAddress = some instruction
  trueInstruction : X86_64Instr
  trueLookup : instructionAtRipIndexed text.indexed trueAddress = some trueInstruction
  falseInstruction : X86_64Instr
  falseLookup : instructionAtRipIndexed text.indexed falseAddress = some falseInstruction
  takenDestination : ∀ state : X86_64MachineState,
    state.rip = sourceAddress → kind.holds state →
      (X86_64Instruction.step instruction state).rip = trueAddress
  fallthroughDestination : ∀ state : X86_64MachineState,
    state.rip = sourceAddress → ¬ kind.holds state →
      (X86_64Instruction.step instruction state).rip = falseAddress

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Connect the selected logical JCC to one taken rel32 and its exact false fallthrough. -/
def ConditionalJumpRelocation.connect {BlockId ExitState : Type}
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    {layout : ClosedCFGLayout graph text} {exit : ComposedState X86_64 ExitState}
    {condition : ConditionCode X86_64}
    {targetTrue targetFalse : BlockRef X86_64 BlockId}
    {edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine)}
    {edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine)}
    {trueExact : edgeTrue.target = targetTrue.entry}
    {falseExact : edgeFalse.target = targetFalse.entry}
    (relocation : ConditionalJumpRelocation layout exit condition targetTrue targetFalse
      edgeTrue edgeFalse trueExact falseExact) :
    ConditionalJumpConnection layout exit condition targetTrue targetFalse edgeTrue edgeFalse where
  sourceBlock := relocation.sourceBlock
  sourceMember := relocation.sourceMember
  logicalState := relocation.logicalState
  logicalAccepted := relocation.logicalAccepted
  selectedEdges := relocation.selectedEdges
  trueDefinition := relocation.trueMember
  falseDefinition := relocation.falseMember
  trueEntry := trueExact
  falseEntry := falseExact
  sourceAddress := relocation.sourceAddress
  sourcePlacement := relocation.sourceAtTerminator
  trueAddress := (layout.emitted targetTrue.definition relocation.trueMember).bodyBase
  truePlacement := rfl
  falseAddress := (layout.emitted targetFalse.definition relocation.falseMember).bodyBase
  falsePlacement := rfl
  kind := relocation.kind
  conditionAgreement := relocation.conditionAgreement
  displacement := relocation.displacement
  checkedTaken := relocation.checkedTaken
  sourceNextNoWrap := checkedRel32ForSize_nextRip_noWrap relocation.checkedTaken
  falseFallthrough := relocation.falseFallthrough
  trueEdgeAtStart := relocation.trueEdgeAtStart
  falseEdgeAtStart := relocation.falseEdgeAtStart
  instruction := (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
  encoding := nearJccInstruction_encoding relocation.emittedInstruction
  bytes := text.bytesAt relocation.sourceAddress 6
  bytesFromText := rfl
  exactBytes := by
    have bytesAt := layout.bytesAtBoundary relocation.sourceBlock relocation.sourceMember
      (layout.emitted relocation.sourceBlock relocation.sourceMember).bodyCode
      (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
      [] (by simp)
    rw [← relocation.sourceAtTerminator] at bytesAt
    have size := nearJccInstruction_size relocation.emittedInstruction
    rw [size] at bytesAt
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
    rw [relocation.sourceAtTerminator]
    simpa only [Prod.fst, Prod.snd] using lookup
  trueInstruction := relocation.trueInstruction
  trueLookup := by
    have localMember := indexInstructions_prefix_mem
      (layout.emitted targetTrue.definition relocation.trueMember).bodyBase
      ((layout.emitted targetTrue.definition relocation.trueMember).bodyCode ++
        [(layout.emitted targetTrue.definition relocation.trueMember).terminatorInstruction])
      [] relocation.trueInstruction relocation.trueSuffix relocation.trueStartsWith
    simpa [instructionSpan] using
      layout.lookupBoundary targetTrue.definition relocation.trueMember _ localMember
  falseInstruction := relocation.falseInstruction
  falseLookup := by
    have localMember := indexInstructions_prefix_mem
      (layout.emitted targetFalse.definition relocation.falseMember).bodyBase
      ((layout.emitted targetFalse.definition relocation.falseMember).bodyCode ++
        [(layout.emitted targetFalse.definition relocation.falseMember).terminatorInstruction])
      [] relocation.falseInstruction relocation.falseSuffix relocation.falseStartsWith
    simpa [instructionSpan] using
      layout.lookupBoundary targetFalse.definition relocation.falseMember _ localMember
  takenDestination := relocation.takenDestination
  fallthroughDestination := relocation.fallthroughDestination

/- REF: docs/MACRO_ASSEMBLER.md#typed-conditional-branch-linking -/
/-- Supply only runtime-applicable premises to construct the existing one-step production
    terminator realization. Relocation contributes encoding and destinations; runtime silence,
    transition, safety, and the dynamic condition relation remain operational/profile evidence. -/
theorem ConditionalJumpRelocation.toTerminatorRealization {Event BlockId ExitState : Type}
    [ExternalCallInterceptor X86_64 Event]
    {graph : TypedControlFlowGraph X86_64 BlockId} {text : LinkedText}
    {layout : ClosedCFGLayout graph text} {exit : ComposedState X86_64 ExitState}
    {condition : ConditionCode X86_64}
    {targetTrue targetFalse : BlockRef X86_64 BlockId}
    {edgeTrue : ConditionalBlockEdge (BlockId := BlockId) exit
      (condition.holds exit.machine)}
    {edgeFalse : ConditionalBlockEdge (BlockId := BlockId) exit
      (¬ condition.holds exit.machine)}
    {trueExact : edgeTrue.target = targetTrue.entry}
    {falseExact : edgeFalse.target = targetFalse.entry}
    (relocation : ConditionalJumpRelocation layout exit condition targetTrue targetFalse
      edgeTrue edgeFalse trueExact falseExact)
    (before : X86_64MachineState) (beforeAtSource : before.rip = relocation.sourceAddress)
    (eventsRev eventsAfter : List Event)
    (transition : nativeOutcomeTransition
      (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
      before eventsRev = (exit.machine, eventsAfter))
    (runtimeSilent : RuntimeSilentAt (Event := Event)
      (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction before)
    (safe : exit.machine.fault = none)
    (conditionMatches : condition.holds exit.machine ↔ relocation.kind.holds before) :
    TerminatorRealization
      (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
      before eventsRev exit (.jcc condition edgeTrue edgeFalse) := by
  apply TerminatorRealization.conditional condition edgeTrue edgeFalse relocation.kind
    (nearJccInstruction_encoding relocation.emittedInstruction) conditionMatches eventsAfter
    transition runtimeSilent safe
  · intro selected
    have silent := runtimeSilent
    unfold RuntimeSilentAt at silent
    have machineEq : exit.machine = X86_64Instruction.step
        (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
        before := by
      unfold nativeOutcomeTransition at transition
      simp only [silent] at transition
      exact congrArg Prod.fst transition.symm
    exact (congrArg X86_64MachineState.rip machineEq).trans
      ((relocation.takenDestination before beforeAtSource selected).trans
        relocation.trueEdgeAtStart.symm)
  · intro selected
    have silent := runtimeSilent
    unfold RuntimeSilentAt at silent
    have machineEq : exit.machine = X86_64Instruction.step
        (layout.emitted relocation.sourceBlock relocation.sourceMember).terminatorInstruction
        before := by
      unfold nativeOutcomeTransition at transition
      simp only [silent] at transition
      exact congrArg Prod.fst transition.symm
    exact (congrArg X86_64MachineState.rip machineEq).trans
      ((relocation.fallthroughDestination before beforeAtSource selected).trans
        relocation.falseEdgeAtStart.symm)

end Gasm.Targets.X86_64.CFGLinker

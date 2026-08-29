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

import Gasm.Core.CFG
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.X86_64.Instructions.Hlt

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- The x86 conditions admitted by the operational CFG bridge. This target-owned datatype keeps a
    logical `ConditionCode` from being attached to an unrelated emitted conditional instruction. -/
inductive X86BranchCondition where
  | equal | notEqual | less | lessEqual | greater | greaterEqual

def X86BranchCondition.holds : X86BranchCondition → X86_64MachineState → Prop
  | .equal => (·.zf = true)
  | .notEqual => (·.zf = false)
  | .less => (fun state => state.sf != state.of_)
  | .lessEqual => (fun state => state.zf = true ∨ state.sf != state.of_)
  | .greater => (fun state => state.zf = false ∧ state.sf = state.of_)
  | .greaterEqual => (fun state => state.sf = state.of_)

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Closed target-owned evidence that the exact existential instruction is a direct JMP. -/
inductive DirectJumpEncoding : X86_64Instr → Prop where
  | rel8 (disp : UInt8) : DirectJumpEncoding (jmp_rel8 disp)
  | rel32 (disp : Int32) : DirectJumpEncoding (jmp_rel32 disp)

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Closed target-owned evidence connecting an exact conditional encoding to its flag predicate. -/
inductive ConditionalJumpEncoding : X86_64Instr → X86BranchCondition → Prop where
  | je8 (disp : UInt8) : ConditionalJumpEncoding (je_rel8 disp) .equal
  | je32 (disp : Int32) : ConditionalJumpEncoding (je_rel32 disp) .equal
  | jne8 (disp : UInt8) : ConditionalJumpEncoding (jne_rel8 disp) .notEqual
  | jne32 (disp : Int32) : ConditionalJumpEncoding (jne_rel32 disp) .notEqual
  | jl8 (disp : UInt8) : ConditionalJumpEncoding (jl_rel8 disp) .less
  | jle8 (disp : UInt8) : ConditionalJumpEncoding (jle_rel8 disp) .lessEqual
  | jle32 (disp : Int32) : ConditionalJumpEncoding (jle_rel32 disp) .lessEqual
  | jg8 (disp : UInt8) : ConditionalJumpEncoding (jg_rel8 disp) .greater
  | jge8 (disp : UInt8) : ConditionalJumpEncoding (jge_rel8 disp) .greaterEqual
  | jge32 (disp : Int32) : ConditionalJumpEncoding (jge_rel32 disp) .greaterEqual

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Conservative pure-block ghost law. Typestate and every ghost/authority component are preserved
    exactly. Effectful blocks require a future ABI/obligation-owned transition certificate instead
    of weakening this record. -/
structure ConservativeGhostFrame {Before After : Type}
    (before : ComposedState X86_64 Before) (after : ComposedState X86_64 After) : Prop where
  sameState : After = Before
  stackDepth : after.stackDepth = before.stackDepth
  api : _root_.cast sameState after.api = before.api
  permissions : after.perms = before.perms
  obligations : after.obligations = before.obligations
  causalClock : after.causalClock = before.causalClock
  eventHistory : after.eventHistory = before.eventHistory

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Exact target-owned realization of a logical terminator by one emitted production transition.
    The constructors bind instruction family, host outcome/events, destination selection, RET stack
    behavior, and the platform ABI register carrying an exit code. There is intentionally no
    indirect-jump constructor until an emitted indirect-target decoder is connected. -/
inductive TerminatorRealization {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    (instruction : X86_64Instr) (before : X86_64MachineState) (eventsRev : List Event) :
    {S : Type} → (exit : ComposedState X86_64 S) → CpuTerminator X86_64 exit → Prop where
  | direct {S} {exit : ComposedState X86_64 S} (edge : BlockEdge exit)
      (encoding : DirectJumpEncoding instruction) (eventsAfter : List Event)
      (transition : nativeOutcomeTransition instruction before eventsRev =
        (exit.machine, eventsAfter))
      (safe : exit.machine.fault = none)
      (destination : exit.machine.rip = edge.targetState.machine.rip) :
      TerminatorRealization instruction before eventsRev exit (.jmp edge)
  | conditional {S} {exit : ComposedState X86_64 S} (condition : ConditionCode X86_64)
      (targetTrue : ConditionalBlockEdge exit (condition.holds exit.machine))
      (targetFalse : ConditionalBlockEdge exit (¬ condition.holds exit.machine))
      (kind : X86BranchCondition) (encoding : ConditionalJumpEncoding instruction kind)
      (conditionMatches : condition.holds exit.machine ↔ kind.holds before)
      (eventsAfter : List Event)
      (transition : nativeOutcomeTransition instruction before eventsRev =
        (exit.machine, eventsAfter))
      (safe : exit.machine.fault = none)
      (trueDestination : kind.holds before →
        exit.machine.rip = targetTrue.targetState.machine.rip)
      (falseDestination : ¬ kind.holds before →
        exit.machine.rip = targetFalse.targetState.machine.rip) :
      TerminatorRealization instruction before eventsRev exit
        (.jcc condition targetTrue targetFalse)
  | ret {S} {exit : ComposedState X86_64 S} (exportedObligations : List ObligationToken)
      (hzero : exit.stackDepth = 0) (hmatch : exit.obligations = exportedObligations)
      (hcallee : CalleeDiscipline X86_64 exit)
      (instructionIsRet : instruction = ret_op) (eventsAfter : List Event)
      (transition : nativeOutcomeTransition instruction before eventsRev =
        (exit.machine, eventsAfter))
      (safe : exit.machine.fault = none)
      (stackEffect : exit.machine.rsp = before.rsp + 8) :
      TerminatorRealization instruction before eventsRev exit
        (.ret exportedObligations 0 hzero hmatch hcallee)
  | linuxSysExit {S} {exit : ComposedState X86_64 S} (exitCode : UInt8)
      (hdroppable : ∀ o ∈ exit.obligations, o.isDroppableOnExit)
      (instructionIsSyscall : instruction = syscall_op)
      (exitCodeArgument : before.gprs .rdi = exitCode.toUInt64)
      (eventsAfter : List Event)
      (transition : nativeOutcomeTransition instruction before eventsRev =
        (exit.machine, eventsAfter))
      (halted : exit.machine.fault = some .halted) :
      TerminatorRealization instruction before eventsRev exit (.sysExit exitCode hdroppable)
  | windowsCallExit {S} {exit : ComposedState X86_64 S} (exitCode : UInt8)
      (hdroppable : ∀ o ∈ exit.obligations, o.isDroppableOnExit)
      (disp : Int32) (instructionIsCall : instruction = call_rip disp)
      (exitCodeArgument : before.gprs .rcx = exitCode.toUInt64)
      (eventsAfter : List Event)
      (transition : nativeOutcomeTransition instruction before eventsRev =
        (exit.machine, eventsAfter))
      (halted : exit.machine.fault = some .halted) :
      TerminatorRealization instruction before eventsRev exit (.sysExit exitCode hdroppable)
  | halt {S} {exit : ComposedState X86_64 S}
      (hdroppable : ∀ o ∈ exit.obligations, o.isDroppableOnExit)
      (instructionIsHlt : instruction = hlt_op) (eventsAfter : List Event)
      (transition : nativeOutcomeTransition instruction before eventsRev =
        (exit.machine, eventsAfter))
      (halted : exit.machine.fault = some .halted) :
      TerminatorRealization instruction before eventsRev exit (.halt hdroppable)

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Production continuation selected by the logical terminator after its concrete instruction has
    executed. The logical constructor remains visible, so a syscall exit cannot be confused with an
    arbitrary HLT even though both use the native evaluator's `halted` stop reason. -/
def resumeAfterTerminator {Event S : Type}
    [ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (exit : ComposedState X86_64 S) (eventsRev : List Event) :
    CpuTerminator X86_64 exit → NativeRunOutcome Event
  | .jmp _ | .jmpIndirect _ | .jcc .. | .ret .. =>
      runProgramOutcomeLoop indexed fuel exit.machine eventsRev
  | .sysExit .. | .halt .. => .halted exit.machine eventsRev.reverse

namespace TerminatorRealization

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- A realized terminator is exactly one production evaluator step followed by the logical
    continuation (or the explicit halt outcome). -/
theorem runProgramOutcomeLoop_step {Event S : Type}
    [ExternalCallInterceptor X86_64 Event]
    (indexed : List (UInt64 × X86_64Instr)) (fuel : Nat)
    (instruction : X86_64Instr) (before : X86_64MachineState) (eventsRev : List Event)
    (exit : ComposedState X86_64 S) (terminator : CpuTerminator X86_64 exit)
    (lookup : instructionAtRipIndexed indexed before.rip = some instruction)
    (realized : TerminatorRealization instruction before eventsRev exit terminator) :
    runProgramOutcomeLoop indexed (fuel + 1) before eventsRev =
      resumeAfterTerminator indexed fuel exit
        (nativeOutcomeTransition instruction before eventsRev).2 terminator := by
  simp only [runProgramOutcomeLoop, lookup]
  cases realized <;> simp_all [resumeAfterTerminator]

end TerminatorRealization

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- One basic block as an exact contiguous slice of one final artifact. `bodyCode` is the ordinary
    prefix discharged by the macro runner; `terminatorInstruction` is deliberately outside that
    prefix and is checked by the production evaluator itself. -/
structure EmittedBasicBlock {Artifact : Type} (indexOf : Artifact → List (UInt64 × X86_64Instr))
    (artifact : Artifact) (block : BasicBlock X86_64) where
  bodyBase : UInt64
  bodyCode : List X86_64Instr
  terminatorInstruction : X86_64Instr
  bodyOrdinary : ∀ instruction ∈ bodyCode, ControlFlowFree instruction
  emittedSlice : ContiguousInstructionSubsequence (indexOf artifact) bodyBase
    (bodyCode ++ [terminatorInstruction])

namespace EmittedBasicBlock

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Exact lookup of the emitted terminator follows from the artifact-global layout law and the
    block's contiguous-slice certificate. -/
theorem terminatorLookup {Artifact : Type} {indexOf : Artifact → List (UInt64 × X86_64Instr)}
    {artifact : Artifact} {block : BasicBlock X86_64}
    (emitted : EmittedBasicBlock indexOf artifact block)
    (layout : IndexedLayoutCertificate (indexOf artifact))
    (initial : X86_64MachineState) (entryRip : initial.rip = emitted.bodyBase) :
    instructionAtRipIndexed (indexOf artifact)
      (runLocalSteps emitted.bodyCode initial).rip = some emitted.terminatorInstruction := by
  have memberBody := indexInstructions_prefix_mem emitted.bodyBase
    (emitted.bodyCode ++ [emitted.terminatorInstruction]) emitted.bodyCode
    emitted.terminatorInstruction [] (by simp)
  have memberArtifact := emitted.emittedSlice.included _ memberBody
  have resolves := layout.resolves _ memberArtifact
  rw [runLocalSteps_rip_eq emitted.bodyCode emitted.bodyOrdinary]
  simpa [entryRip] using resolves

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Pointwise operational realization. This is the only block-local proof obligation: the entry
    names the emitted slice, the ordinary prefix is runtime-silent, and the exact production host
    transition for the emitted terminator produces the dependent body result. -/
structure RealizesAt {Event Artifact : Type}
    [ExternalCallInterceptor X86_64 Event]
    {indexOf : Artifact → List (UInt64 × X86_64Instr)} {artifact : Artifact}
    {block : BasicBlock X86_64} (emitted : EmittedBasicBlock indexOf artifact block)
    (state : ComposedState X86_64 block.entry.State)
    (accepted : block.entry.accepts state) : Prop where
  entryRip : state.machine.rip = emitted.bodyBase
  initialSafe : state.machine.fault = none
  runtimeSilent : RuntimeSilentOn (Event := Event) emitted.bodyCode state.machine
  ghostFrame :
    let result := block.body state accepted
    ConservativeGhostFrame state result.2.1
  terminatorRealization : ∀ eventsRev,
    let result := block.body state accepted
    TerminatorRealization (Event := Event) emitted.terminatorInstruction
      (runLocalSteps emitted.bodyCode state.machine) eventsRev result.2.1 result.2.2

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Exact production execution theorem for a realized block. Unlike `Step.fromBody`, this theorem
    cannot be constructed from an arbitrary Lean body: it consumes final-artifact placement and the
    actual production instruction/interceptor transition. -/
theorem runProgramOutcomeLoop_block {Event Artifact : Type}
    [ExternalCallInterceptor X86_64 Event]
    {indexOf : Artifact → List (UInt64 × X86_64Instr)} {artifact : Artifact}
    {block : BasicBlock X86_64} (emitted : EmittedBasicBlock indexOf artifact block)
    (layout : IndexedLayoutCertificate (indexOf artifact))
    (state : ComposedState X86_64 block.entry.State)
    (accepted : block.entry.accepts state)
    (realized : RealizesAt (Event := Event) emitted state accepted)
    (fuel : Nat) (eventsRev : List Event) :
    let result := block.body state accepted
    let next := nativeOutcomeTransition emitted.terminatorInstruction
      (runLocalSteps emitted.bodyCode state.machine) eventsRev
    runProgramOutcomeLoop (indexOf artifact) (emitted.bodyCode.length + (fuel + 1))
        state.machine eventsRev =
      resumeAfterTerminator (indexOf artifact) fuel result.2.1 next.2 result.2.2 := by
  dsimp only
  have placement := ContextualStraightLinePlacement.ofSubsequence
    (indexOf artifact) emitted.bodyBase emitted.bodyCode state.machine emitted.bodyOrdinary
    realized.entryRip layout
    { included := by
        intro entry member
        apply emitted.emittedSlice.included entry
        rw [indexInstructions, indexInstructions_loop_append]
        exact List.mem_append_left _ member }
  rw [runProgramOutcomeLoop_prefix emitted.bodyCode emitted.bodyOrdinary
    (indexOf artifact) emitted.bodyBase state.machine placement realized.runtimeSilent
    realized.initialSafe (fuel + 1) eventsRev]
  have lookup := emitted.terminatorLookup layout state.machine realized.entryRip
  have terminal := realized.terminatorRealization eventsRev
  exact TerminatorRealization.runProgramOutcomeLoop_step _ _ _ _ _ _ _ lookup terminal

end EmittedBasicBlock

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- Final-artifact operational realization of every published block in a typed CFG. Link layout is
    owned once here; consumers select blocks and edges without replaying global placement facts. -/
structure OperationalCFGRealization {Event Artifact : Type}
    [ExternalCallInterceptor X86_64 Event]
    (indexOf : Artifact → List (UInt64 × X86_64Instr)) (artifact : Artifact)
    (graph : TypedControlFlowGraph X86_64) where
  layout : IndexedLayoutCertificate (indexOf artifact)
  emitted : (block : BasicBlock X86_64) → block ∈ graph.blocks →
    EmittedBasicBlock indexOf artifact block
  realizes : ∀ (block : BasicBlock X86_64) (member : block ∈ graph.blocks)
    (state : ComposedState X86_64 block.entry.State) (accepted : block.entry.accepts state),
    EmittedBasicBlock.RealizesAt (Event := Event) (emitted block member) state accepted

end Gasm.Targets.X86_64

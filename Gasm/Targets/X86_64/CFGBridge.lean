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

namespace Gasm.Targets.X86_64

open Gasm.Core
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/MACRO_ASSEMBLER.md#operational-cfg-realization -/
/-- The fault state demanded after the emitted terminator. Jump-like transfers and returns resume
    production execution; explicit process exits and halts must reach the platform's halt outcome.
    Divide and memory faults never realize a typed terminator. -/
def ProductionTerminatorFault {S : Type} (exit : ComposedState X86_64 S) :
    CpuTerminator X86_64 exit → Prop
  | .jmp _ | .jmpIndirect _ | .jcc .. | .ret .. => exit.machine.fault = none
  | .sysExit .. | .halt .. => exit.machine.fault = some .halted

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
  exitMachine :
    let result := block.body state accepted
    result.2.1.machine =
      (nativeOutcomeTransition (Event := Event) emitted.terminatorInstruction
        (runLocalSteps emitted.bodyCode state.machine) []).1
  terminatorFault :
    let result := block.body state accepted
    ProductionTerminatorFault result.2.1 result.2.2

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
  simp only [runProgramOutcomeLoop, lookup]
  let next := nativeOutcomeTransition emitted.terminatorInstruction
    (runLocalSteps emitted.bodyCode state.machine) eventsRev
  have sameMachine : next.1 = (block.body state accepted).2.1.machine := by
    calc
      next.1 = (nativeOutcomeTransition emitted.terminatorInstruction
          (runLocalSteps emitted.bodyCode state.machine) []).1 :=
        nativeOutcomeTransition_fst_independent_events _ _ _ _
      _ = (block.body state accepted).2.1.machine := realized.exitMachine.symm
  change (match next.1.fault with
    | none => runProgramOutcomeLoop (indexOf artifact) fuel next.1 next.2
    | some .halted => .halted next.1 next.2.reverse
    | some .divideError => .faulted next.1 next.2.reverse
    | some (.memFault _ _ _) => .faulted next.1 next.2.reverse) = _
  rw [sameMachine]
  have fault := realized.terminatorFault
  cases hterm : (block.body state accepted).2.2 <;>
    simp [ProductionTerminatorFault, hterm] at fault <;>
    simp [resumeAfterTerminator, hterm, fault, next]

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

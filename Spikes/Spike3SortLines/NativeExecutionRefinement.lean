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
import Spikes.Spike3SortLines.NativeSpecification

/-!
Selected-artifact execution refinement for native Spike 3 preparation.

The prior preparation certificate deliberately stopped at an operation trace of
the allocator routines.  This module is the only seam which lets that trace be
used as native execution evidence: every allocator invocation has a prefix
from the exact loaded artifact entry, a contiguous linked-code witness, and a
selected production prefix for the routine itself.  The abstraction leaves RIP
coordinates to link evidence while forbidding a standalone `0x1000` test
routine or an unrelated artifact.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.Linux
open Gasm.Targets.Windows
open Gasm.Targets.X86_64.ProductionPrefix
open Stdlib.SmolAlloc

/-- The exact selected instruction view.  This is a projection of the
    context-indexed artifact, never an instruction list supplied by a client. -/
def nativePreparationInstructions (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) : List X86_64Instr :=
  match target with
  | .linux => (spike3LinuxArtifactForContext context).instructions
  | .windows => (spike3WindowsArtifactForContext context).instructions

/-- The exact entry state from the same artifact and universal environment. -/
def nativePreparationEntry (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment) : X86_64MachineState :=
  match target with
  | .linux => (spike3LinuxArtifactForContext context).executable.loadWithStdin environment.stdin
  | .windows => (spike3WindowsArtifactForContext context).executable.loadWithStdin environment.stdin

/-- The production indexed text for a selected native artifact. -/
def nativePreparationIndex (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment) :
    List (UInt64 × X86_64Instr) :=
  indexInstructions (nativePreparationEntry target context environment).rip
    (nativePreparationInstructions target context)

/-- The host-call surface accepted by the actual selected runtime.  Ordinary
    artifact addresses are admitted; host boundaries are restricted to the
    target's concrete ABI surface instead of being hidden behind `true`. -/
def nativePreparationSelected (target : NativePreparationTarget) (address : Gasm.Core.Address)
    (state : X86_64MachineState) : Bool :=
  match target with
  | .linux =>
      if address == linuxSyscallEntry then
        state.gprs .rax == SYS_mmap || state.gprs .rax == SYS_read ||
          state.gprs .rax == SYS_write || state.gprs .rax == SYS_exit
      else true
  | .windows =>
      match findIatIndex state address with
      | some index => index < 6
      | none => true

/-- The target-owned production runner.  Keeping the full `NativeRunOutcome`
    here is important: its final machine state and emitted events remain
    available to the phase certificate before any observable outcome is
    projected. -/
def runNativePreparation (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment) (fuel : Nat) :
    NativeRunOutcome AnyEvent :=
  match target with
  | .linux =>
      letI : ExternalCallInterceptor X86_64 AnyEvent :=
        spike3LinuxRuntime AnyEvent context.arenaGrant
      runProgramOutcomeWithLoops (nativePreparationEntry target context environment).rip
        (nativePreparationInstructions target context) fuel
        (nativePreparationEntry target context environment)
  | .windows =>
      letI : ExternalCallInterceptor X86_64 AnyEvent :=
        spike3WindowsRuntime AnyEvent context.arenaGrant
      runProgramOutcomeWithLoops (nativePreparationEntry target context environment).rip
        (nativePreparationInstructions target context) fuel
        (nativePreparationEntry target context environment)

/-- One exact finite segment of the production runner.  The target runtime,
    artifact index, selection policy, step count, state transition, and event
    transition are all fixed by the enclosing target/context/environment. -/
def NativePreparationPrefix (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment) :
    (fuel : Nat) → X86_64MachineState → List AnyEvent → X86_64MachineState →
      List AnyEvent → List AnyEvent → Prop :=
  match target with
  | .linux =>
      letI : ExternalCallInterceptor X86_64 AnyEvent :=
        spike3LinuxRuntime AnyEvent context.arenaGrant
      SelectedPrefix (nativePreparationSelected target)
        (nativePreparationIndex target context environment)
  | .windows =>
      letI : ExternalCallInterceptor X86_64 AnyEvent :=
        spike3WindowsRuntime AnyEvent context.arenaGrant
      SelectedPrefix (nativePreparationSelected target)
        (nativePreparationIndex target context environment)

/-- A `smol_malloc` operation together with its actual placement and
    reachability in the selected final artifact.  `routinePrefix` executes the
    linked instructions, not a separately loaded allocator fixture. -/
structure NativeLinkedMalloc (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (arena : NativeArenaCapability) (request : UInt64)
    (before after : SmolAllocatorFrame) (result : NativeAllocatorCallResult) where
  call : NativeAllocatorCall arena request before after result
  entryReachable : ∃ fuel eventsAtEntry emitted,
    NativePreparationPrefix target context environment fuel
      (nativePreparationEntry target context environment) [] call.machineBefore eventsAtEntry emitted
  linkedSlice : ContiguousInstructionSubsequence
    (nativePreparationIndex target context environment) call.entryRip call.instructions
  routinePrefix : ∃ fuel eventsAtEntry eventsAfter,
    NativePreparationPrefix target context environment fuel call.machineBefore eventsAtEntry
      call.machineAfter eventsAfter []

/-- The corresponding selected-artifact witness for `smol_free`.  The payload
    is retained in both this object and `NativeOperationTrace` so a free cannot
    be reinterpreted as reclaiming an unrelated allocation. -/
structure NativeLinkedFree (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (before after : SmolAllocatorFrame) (payload : UInt64) where
  call : NativeAllocatorFreeCall before after payload
  entryReachable : ∃ fuel eventsAtEntry emitted,
    NativePreparationPrefix target context environment fuel
      (nativePreparationEntry target context environment) [] call.machineBefore eventsAtEntry emitted
  linkedSlice : ContiguousInstructionSubsequence
    (nativePreparationIndex target context environment) call.entryRip call.instructions
  routinePrefix : ∃ fuel eventsAtEntry eventsAfter,
    NativePreparationPrefix target context environment fuel call.machineBefore eventsAtEntry
      call.machineAfter eventsAfter []

/-- The allocator trace after it has been bound to reachable production code.
    This is intentionally indexed by the plan's operation list and live owner
    list: callers cannot permute calls, drop an intervening free, or discharge
    an EOF/growth free with a pointer owned by another allocation. -/
inductive NativeLinkedOperationTrace (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (arena : NativeArenaCapability) :
    SmolAllocatorFrame → List (NativeAllocationOwner × UInt64) →
      List NativePreparationOperation → SmolAllocatorFrame →
        List (NativeAllocationOwner × UInt64) → Prop where
  | empty (frame : SmolAllocatorFrame) (live : List (NativeAllocationOwner × UInt64)) :
      NativeLinkedOperationTrace target context environment arena frame live [] frame live
  | malloc {before after finish : SmolAllocatorFrame} {purpose : NativeMallocPurpose}
      {payload : UInt64} {live liveFinish : List (NativeAllocationOwner × UInt64)}
      {operations : List NativePreparationOperation}
      (linked : NativeLinkedMalloc target context environment arena purpose.request before after .allocated)
      (returned : linked.call.machineAfter.gprs .rax = payload)
      (rest : NativeLinkedOperationTrace target context environment arena after
        ((purpose.owner, payload) :: live) operations finish liveFinish) :
      NativeLinkedOperationTrace target context environment arena before live
        (.malloc purpose :: operations) finish liveFinish
  | free {before after finish : SmolAllocatorFrame} {purpose : NativeFreePurpose}
      {payload : UInt64} {live liveFinish : List (NativeAllocationOwner × UInt64)}
      {operations : List NativePreparationOperation}
      (owned : (purpose.owner, payload) ∈ live)
      (linked : NativeLinkedFree target context environment before after payload)
      (rest : NativeLinkedOperationTrace target context environment arena after
        (live.erase (purpose.owner, payload)) operations finish liveFinish) :
      NativeLinkedOperationTrace target context environment arena before live
        (.free purpose payload :: operations) finish liveFinish

/-- Forgetting production reachability yields exactly the original ordered
    allocator trace; the theorem is a one-way cutpoint so downstream phase
    proofs do not normalize the selected-prefix constructor spine. -/
theorem NativeLinkedOperationTrace.toNativeOperationTrace
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {arena : NativeArenaCapability}
    {initial final : SmolAllocatorFrame} {liveInitial liveFinal : List (NativeAllocationOwner × UInt64)}
    {operations : List NativePreparationOperation}
    (trace : NativeLinkedOperationTrace target context environment arena initial liveInitial operations final liveFinal) :
    NativeOperationTrace arena initial liveInitial operations final liveFinal := by
  induction trace with
  | empty => exact .empty _ _
  | malloc linked returned rest ih => exact .malloc linked.call returned ih
  | free owned linked rest ih => exact .free owned linked.call ih

/-- EOF is a phase fact, not yet a public success outcome.  Its trace has
    completed every operation in the one selected plan, including the two
    staging-buffer frees prescribed by `operationsExact`. -/
structure NativeEOFExecution (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    {stored : List (List UInt8)} (plan : NativePreparationPlan stored)
    (arena : NativeArenaCapability) (initial final : SmolAllocatorFrame)
    (liveFinal : List (NativeAllocationOwner × UInt64)) where
  operations : NativeLinkedOperationTrace target context environment arena initial []
    plan.operations final liveFinal

/-- The explicit terminal classification of an exact native preparation run.
    `eof` does not expose a sorted/output result.  Only `success` additionally
    carries the existing `.ready` proof; resource refusal is kept distinct and
    requires the target's resource-exit code in the actual unprojected run. -/
inductive NativePreparationExecutionOutcome (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8))
    (execution : NativeRunOutcome AnyEvent) : Prop where
  | resourceRefusal
      (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
      (exhausted : nativePreparationOutcome evidence = .exhausted)
      (final : X86_64MachineState) (events : List AnyEvent)
      (terminal : execution = .terminated (.processExit spike3ResourceFailureExitCode) final events) :
      NativePreparationExecutionOutcome target context environment storageCapacity readCapacity chunks execution
  | eof {stored : List (List UInt8)} {plan : NativePreparationPlan stored}
      {arena : NativeArenaCapability} {initial final : SmolAllocatorFrame}
      {liveFinal : List (NativeAllocationOwner × UInt64)}
      (completed : NativeEOFExecution target context environment plan arena initial final liveFinal) :
      NativePreparationExecutionOutcome target context environment storageCapacity readCapacity chunks execution
  | success {stored : List (List UInt8)} {plan : NativePreparationPlan stored}
      {arena : NativeArenaCapability} {initial finalFrame : SmolAllocatorFrame}
      {liveFinal : List (NativeAllocationOwner × UInt64)}
      (completed : NativeEOFExecution target context environment plan arena initial finalFrame liveFinal)
      (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
      (ready : nativePreparationOutcome evidence = .ready)
      (final : X86_64MachineState) (events : List AnyEvent)
      (terminal : execution = .terminated (.processExit 0) final events) :
      NativePreparationExecutionOutcome target context environment storageCapacity readCapacity chunks execution

/-- The complete selected-artifact refinement.  Its only input observation is
    the universal read binder; lossless records are derived from that exact
    stdin, and the chosen plan is then tied to ordered reachable allocator
    calls before a resource/EOF/success outcome may be classified. -/
structure NativePreparationExecutionRefinement (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8)) where
  reads : ChunksOf environment.stdin.toList readCapacity chunks
  stored : List (List UInt8)
  plan : NativePreparationPlan stored
  inputExact : plan.records = decodeNativeRecords environment.stdin
  fuel : Nat
  execution : NativeRunOutcome AnyEvent
  runnerExact : runNativePreparation target context environment fuel = execution
  outcome : NativePreparationExecutionOutcome target context environment storageCapacity
    readCapacity chunks execution

/-- The selected plan's source lines are forced by the same universal stdin
    binder.  This is derived, rather than accepted as a second adapter field. -/
theorem NativePreparationExecutionRefinement.lines_exact
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (refinement : NativePreparationExecutionRefinement target context environment
      storageCapacity readCapacity chunks) :
    refinement.stored = environmentInputLines environment := by
  rw [← refinement.plan.recordsExact, refinement.inputExact]
  exact decodeNativeRecords_lines environment.stdin

/-- The proof-relevant read schedule is the same byte stream from which the
    lossless records are decoded; chunk boundaries are not an auxiliary input
    selector. -/
theorem NativePreparationExecutionRefinement.read_chunks_exact
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (refinement : NativePreparationExecutionRefinement target context environment
      storageCapacity readCapacity chunks) :
    chunks.flatten = environment.stdin.toList :=
  refinement.reads.flatten_eq_total

end Spikes.Spike3SortLines

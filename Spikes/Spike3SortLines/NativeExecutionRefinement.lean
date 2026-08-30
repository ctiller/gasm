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
  linkedSlice : ContiguousInstructionSubsequence
    (nativePreparationIndex target context environment) call.entryRip call.instructions
  routinePrefix : ∃ fuel eventsAtEntry eventsAfter,
    NativePreparationPrefix target context environment fuel call.machineBefore eventsAtEntry
      call.machineAfter eventsAfter []

/-- The input capacity requested by the two emitted native read sites.  This
is read from the live ABI register at the host boundary, not supplied as a
separate logical chunk-size parameter. -/
def nativeReadRequestCapacity (target : NativePreparationTarget)
    (state : X86_64MachineState) : UInt64 :=
  match target with
  | .linux => state.gprs .rdx
  | .windows => state.gprs .r8

/-- The selected target runtime's actual host dispatcher, retained in the
certificate so a boundary cannot be replaced with a register-shaped hook
lemma. -/
def nativePreparationHostIntercept (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (address : Gasm.Core.Address)
    (state : X86_64MachineState) : Option (X86_64MachineState × Option AnyEvent) :=
  match target with
  | .linux => spike3LinuxCallIntercept context.arenaGrant address state
  | .windows => spike3WindowsCallIntercept context.arenaGrant address state

/-- Named control-flow nodes for the preparation artifact.  These are not a
generic solver: each node carries the Spike3-specific phase, chunk cursor,
allocation ownership and callsite-occurrence ledger that its body must
preserve. -/
inductive NativePreparationBlock where
  | loader | read | scan | grow | payload | node | eofCleanup | sortTable | sort | write
  | resourceExit | successExit
  deriving DecidableEq

structure NativePreparationGhostState {stored : List (List UInt8)}
    (plan : NativePreparationPlan stored) where
  phase : NativePreparationBlock
  observedChunks : List (List UInt8)
  retainedPrefix : List NativeInputRecord
  liveOwners : List (NativeAllocationOwner × UInt64)
  occurrenceLedger : List NativeMallocOccurrence
  occurrenceExact : occurrenceLedger = plan.mallocOccurrences
  operationsRemaining : List NativePreparationOperation

/-- A caller-supplied local contract.  `forward` propagates the facts a block
establishes; `backward` states the weakest postcondition demanded by its
successor.  Their equality is the explicit join invariant, and terminal edges
are represented by a process outcome rather than another fall-through node. -/
structure NativePreparationBlockContract (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    {stored : List (List UInt8)} (plan : NativePreparationPlan stored)
    (source targetBlock : NativePreparationBlock)
    (before after : NativePreparationGhostState plan)
    (machineBefore machineAfter : X86_64MachineState)
    (eventsBefore eventsAfter : List AnyEvent) where
  forward : before.phase = source
  backward : after.phase = targetBlock
  joinInvariant : before.operationsRemaining = after.operationsRemaining ∨
    after.operationsRemaining = before.operationsRemaining.tail
  fuel : Nat
  execution : NativePreparationPrefix target context environment fuel machineBefore eventsBefore
    machineAfter eventsAfter []

/-- A single actual host-read boundary in the selected artifact.  The before
and after stdin buffers expose precisely the bytes consumed by that call;
the selected production segment retains its machine state, event continuation,
and local fuel. -/
structure NativeProductionReadStep (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (readCapacity : Nat) (chunk : List UInt8)
    (before after : X86_64MachineState) (eventsBefore eventsAfter : List AnyEvent) where
  instruction : X86_64Instr
  hostEncoding : HostInterceptEncoding instruction
  boundary : X86_64MachineState
  steppedIntoBoundary : boundary = X86_64Instruction.step instruction before
  /- The artifact reaches this host boundary by executing its selected
      instruction; this is separate from the host interception which consumes
      stdin after the instruction has established the ABI boundary. -/
  artifactStep : NativePreparationPrefix target context environment 1 before eventsBefore
    boundary eventsBefore []
  requestedCapacity : nativeReadRequestCapacity target boundary = readCapacity.toUInt64
  targetCapacity : readCapacity = 512
  readEntry : match target with
    | .linux => boundary.rip = linuxSyscallEntry ∧ boundary.gprs .rax = SYS_read ∧
        boundary.gprs .rdi = 0 ∧ boundary.gprs .rdx = readCapacity.toUInt64
    | .windows => findIatIndex boundary boundary.rip = some 1
  intercepted : nativePreparationHostIntercept target context boundary.rip boundary = some (after, none)
  consumed : before.stdinBuffer.toList = chunk ++ after.stdinBuffer.toList
  fuel : Nat
  selectedSegment : NativePreparationPrefix target context environment fuel before eventsBefore
    after eventsAfter []

/-- Ordered physical read calls of one production execution.  Adjacent states
and event continuations are definitionally shared, so a `ChunksOf` witness can
no longer be attached to a different read schedule. -/
inductive NativeProductionReadTrace (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment) (readCapacity : Nat) :
    X86_64MachineState → List AnyEvent → List (List UInt8) →
      X86_64MachineState → List AnyEvent → Type 1 where
  | empty (state : X86_64MachineState) (events : List AnyEvent) :
      NativeProductionReadTrace target context environment readCapacity state events [] state events
  | read {before middle final : X86_64MachineState} {eventsBefore eventsMiddle eventsFinal : List AnyEvent}
      {chunk : List UInt8} {chunks : List (List UInt8)}
      (step : NativeProductionReadStep target context environment readCapacity chunk before middle
        eventsBefore eventsMiddle)
      (rest : NativeProductionReadTrace target context environment readCapacity middle eventsMiddle
        chunks final eventsFinal) :
      NativeProductionReadTrace target context environment readCapacity before eventsBefore
        (chunk :: chunks) final eventsFinal

def NativeProductionReadTrace.totalFuel : NativeProductionReadTrace target context environment readCapacity
    initial initialEvents chunks final finalEvents → Nat
  | .empty .. => 0
  | .read step rest => step.fuel + rest.totalFuel

/-- A chained production realization of an allocator plan.  Unlike the older
reachability projection, each next call begins in the preceding call's exact
machine state and event continuation; each segment carries its own checked
fuel rather than being a collection of unrelated prefixes. -/
inductive NativeProductionOperationTrace (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (arena : NativeArenaCapability) :
    SmolAllocatorFrame → List (NativeAllocationOwner × UInt64) →
      X86_64MachineState → List AnyEvent → List NativePreparationOperation →
      SmolAllocatorFrame → List (NativeAllocationOwner × UInt64) →
        X86_64MachineState → List AnyEvent → Type 1 where
  | empty (frame : SmolAllocatorFrame) (live : List (NativeAllocationOwner × UInt64))
      (state : X86_64MachineState) (events : List AnyEvent) :
      NativeProductionOperationTrace target context environment arena frame live state events []
        frame live state events
  | malloc {before after finish : SmolAllocatorFrame} {purpose : NativeMallocPurpose}
      {payload : UInt64} {live liveFinish : List (NativeAllocationOwner × UInt64)}
      {machineBefore machineAfter machineFinish : X86_64MachineState}
      {eventsBefore eventsAfter eventsFinish : List AnyEvent} {operations : List NativePreparationOperation}
      (linked : NativeLinkedMalloc target context environment arena purpose.request before after .allocated)
      (identity : NativeMallocOccurrence)
      (purposeIdentity : identity.purpose = purpose)
      (callsiteRipExact : linked.call.entryRip = identity.callsiteRip)
      (machineExact : linked.call.machineBefore = machineBefore ∧ linked.call.machineAfter = machineAfter)
      (fuel : Nat)
      (segment : NativePreparationPrefix target context environment fuel machineBefore eventsBefore
        machineAfter eventsAfter [])
      (returned : linked.call.machineAfter.gprs .rax = payload)
      (continuationFuel : Nat) (continuationMachine : X86_64MachineState)
      (continuationEvents : List AnyEvent)
      (continuation : NativePreparationPrefix target context environment continuationFuel
        machineAfter eventsAfter continuationMachine continuationEvents [])
      (rest : NativeProductionOperationTrace target context environment arena after
        ((purpose.owner, payload) :: live) continuationMachine continuationEvents operations finish liveFinish
          machineFinish eventsFinish) :
      NativeProductionOperationTrace target context environment arena before live machineBefore eventsBefore
        (.malloc purpose :: operations) finish liveFinish machineFinish eventsFinish
  | free {before after finish : SmolAllocatorFrame} {purpose : NativeFreePurpose}
      {payload : UInt64} {live liveFinish : List (NativeAllocationOwner × UInt64)}
      {machineBefore machineAfter machineFinish : X86_64MachineState}
      {eventsBefore eventsAfter eventsFinish : List AnyEvent} {operations : List NativePreparationOperation}
      (owned : (purpose.owner, payload) ∈ live)
      (linked : NativeLinkedFree target context environment before after payload)
      (machineExact : linked.call.machineBefore = machineBefore ∧ linked.call.machineAfter = machineAfter)
      (fuel : Nat)
      (segment : NativePreparationPrefix target context environment fuel machineBefore eventsBefore
        machineAfter eventsAfter [])
      (continuationFuel : Nat) (continuationMachine : X86_64MachineState)
      (continuationEvents : List AnyEvent)
      (continuation : NativePreparationPrefix target context environment continuationFuel
        machineAfter eventsAfter continuationMachine continuationEvents [])
      (rest : NativeProductionOperationTrace target context environment arena after
        (live.erase (purpose.owner, payload)) continuationMachine continuationEvents operations finish liveFinish
          machineFinish eventsFinish) :
      NativeProductionOperationTrace target context environment arena before live machineBefore eventsBefore
        (.free purpose payload :: operations) finish liveFinish machineFinish eventsFinish

def NativeProductionOperationTrace.totalFuel : NativeProductionOperationTrace target context environment arena
    initial initialLive initialMachine initialEvents operations final finalLive finalMachine finalEvents → Nat
  | .empty .. => 0
  | .malloc _ _ _ _ _ fuel _ _ continuationFuel _ _ _ rest => fuel + continuationFuel + rest.totalFuel
  | .free _ _ _ fuel _ continuationFuel _ _ _ rest => fuel + continuationFuel + rest.totalFuel

/-- The callsite ledger is projected from the same chained execution spine,
not supplied beside it.  Combined with the plan's ordinal invariant, this
prevents an equal-sized allocator call from standing in for a different
occurrence. -/
def NativeProductionOperationTrace.mallocIdentities : NativeProductionOperationTrace target context environment arena
    initial initialLive initialMachine initialEvents operations final finalLive finalMachine finalEvents →
      List NativeMallocOccurrence
  | .empty .. => []
  | .malloc _ identity _ _ _ _ _ _ _ _ _ _ rest => identity :: rest.mallocIdentities
  | .free _ _ _ _ _ _ _ _ _ rest => rest.mallocIdentities

/-- Forget the production coordinates only after the complete chain has been
checked.  This preserves the original allocator-frame theorem for downstream
resource arguments without weakening the execution certificate. -/
theorem NativeProductionOperationTrace.toNativeOperationTrace
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {arena : NativeArenaCapability}
    {initial final : SmolAllocatorFrame} {liveInitial liveFinal : List (NativeAllocationOwner × UInt64)}
    {machineInitial machineFinal : X86_64MachineState} {eventsInitial eventsFinal : List AnyEvent}
    {operations : List NativePreparationOperation}
    (trace : NativeProductionOperationTrace target context environment arena initial liveInitial
      machineInitial eventsInitial operations final liveFinal machineFinal eventsFinal) :
    NativeOperationTrace arena initial liveInitial operations final liveFinal := by
  induction trace with
  | empty => exact .empty _ _
  | malloc linked identity purposeIdentity callsiteRipExact machineExact fuel segment returned continuationFuel continuationMachine continuationEvents continuation rest ih =>
      exact .malloc linked.call returned ih
  | free owned linked machineExact fuel segment continuationFuel continuationMachine continuationEvents continuation rest ih =>
      exact .free owned linked.call ih

/-- EOF is a phase fact, not yet a public success outcome.  Its trace has
    completed every operation in the one selected plan, including the two
    staging-buffer frees prescribed by `operationsExact`. -/
structure NativeEOFExecution (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    {stored : List (List UInt8)} (plan : NativePreparationPlan stored)
    (arena : NativeArenaCapability) (initial final : SmolAllocatorFrame)
    (liveFinal : List (NativeAllocationOwner × UInt64)) where
  machineFinal : X86_64MachineState
  eventsFinal : List AnyEvent
  productionOperations : NativeProductionOperationTrace target context environment arena initial []
    (nativePreparationEntry target context environment) [] plan.operations final liveFinal
      machineFinal eventsFinal

/-- The failure locator for a plan-aware terminal result.  Ingestion failures
name the scanner record and one of all three emitted refusal sites; the only
non-record position is the post-EOF descriptor-table allocation. -/
inductive NativePlannedRefusalPosition {stored : List (List UInt8)}
    (plan : NativePreparationPlan stored) where
  | record (record : NativeInputRecord) (position : NativeRecordRefusalPosition record)
  | sortTable

def NativePlannedRefusalPosition.mallocPurpose {stored : List (List UInt8)}
    {plan : NativePreparationPlan stored} : NativePlannedRefusalPosition plan → NativeMallocPurpose
  | .record _ position => position.failurePurpose.mallocPurpose
  | .sortTable => .sortTable stored

/-- The explicit terminal classification of an exact native preparation run.
    EOF is an internal phase fact (`NativeEOFExecution`), not a terminal arm:
    publishing it as an outcome used to permit an arbitrary run to be called
    EOF.  The two terminal constructors are disjoint process-exit results of
    the exact selected execution. -/
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
  | success {stored : List (List UInt8)} {plan : NativePreparationPlan stored}
      {arena : NativeArenaCapability} {initial finalFrame : SmolAllocatorFrame}
      {liveFinal : List (NativeAllocationOwner × UInt64)}
      (completed : NativeEOFExecution target context environment plan arena initial finalFrame liveFinal)
      (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
      (ready : nativePreparationOutcome evidence = .ready)
      (final : X86_64MachineState) (events : List AnyEvent)
      (terminal : execution = .terminated (.processExit 0) final events) :
      NativePreparationExecutionOutcome target context environment storageCapacity readCapacity chunks execution

/-- The two public terminal classifications are disjoint before final states
or event prefixes are projected: the resource path exits with 75, while the
successful artifact path exits with zero. -/
theorem native_resource_terminal_ne_success_terminal
    (resourceFinal successFinal : X86_64MachineState) (resourceEvents successEvents : List AnyEvent) :
    (.terminated (.processExit spike3ResourceFailureExitCode) resourceFinal resourceEvents :
      NativeRunOutcome AnyEvent) ≠ .terminated (.processExit 0) successFinal successEvents := by
  simp [spike3ResourceFailureExitCode]

/-- Terminal results after stdin has been observed are indexed by the one
stdin-exact preparation plan.  A resource refusal therefore names its exact
failed operation in that plan, while a successful exit owns the completed
ordered production chain for the same plan. -/
inductive NativePlannedExecutionOutcome (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8))
    {stored : List (List UInt8)} (plan : NativePreparationPlan stored)
    (execution : NativeRunOutcome AnyEvent) : Prop where
  | resourceRefusal {arena : NativeArenaCapability} {initial : SmolAllocatorFrame}
      (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
      (postRead : evidence.isPostReadRefusal = true)
      (position : NativePlannedRefusalPosition plan)
      (refusal : NativeOperationRefusal arena plan initial)
      (positionExact : refusal.nextPurpose = position.mallocPurpose)
      (machineBefore : X86_64MachineState) (eventsBefore : List AnyEvent)
      (completed : NativeProductionOperationTrace target context environment arena initial []
        (nativePreparationEntry target context environment) [] refusal.completedOperations
          refusal.beforeFailure refusal.liveBeforeFailure machineBefore eventsBefore)
      (failed : NativeLinkedMalloc target context environment arena refusal.nextPurpose.request
        refusal.beforeFailure refusal.beforeFailure .refused)
      (failedAtBoundary : failed.call.machineBefore = machineBefore)
      (failedFuel : Nat)
      (failedPrefix : NativePreparationPrefix target context environment failedFuel machineBefore eventsBefore
        failed.call.machineAfter eventsBefore [])
      (final : X86_64MachineState) (events : List AnyEvent)
      (terminal : execution = .terminated (.processExit spike3ResourceFailureExitCode) final events) :
      NativePlannedExecutionOutcome target context environment storageCapacity readCapacity chunks plan execution
  | success {arena : NativeArenaCapability} {initial finalFrame : SmolAllocatorFrame}
      {liveFinal : List (NativeAllocationOwner × UInt64)}
      (completed : NativeEOFExecution target context environment plan arena initial finalFrame liveFinal)
      (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
      (ready : nativePreparationOutcome evidence = .ready)
      (final : X86_64MachineState) (events : List AnyEvent)
      (terminal : execution = .terminated (.processExit 0) final events) :
      NativePlannedExecutionOutcome target context environment storageCapacity readCapacity chunks plan execution

/-- A production realization of the successfully completed prefix of a
failing plan.  It includes the application continuations between allocator
calls and the selected prefix that reaches the next refused call. -/
structure NativeProductionOperationRefusal (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (arena : NativeArenaCapability) {stored : List (List UInt8)}
    (plan : NativePreparationPlan stored) (initial : SmolAllocatorFrame) where
  refusal : NativeOperationRefusal arena plan initial
  machineBefore : X86_64MachineState
  eventsBefore : List AnyEvent
  completed : NativeProductionOperationTrace target context environment arena initial []
    (nativePreparationEntry target context environment) [] refusal.completedOperations
      refusal.beforeFailure refusal.liveBeforeFailure machineBefore eventsBefore
  failed : NativeLinkedMalloc target context environment arena refusal.nextPurpose.request
    refusal.beforeFailure refusal.beforeFailure .refused
  machineExact : failed.call.machineBefore = machineBefore
  fuel : Nat
  reachesFailedCall : NativePreparationPrefix target context environment fuel machineBefore eventsBefore
    failed.call.machineAfter eventsBefore []

/-- One decomposed execution of the selected artifact from loader entry through
the physical reads, application continuations, allocator plan, and terminal
state.  The fuel equation is tied directly to `runNativePreparation`; it is
not a second evaluator. -/
structure NativePreparationProductionExecution (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8))
    {stored : List (List UInt8)} (plan : NativePreparationPlan stored)
    (execution : NativeRunOutcome AnyEvent) where
  reads : ChunksOf environment.stdin.toList readCapacity chunks
  readInitial : X86_64MachineState
  readInitialEvents : List AnyEvent
  loaderFuel : Nat
  loader : NativePreparationPrefix target context environment loaderFuel
    (nativePreparationEntry target context environment) [] readInitial readInitialEvents []
  readFinal : X86_64MachineState
  readFinalEvents : List AnyEvent
  readTrace : NativeProductionReadTrace target context environment readCapacity readInitial
    readInitialEvents chunks readFinal readFinalEvents
  arena : NativeArenaCapability
  allocatorInitial : SmolAllocatorFrame
  allocatorFinal : SmolAllocatorFrame
  liveFinal : List (NativeAllocationOwner × UInt64)
  applicationFuel : Nat
  applicationInitial : X86_64MachineState
  applicationEvents : List AnyEvent
  readToAllocator : NativePreparationPrefix target context environment applicationFuel readFinal
    readFinalEvents applicationInitial applicationEvents []
  operationsFinal : X86_64MachineState
  operationsEvents : List AnyEvent
  operations : NativeProductionOperationTrace target context environment arena allocatorInitial []
    applicationInitial applicationEvents plan.operations allocatorFinal liveFinal operationsFinal operationsEvents
  operationOccurrencesExact : operations.mallocIdentities = plan.mallocOccurrences
  terminalFuel : Nat
  terminalFinal : X86_64MachineState
  terminalEvents : List AnyEvent
  terminalContinuation : NativePreparationPrefix target context environment terminalFuel operationsFinal
    operationsEvents terminalFinal terminalEvents []
  loaderGhost : NativePreparationGhostState plan
  readGhost : NativePreparationGhostState plan
  scanGhost : NativePreparationGhostState plan
  writeGhost : NativePreparationGhostState plan
  loaderToRead : NativePreparationBlockContract target context environment plan .loader .read
    loaderGhost readGhost (nativePreparationEntry target context environment) readInitial [] readInitialEvents
  loaderContractFuel : loaderToRead.fuel = loaderFuel
  readToScan : NativePreparationBlockContract target context environment plan .read .scan
    readGhost scanGhost readFinal applicationInitial readFinalEvents applicationEvents
  readContractFuel : readToScan.fuel = applicationFuel
  scanToSort : NativePreparationBlockContract target context environment plan .scan .sort
    scanGhost writeGhost applicationInitial operationsFinal applicationEvents operationsEvents
  sortToWrite : NativePreparationBlockContract target context environment plan .sort .write
    writeGhost writeGhost operationsFinal terminalFinal operationsEvents terminalEvents
  writeContractFuel : sortToWrite.fuel = terminalFuel
  fuel : Nat
  fuelExact : fuel = loaderFuel + readTrace.totalFuel + applicationFuel + operations.totalFuel + terminalFuel
  runnerExact : runNativePreparation target context environment fuel = execution
  outcome : NativePlannedExecutionOutcome target context environment storageCapacity readCapacity chunks plan execution
/-- An early refusal is a real terminal execution but has no stdin plan: its
failure happened before the first 512-byte read. -/
inductive NativeStartupRefusal : NativePreparationEvidence target context environment
    storageCapacity readCapacity chunks → Prop where
  | reservation (h : nativeReservationOutcome context = .refused) :
      NativeStartupRefusal (.reservationRefused (target := target) (context := context)
        (environment := environment) (storageCapacity := storageCapacity)
        (readCapacity := readCapacity) (chunks := chunks) h)
  | readBuffer {arena initial} {reservation : NativeReservationEvidence target context arena}
      {initialFrame : NativeAllocatorInitialFrame arena initial} {refused : NativeAllocatorCall arena
        NativeMallocPurpose.startupReadBuffer.request initial initial .refused} :
      NativeStartupRefusal (.startupReadBufferRefused arena reservation initial initialFrame refused)
  | lineBuffer {arena initial afterRead} {reservation : NativeReservationEvidence target context arena}
      {initialFrame : NativeAllocatorInitialFrame arena initial} {readBuffer : NativeAllocatorCall arena
        NativeMallocPurpose.startupReadBuffer.request initial afterRead .allocated}
      {payload : readBuffer.machineAfter.gprs .rax ≠ 0} {refused : NativeAllocatorCall arena
        NativeMallocPurpose.startupLineBuffer.request afterRead afterRead .refused} :
      NativeStartupRefusal (.startupLineBufferRefused arena reservation initial afterRead initialFrame readBuffer payload refused)

/-- Complete selected-artifact refinement.  Only the `planned` constructor
can observe stdin: it carries the unique lossless plan and an ordered physical
read trace.  The startup arm deliberately has neither. -/
inductive NativePreparationExecutionRefinement (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8)) : Prop where
  | startupRefusal (fuel : Nat) (execution : NativeRunOutcome AnyEvent)
      (runnerExact : runNativePreparation target context environment fuel = execution)
      (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
      (startup : NativeStartupRefusal evidence) (final : X86_64MachineState) (events : List AnyEvent)
      (terminal : execution = .terminated (.processExit spike3ResourceFailureExitCode) final events) :
      NativePreparationExecutionRefinement target context environment storageCapacity readCapacity chunks
  | planned {stored : List (List UInt8)}
      (plan : NativePreparationPlan stored)
      (inputExact : plan.records = decodeNativeRecords environment.stdin)
      (execution : NativeRunOutcome AnyEvent)
      (production : NativePreparationProductionExecution target context environment storageCapacity
        readCapacity chunks plan execution) :
      NativePreparationExecutionRefinement target context environment storageCapacity readCapacity chunks

/-- A planned result has exactly the lines decoded from the sole stdin oracle. -/
theorem NativePreparationExecutionRefinement.planned_lines_exact
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    {stored : List (List UInt8)}
    {plan : NativePreparationPlan stored}
    {inputExact : plan.records = decodeNativeRecords environment.stdin}
    {execution : NativeRunOutcome AnyEvent}
    {production : NativePreparationProductionExecution target context environment storageCapacity
      readCapacity chunks plan execution} :
    stored = environmentInputLines environment := by
  rw [← plan.recordsExact, inputExact]
  exact decodeNativeRecords_lines environment.stdin

/-- The logical `ChunksOf` schedule in a planned result is the same sequence
indexed by its physical selected-artifact read trace. -/
theorem NativePreparationExecutionRefinement.planned_read_chunks_exact
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    {stored : List (List UInt8)}
    {plan : NativePreparationPlan stored}
    {inputExact : plan.records = decodeNativeRecords environment.stdin}
    {execution : NativeRunOutcome AnyEvent}
    {production : NativePreparationProductionExecution target context environment storageCapacity
      readCapacity chunks plan execution} :
    chunks.flatten = environment.stdin.toList := production.reads.flatten_eq_total

/-- Concrete, non-sample reservation contexts used to exercise both target
ABIs.  They keep the witness at the actual platform bases and 64 KiB request,
rather than postulating an abstract arena. -/
def spike3ConcreteExecutionContext : Spike3NativeExecutionContext :=
  { arenaGrant := ⟨65536⟩, proofBudget := ⟨0⟩ }

def spike3ConcreteLinuxArena : NativeArenaCapability :=
  { base := 0x70000000, endExclusive := 0x70010000 }

def spike3ConcreteWindowsArena : NativeArenaCapability :=
  { base := 0x20000000, endExclusive := 0x20010000 }

end Spikes.Spike3SortLines

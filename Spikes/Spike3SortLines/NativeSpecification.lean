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

import Spikes.Spike3SortLines.Composition
import Spikes.Spike3SortLines.NativeRuntime
import Stdlib.SmolAlloc.Equivalence

/-!
Phase-indexed native preparation evidence shared by the Linux and Win32 bridges.

An accepted OS reservation is not preparation success.  The evidence below
follows the actual phases: a refused reservation stops immediately; an admitted
reservation exposes classified ingestion; completed ingestion exposes the exact
descriptor-table allocation result.  Every actual allocator request is carried
through `smolFreshAllocationOutcome`, which includes the implementation's
rounding, header, and finite-arena boundary checks.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform
open Stdlib.SmolAlloc
open Gasm.Targets.X86_64

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Classification of the initial fallible OS reservation alone.  This is intentionally not the
whole preparation outcome: storing a line or allocating its sort-table descriptor may still
exhaust the already-reserved arena. -/
inductive NativeReservationOutcome where
  | admitted
  | refused
  deriving DecidableEq, BEq

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The caller-selected initial reservation result. -/
def nativeReservationOutcome (context : Spike3NativeExecutionContext) : NativeReservationOutcome :=
  if context.arenaGrant.admits context.arenaGrant.requestedBytes.toUInt64 then .admitted else .refused

/-- The native target determines both the reservation instruction and the arena base it returns.
Keeping this index on preparation evidence prevents a Linux `mmap` witness from establishing a
Win32 `VirtualAlloc` preparation (or conversely). -/
inductive NativePreparationTarget where
  | linux
  | windows
  deriving DecidableEq, BEq

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- A finite arena actually returned by the target's admitted reservation transition.  The
constructors retain the concrete platform call and its returned register value, including the
fixed target base, rather than merely recording an arbitrary `ofReservation` extent. -/
inductive NativeReservationEvidence : (target : NativePreparationTarget) →
    (context : Spike3NativeExecutionContext) → NativeArenaCapability → Type 1 where
  | linux {context arena}
      (admitted : nativeReservationOutcome context = .admitted)
      (exactReservation : NativeArenaCapability.ofReservation 0x70000000
        context.arenaGrant.requestedBytes.toUInt64 = some arena)
      (state : X86_64MachineState)
      (request : state.gprs .rsi = context.arenaGrant.requestedBytes.toUInt64)
      (returned : (spike3LinuxMmapHook (Event := AnyEvent) context.arenaGrant state).1.gprs .rax =
        arena.base) : NativeReservationEvidence .linux context arena
  | windows {context arena}
      (admitted : nativeReservationOutcome context = .admitted)
      (exactReservation : NativeArenaCapability.ofReservation 0x20000000
        context.arenaGrant.requestedBytes.toUInt64 = some arena)
      (state : X86_64MachineState)
      (request : state.gprs .rdx = context.arenaGrant.requestedBytes.toUInt64)
      (returned : (spike3VirtualAllocHook (Event := AnyEvent) context.arenaGrant state).1.gprs .rax =
        arena.base) : NativeReservationEvidence .windows context arena

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- The concrete allocator frame installed immediately after an admitted reservation.  It starts
at the returned arena base with an empty free list, exactly as the native lowerings initialize
`r11` and `r10`; no arbitrary or wrapped initial bump is accepted. -/
structure NativeAllocatorInitialFrame (arena : NativeArenaCapability) (frame : SmolAllocatorFrame) where
  bumpAtArenaBase : frame.bump = arena.base
  freeListEmpty : frame.freeHead = 0

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- Exact native `smol_malloc` request pair made for one retained source line: the NUL-terminated
payload followed by the 24-byte `LineNode`.  Staging-buffer growth requests remain in the same
ledger but are not substituted for these source-derived requests. -/
def nativeRetainedLineRequests (line : List UInt8) : List UInt64 :=
  [line.length.toUInt64 + 1, 24]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- The retained-line request sequence in native allocation order. -/
def nativeRetainedLinesRequests (stored : List (List UInt8)) : List UInt64 :=
  stored.flatMap nativeRetainedLineRequests

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- The actual native descriptor table has sixteen-byte slots (pointer, length, next/order
metadata), so the lowered `shl rcx, 4` request is exactly this UInt64 product. -/
def nativeSortTableRequest (stored : List (List UInt8)) : UInt64 :=
  stored.length.toUInt64 * 16

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Result classification of one actual invocation of the emitted `smol_malloc` routine. -/
inductive NativeAllocatorCallResult where
  | allocated
  | refused

/-- Projection of the actual emitted allocator call, including its machine trace and all
persistent allocator state.  This is intentionally not the old fresh-only arithmetic model:
the trace executes the real routine, so header writes and free-list reuse remain represented in
the before/after memory and register frames. -/
structure NativeAllocatorCall (arena : NativeArenaCapability) (request : UInt64)
    (before after : SmolAllocatorFrame) (result : NativeAllocatorCallResult) where
  machineBefore : X86_64MachineState
  machineAfter : X86_64MachineState
  entry : machineBefore.rip = 0x1000
  requestInstalled : machineBefore.gprs .rcx = request
  arenaBaseInstalled : machineBefore.gprs .r11 = before.bump
  arenaEndInstalled : machineBefore.gprs .r15 = arena.endExclusive
  freeListInstalled : machineBefore.gprs .r10 = before.freeHead
  memoryInstalled : machineBefore.memory = before.memory
  executes : runProgramWithLoops 0x1000 smolMallocInstructions 30 machineBefore = machineAfter
  bumpProjected : machineAfter.gprs .r11 = after.bump
  freeListProjected : machineAfter.gprs .r10 = after.freeHead
  memoryProjected : machineAfter.memory = after.memory
  resultProjected : match result with
    | .allocated => machineAfter.gprs .rax ≠ 0
    | .refused => machineAfter.gprs .rax = 0

/-- Projection of one actual emitted `smol_free` call.  Preparation's staging-buffer growth
frees are retained in the same ledger as subsequent allocations, so a later reuse cannot be
silently modelled as a fresh bump allocation. -/
structure NativeAllocatorFreeCall (before after : SmolAllocatorFrame) (payload : UInt64) where
  machineBefore : X86_64MachineState
  machineAfter : X86_64MachineState
  entry : machineBefore.rip = 0x1000
  payloadInstalled : machineBefore.gprs .rcx = payload
  bumpInstalled : machineBefore.gprs .r11 = before.bump
  freeListInstalled : machineBefore.gprs .r10 = before.freeHead
  memoryInstalled : machineBefore.memory = before.memory
  executes : runProgramWithLoops 0x1000 smolFreeInstructions 30 machineBefore = machineAfter
  bumpProjected : machineAfter.gprs .r11 = after.bump
  freeListProjected : machineAfter.gprs .r10 = after.freeHead
  memoryProjected : machineAfter.memory = after.memory

/-- A full ordered trace of allocation calls.  Its adjacent frame indices retain every concrete
header write and free-list update made by the emitted allocator, including `smol_free` transitions;
it is not a payload-only budget. -/
inductive NativeAllocationLedger (arena : NativeArenaCapability) :
    SmolAllocatorFrame → List UInt64 → SmolAllocatorFrame → Prop where
  | empty (frame : SmolAllocatorFrame) : NativeAllocationLedger arena frame [] frame
  | allocated {before after finish : SmolAllocatorFrame} {request : UInt64} {requests : List UInt64}
      (call : NativeAllocatorCall arena request before after .allocated)
      (rest : NativeAllocationLedger arena after requests finish) :
      NativeAllocationLedger arena before (request :: requests) finish
  | freed {before after finish : SmolAllocatorFrame} {requests : List UInt64} {payload : UInt64}
      (call : NativeAllocatorFreeCall before after payload)
      (rest : NativeAllocationLedger arena after requests finish) :
      NativeAllocationLedger arena before requests finish

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- A concrete refused request after an exact successful call trace.  The refusal is the actual
emitted `smol_malloc` return value, and `unchanged` retains its no-publication frame result. -/
structure NativeAllocationFailure (arena : NativeArenaCapability) (start : SmolAllocatorFrame) where
  successfulRequests : List UInt64
  beforeFailure : SmolAllocatorFrame
  successful : NativeAllocationLedger arena start successfulRequests beforeFailure
  failedRequest : UInt64
  refused : NativeAllocatorCall arena failedRequest beforeFailure beforeFailure .refused

/-- Exact finite request schedule for retained lines.  Staging allocations may occur between
retained-line requests, but every retained line contributes its concrete payload/node pair in
order; this replaces the prior weak `Sublist` assertion. -/
inductive NativeRetainedRequestSchedule : List (List UInt8) → List UInt64 → Prop where
  | done : NativeRetainedRequestSchedule [] []
  | staging {lines : List (List UInt8)} {requests : List UInt64} (request : UInt64)
      (rest : NativeRetainedRequestSchedule lines requests) :
      NativeRetainedRequestSchedule lines (request :: requests)
  | retained {line : List UInt8} {lines : List (List UInt8)} {requests : List UInt64}
      (rest : NativeRetainedRequestSchedule lines requests) :
      NativeRetainedRequestSchedule (line :: lines) (nativeRetainedLineRequests line ++ requests)

/-- The exact allocation site at which ingestion of a first refused line can stop.  A staging
buffer request remains explicit rather than being incorrectly folded into either retained object
allocation. -/
inductive NativeIngestionFailureSite (first : List UInt8) where
  | staging (request : UInt64)
  | payload : NativeIngestionFailureSite first
  | node : NativeIngestionFailureSite first

def NativeIngestionFailureSite.request {first : List UInt8} :
    NativeIngestionFailureSite first → UInt64
  | .staging request => request
  | .payload => first.length.toUInt64 + 1
  | .node => 24

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The complete phase-indexed evidence for one finite native invocation.  In particular,
reservation refusal carries no fictional ingestion/table result, and a completed ingestion must
carry an exact descriptor-table allocation result.  A target execution proof must establish that
its concrete calls refine these ledgers; this module does not synthesize one. -/
inductive NativePreparationEvidence (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8)) where
  | reservationRefused
      (reservation : nativeReservationOutcome context = .refused) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | ingestionRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult storageCapacity []
        (environmentInputLines environment))
      (prepared untouchedTail : List (List UInt8)) (first : List UInt8)
      (ingestionRefused : ingestion = .refused prepared first untouchedTail)
      (allocationFailure : NativeAllocationFailure arena initial)
      (successfulPrefixExact : NativeRetainedRequestSchedule prepared
        allocationFailure.successfulRequests)
      (failureSite : NativeIngestionFailureSite first)
      (failedRequestExact : allocationFailure.failedRequest = failureSite.request) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | sortTableRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial afterIngestion : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult storageCapacity []
        (environmentInputLines environment))
      (stored : List (List UInt8)) (ingestionCompleted : ingestion = .completed stored)
      (ingestionRequests : List UInt64)
      (ingestionLedger : NativeAllocationLedger arena initial ingestionRequests afterIngestion)
      (retainedRequests : NativeRetainedRequestSchedule stored ingestionRequests)
      (tableRequest : UInt64) (tableRequestExact : tableRequest = nativeSortTableRequest stored)
      (tableRefused : NativeAllocatorCall arena tableRequest afterIngestion afterIngestion .refused) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | ready
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial afterIngestion afterTable : SmolAllocatorFrame)
      (initialFrame : NativeAllocatorInitialFrame arena initial)
      (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult storageCapacity []
        (environmentInputLines environment))
      (stored : List (List UInt8)) (ingestionCompleted : ingestion = .completed stored)
      (ingestionRequests : List UInt64)
      (ingestionLedger : NativeAllocationLedger arena initial ingestionRequests afterIngestion)
      (retainedRequests : NativeRetainedRequestSchedule stored ingestionRequests)
      (tableRequest : UInt64)
      (tableRequestExact : tableRequest = nativeSortTableRequest stored)
      (tableAllocated : NativeAllocatorCall arena tableRequest afterIngestion afterTable .allocated) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Final native preparation classification.  Only the final phase-indexed constructor reaches
`.ready`; all resource refusals remain the specified abort arm. -/
def nativePreparationOutcome {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks) :
    Spike3PreparationOutcome :=
  match evidence with
  | .ready .. => .ready
  | .reservationRefused .. | .ingestionRefused .. | .sortTableRefused .. => .exhausted

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The ready constructor exposes its exact target-owned allocation ledger and concrete final
table request.  This is the only allocation authority carried into the source ready arm. -/
theorem nativePreparationEvidence_ready_ledger
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
    (ready : nativePreparationOutcome evidence = .ready) :
    ∃ (arena : NativeArenaCapability) (initial afterIngestion afterTable : SmolAllocatorFrame)
      (ingestion : AppendLinesResult (List UInt8)) (stored : List (List UInt8))
      (ingestionRequests : List UInt64) (tableRequest : UInt64)
      (reservation : NativeReservationEvidence target context arena)
      (initialFrame : NativeAllocatorInitialFrame arena initial),
      ingestion = appendLinesResult storageCapacity [] (environmentInputLines environment) ∧
        ingestion = .completed stored ∧
      NativeAllocationLedger arena initial ingestionRequests afterIngestion ∧
      NativeRetainedRequestSchedule stored ingestionRequests ∧
      tableRequest = nativeSortTableRequest stored ∧
      Nonempty (NativeAllocatorCall arena tableRequest afterIngestion afterTable .allocated) := by
  cases evidence with
  | reservationRefused => simp [nativePreparationOutcome] at ready
  | ingestionRefused => simp [nativePreparationOutcome] at ready
  | sortTableRefused => simp [nativePreparationOutcome] at ready
  | ready arena reservation initial afterIngestion afterTable initialFrame reads ingestion ingestionExact
      stored ingestionCompleted ingestionRequests ingestionLedger retainedRequests tableRequest
      tableRequestExact tableAllocated =>
    exact ⟨arena, initial, afterIngestion, afterTable, ingestion, stored, ingestionRequests,
      tableRequest, reservation, initialFrame, ingestionExact, ingestionCompleted, ingestionLedger,
      retainedRequests, tableRequestExact, ⟨tableAllocated⟩⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The independent whole-program specification receives only the combined phase-indexed
preparation classification, never reservation admission by itself. -/
def nativeSpike3Spec {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
    (output : Spike3OutputOutcome) : Spike3ByteSortOutcome :=
  spike3ByteSortSpec environment (nativePreparationOutcome evidence) output

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A bridge that has established the combined ready result may use the pure bounded-ingestion
success law for every finite environment input. -/
theorem boundedLineSortOutcome_agrees_native_ready_accepted
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
    (capacity : Nat) (lines : List (List UInt8))
    (ready : nativePreparationOutcome evidence = .ready)
    (input : environmentInputLines environment = lines) (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .accepted =
      nativeSpike3Spec evidence .accepted := by
  unfold nativeSpike3Spec
  rw [ready]
  exact boundedLineSortOutcome_of_fits_agrees_ready_accepted environment capacity lines input fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Output refusal remains the selected native specification outcome after a combined ready
preparation result; it cannot be folded into any allocation failure. -/
theorem boundedLineSortOutcome_agrees_native_ready_refused
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
    (capacity : Nat) (lines : List (List UInt8))
    (ready : nativePreparationOutcome evidence = .ready)
    (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .refused =
      nativeSpike3Spec evidence .refused := by
  unfold nativeSpike3Spec
  rw [ready, spike3ByteSortSpec_output_refused]
  exact boundedLineSortOutcome_of_fits_refused capacity lines fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Every combined preparation abort has no success or output-prefix payload, independently of
the caller's finite stdin. -/
theorem nativeSpike3Spec_exhausted
    {target : NativePreparationTarget} {context : Spike3NativeExecutionContext}
    {environment : Environment} {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence target context environment storageCapacity readCapacity chunks)
    (output : Spike3OutputOutcome)
    (exhausted : nativePreparationOutcome evidence = .exhausted) :
    nativeSpike3Spec evidence output = .preparationFailure := by
  unfold nativeSpike3Spec
  rw [exhausted, spike3ByteSortSpec_exhausted]

end Spikes.Spike3SortLines

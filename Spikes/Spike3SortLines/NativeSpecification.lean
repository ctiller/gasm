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
import Gasm.Targets.X86_64.Assembler

/-!
Phase-indexed native preparation evidence shared by the Linux and Win32 bridges.

An accepted OS reservation is not preparation success.  The evidence below
follows the actual phases: a refused reservation stops immediately; an admitted
reservation exposes classified ingestion; completed ingestion exposes the exact
descriptor-table allocation result.  `smolFreshAllocationOutcome` is only the
fresh-allocation guard model; this module records full emitted malloc/free calls
and their frame transitions so header writes and free-list reuse are not erased.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform
open Stdlib.SmolAlloc
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler

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
metadata), so this is the lowered `shl rcx, 4` *UInt64* request.  It is modular by definition;
`NativeTableRequestFits` is carried by a successful nonempty preparation before treating it as a
nonwrapping mathematical `count * 16` allocation. -/
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
  /-- The allocator RIP is a link-time coordinate.  It must not be fixed to
      the standalone routine's old `0x1000` test base: the selected native
      artifact embeds this exact code at its own linked address. -/
  entryRip : UInt64
  entry : machineBefore.rip = entryRip
  instructions : List X86_64Instr
  /-- Reassemble the allocator's one symbolic body at the *linked* entry.
      Relative branch displacements are consequently those in the selected
      final artifact, not those of the historical standalone `0x1000` probe. -/
  instructionIdentity : instructions = assembleProgram entryRip smolMallocSymbolicProgram
  requestInstalled : machineBefore.gprs .rcx = request
  arenaBaseInstalled : machineBefore.gprs .r11 = before.bump
  arenaEndInstalled : machineBefore.gprs .r15 = arena.endExclusive
  freeListInstalled : machineBefore.gprs .r10 = before.freeHead
  memoryInstalled : machineBefore.memory = before.memory
  executes : runProgramWithLoops entryRip instructions 30 machineBefore = machineAfter
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
  entryRip : UInt64
  entry : machineBefore.rip = entryRip
  instructions : List X86_64Instr
  instructionIdentity : instructions = assembleProgram entryRip smolFreeSymbolicProgram
  payloadInstalled : machineBefore.gprs .rcx = payload
  bumpInstalled : machineBefore.gprs .r11 = before.bump
  freeListInstalled : machineBefore.gprs .r10 = before.freeHead
  memoryInstalled : machineBefore.memory = before.memory
  executes : runProgramWithLoops entryRip instructions 30 machineBefore = machineAfter
  bumpProjected : machineAfter.gprs .r11 = after.bump
  freeListProjected : machineAfter.gprs .r10 = after.freeHead
  memoryProjected : machineAfter.memory = after.memory

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Every allocation in native preparation is named by its emitted call site.  This is an
operation trace, rather than an embedding of source requests into an arbitrary list: the
purpose determines the exact request and the order records intervening frees. -/
inductive NativeMallocPurpose where
  | startupReadBuffer
  | startupLineBuffer
  | growLineBuffer (oldCapacity : UInt64)
  | retainedPayload (line : List UInt8)
  | retainedNode (line : List UInt8)
  | sortTable (stored : List (List UInt8))

/-- The emitted call site, rather than its byte count, identifies the role of
one allocator invocation.  In particular, two equal source lines produce two
different `retainedPayload` occurrences even though their requests coincide. -/
inductive NativeMallocCallsite where
  | startupReadBuffer | startupLineBuffer | growLineBuffer
  | retainedPayload | retainedNode | sortTable
  deriving DecidableEq

def NativeMallocPurpose.callsite : NativeMallocPurpose → NativeMallocCallsite
  | .startupReadBuffer => .startupReadBuffer
  | .startupLineBuffer => .startupLineBuffer
  | .growLineBuffer _ => .growLineBuffer
  | .retainedPayload _ => .retainedPayload
  | .retainedNode _ => .retainedNode
  | .sortTable _ => .sortTable

/-- A purpose occurrence is named by its lowered call site and its ordinal at
that site.  Request sizes are deliberately not part of this identity. -/
structure NativeMallocOccurrence where
  callsite : NativeMallocCallsite
  /-- The instruction address of the lowered caller, rather than the common
      allocator entry address.  This distinguishes growth, payload, node and
      table calls even when they request equal byte counts. -/
  callsiteRip : UInt64
  occurrence : Nat
  purpose : NativeMallocPurpose
  callsiteExact : purpose.callsite = callsite

/-- The ordinal is derived from the preceding ledger entries at the same
callsite.  It is deliberately independent of request size: equal length
records still have different `(callsite, occurrence)` identities. -/
def NativeMallocOccurrencesOrdinalFrom (seen : List NativeMallocOccurrence) :
    List NativeMallocOccurrence → Prop
  | [] => True
  | current :: rest =>
      current.occurrence = (seen.filter (fun prior => prior.callsite == current.callsite)).length ∧
        NativeMallocOccurrencesOrdinalFrom (seen ++ [current]) rest

def NativeMallocOccurrencesOrdinals (occurrences : List NativeMallocOccurrence) : Prop :=
  NativeMallocOccurrencesOrdinalFrom [] occurrences

def NativeMallocPurpose.request : NativeMallocPurpose → UInt64
  | .startupReadBuffer => 512
  | .startupLineBuffer => 256
  | .growLineBuffer oldCapacity => oldCapacity + 256
  | .retainedPayload line => line.length.toUInt64 + 1
  | .retainedNode _ => 24
  | .sortTable stored => nativeSortTableRequest stored

/-- The allocation owning a live native payload.  Free operations name this owner as well as the
payload address, preventing an EOF/growth free from being justified by an unrelated allocation. -/
inductive NativeAllocationOwner where
  | startupReadBuffer
  | lineBuffer (capacity : UInt64)
  | retainedPayload (line : List UInt8)
  | retainedNode (line : List UInt8)
  | sortTable (stored : List (List UInt8))
  deriving DecidableEq

def NativeMallocPurpose.owner : NativeMallocPurpose → NativeAllocationOwner
  | .startupReadBuffer => .startupReadBuffer
  | .startupLineBuffer => .lineBuffer 256
  | .growLineBuffer oldCapacity => .lineBuffer (oldCapacity + 256)
  | .retainedPayload line => .retainedPayload line
  | .retainedNode line => .retainedNode line
  | .sortTable stored => .sortTable stored

/-- `smol_free` sites are retained in the preparation trace because free-list reuse affects a
later malloc result.  A growth step therefore cannot be treated as a fresh-only allocation. -/
inductive NativeFreePurpose where
  | replaceLineBuffer (oldCapacity : UInt64)
  | eofReadBuffer
  | eofLineBuffer (capacity : UInt64)

def NativeFreePurpose.owner : NativeFreePurpose → NativeAllocationOwner
  | .replaceLineBuffer capacity => .lineBuffer capacity
  | .eofReadBuffer => .startupReadBuffer
  | .eofLineBuffer capacity => .lineBuffer capacity

inductive NativePreparationOperation where
  | malloc (purpose : NativeMallocPurpose)
  | free (purpose : NativeFreePurpose) (payload : UInt64)

def NativePreparationOperation.request? : NativePreparationOperation → Option UInt64
  | .malloc purpose => some purpose.request
  | .free .. => none

def NativePreparationOperation.mallocPurpose? : NativePreparationOperation → Option NativeMallocPurpose
  | .malloc purpose => some purpose
  | .free .. => none

/-- An ordered projection of actual `smol_malloc`/`smol_free` executions.  Adjacent allocator
frames include all header writes and free-list reuse, while the `live` indices ensure each free
uses the exact pointer returned by the preceding allocation of its named owner. -/
inductive NativeOperationTrace (arena : NativeArenaCapability) :
    SmolAllocatorFrame → List (NativeAllocationOwner × UInt64) →
      List NativePreparationOperation → SmolAllocatorFrame → List (NativeAllocationOwner × UInt64) → Prop where
  | empty (frame : SmolAllocatorFrame) (live : List (NativeAllocationOwner × UInt64)) :
      NativeOperationTrace arena frame live [] frame live
  | malloc {before after finish : SmolAllocatorFrame} {purpose : NativeMallocPurpose}
      {payload : UInt64} {live liveFinish : List (NativeAllocationOwner × UInt64)}
      {operations : List NativePreparationOperation}
      (call : NativeAllocatorCall arena purpose.request before after .allocated)
      (returned : call.machineAfter.gprs .rax = payload)
      (rest : NativeOperationTrace arena after ((purpose.owner, payload) :: live) operations finish liveFinish) :
      NativeOperationTrace arena before live (.malloc purpose :: operations) finish liveFinish
  | free {before after finish : SmolAllocatorFrame} {purpose : NativeFreePurpose}
      {payload : UInt64} {live liveFinish : List (NativeAllocationOwner × UInt64)}
      {operations : List NativePreparationOperation}
      (owned : (purpose.owner, payload) ∈ live)
      (call : NativeAllocatorFreeCall before after payload)
      (rest : NativeOperationTrace arena after (live.erase (purpose.owner, payload)) operations finish liveFinish) :
      NativeOperationTrace arena before live (.free purpose payload :: operations) finish liveFinish

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- Bounds carried at the native boundary.  Lean `UInt64` arithmetic is modular; the phase model
therefore does not claim a mathematical request size unless this premise rules out wrapping. -/
def nativeUInt64Modulus : Nat := 18446744073709551616

/-- The scanner's growth guard is evaluated before appending each *raw*
    non-LF byte.  It must therefore be indexed by `NativeInputRecord.scanned`,
    not by the CRLF-trimmed retained line or by its later NUL-terminated payload
    request.  In particular, a 256-byte unterminated record fits a 256-byte
    scan buffer (its later 257-byte retained payload is a different malloc),
    while a 256-byte CRLF record grows when the scanner reaches its trailing
    CR. -/
def NativeRecordCapacityFits (record : NativeInputRecord) (capacity : UInt64) : Prop :=
  record.scanned.length < nativeUInt64Modulus ∧ record.scanned.length.toUInt64 ≤ capacity

def NativeGrowthSafe (capacity : UInt64) : Prop :=
  capacity ≤ 0xFFFFFFFFFFFFFFFF - 256

def NativeTableRequestFits (stored : List (List UInt8)) : Prop :=
  stored.length < nativeUInt64Modulus / 16

/-- The source-derived portion of preparation.  A growth pair is always `malloc(cap + 256)`
followed immediately by freeing the old buffer.  It can occur only for the next line which does
not fit, carries a nonwrapping bound, and recurs at the enlarged capacity; hence it cannot insert
arbitrary/zero growth steps.  Retention consumes exactly one line in input order. -/
inductive NativeIngestionOperationOrder : UInt64 → List NativeInputRecord →
    List NativePreparationOperation → UInt64 → Prop where
  | done (capacity : UInt64) : NativeIngestionOperationOrder capacity [] [] capacity
  | grow {capacity : UInt64} {record : NativeInputRecord} {records : List NativeInputRecord}
      {operations : List NativePreparationOperation} {finish : UInt64}
      (safe : NativeGrowthSafe capacity)
      (doesNotFit : ¬ NativeRecordCapacityFits record capacity)
      (oldPayload : UInt64)
      (rest : NativeIngestionOperationOrder (capacity + 256) (record :: records) operations finish) :
      NativeIngestionOperationOrder capacity (record :: records)
        (.malloc (.growLineBuffer capacity) ::
          .free (.replaceLineBuffer capacity) oldPayload :: operations) finish
  | retained {capacity finish : UInt64} {record : NativeInputRecord} {records : List NativeInputRecord}
      {operations : List NativePreparationOperation}
      (fits : NativeRecordCapacityFits record capacity)
      (rest : NativeIngestionOperationOrder capacity records operations finish) :
      NativeIngestionOperationOrder capacity (record :: records)
        (.malloc (.retainedPayload record.line) ::
          .malloc (.retainedNode record.line) :: operations) finish

/-- The complete successful operation shape.  Startup failures are modeled separately; after
both startup allocations, EOF always frees both staging buffers.  For empty input no table
allocation appears at all, while a nonempty finalized source has exactly one `count * 16` table
operation after those frees. -/
structure NativePreparationPlan (stored : List (List UInt8)) where
  /-- The lossless scanner records from the read binder.  Keeping this beside
      `stored` prevents a plan from reconstructing a pre-append growth decision
      from a CRLF-trimmed line value. -/
  records : List NativeInputRecord
  recordsExact : records.map NativeInputRecord.line = stored
  readBufferPayload : UInt64
  initialLineBufferPayload : UInt64
  ingestionOperations : List NativePreparationOperation
  finalLineCapacity : UInt64
  finalLineBufferPayload : UInt64
  ingestionExact : NativeIngestionOperationOrder 256 records ingestionOperations finalLineCapacity
  postEofOperations : List NativePreparationOperation
  postEofExact : if stored = [] then postEofOperations = [] else
    postEofOperations = [.malloc (.sortTable stored)]
  tableRequestBound : stored ≠ [] → NativeTableRequestFits stored
  operations : List NativePreparationOperation
  /-- The purpose ledger is ordered exactly as the emitted malloc operations.
      Its uniqueness is on `(callsite, occurrence)`, so equal-size requests
      cannot be substituted for one another. -/
  mallocOccurrences : List NativeMallocOccurrence
  mallocOccurrencesExact : mallocOccurrences.map NativeMallocOccurrence.purpose =
    operations.filterMap NativePreparationOperation.mallocPurpose?
  mallocOccurrencesOrdinal : NativeMallocOccurrencesOrdinals mallocOccurrences
  mallocOccurrencesDistinct : mallocOccurrences.Pairwise (fun left right =>
    left.callsite ≠ right.callsite ∨ left.occurrence ≠ right.occurrence)
  operationsExact : operations =
    .malloc .startupReadBuffer :: .malloc .startupLineBuffer :: ingestionOperations ++
      [.free .eofReadBuffer readBufferPayload,
        .free (.eofLineBuffer finalLineCapacity) finalLineBufferPayload] ++ postEofOperations

/-- A failed malloc is located at the next operation of the selected plan, after an exact prefix
of actual allocator transitions.  It cannot silently skip a source line or invent a subsequent
table result. -/
structure NativeOperationRefusal (arena : NativeArenaCapability) {stored : List (List UInt8)}
    (plan : NativePreparationPlan stored) (start : SmolAllocatorFrame) where
  completedOperations : List NativePreparationOperation
  nextPurpose : NativeMallocPurpose
  remainingOperations : List NativePreparationOperation
  beforeFailure : SmolAllocatorFrame
  liveBeforeFailure : List (NativeAllocationOwner × UInt64)
  selectedPlan : plan.operations = completedOperations ++ .malloc nextPurpose :: remainingOperations
  successful : NativeOperationTrace arena start [] completedOperations beforeFailure liveBeforeFailure
  refused : NativeAllocatorCall arena nextPurpose.request beforeFailure beforeFailure .refused

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The exact malloc purpose at the first source record which cannot be retained. -/
inductive NativeIngestionFailurePurpose (first : List UInt8) where
  | grow (oldCapacity : UInt64)
  | payload
  | node

def NativeIngestionFailurePurpose.mallocPurpose {first : List UInt8} :
    NativeIngestionFailurePurpose first → NativeMallocPurpose
  | .grow oldCapacity => .growLineBuffer oldCapacity
  | .payload => .retainedPayload first
  | .node => .retainedNode first

/-- The exact refusal position within one scanner record.  This records the
pre-append growth check as well as the later payload and node calls, so a
failure cannot be attributed merely to a same-sized allocation elsewhere in
the record or in a repeated equal line. -/
inductive NativeRecordRefusalPosition (record : NativeInputRecord) where
  | grow (oldCapacity : UInt64)
  | payload
  | node

def NativeRecordRefusalPosition.failurePurpose {record : NativeInputRecord} :
    NativeRecordRefusalPosition record → NativeIngestionFailurePurpose record.line
  | .grow capacity => .grow capacity
  | .payload => .payload
  | .node => .node

/-- The complete phase-indexed evidence for one finite native invocation.  The constructors
mirror the emitted control flow: reservation, the 512-byte startup malloc, the 256-byte startup
malloc, source ingestion, EOF staging frees, and only then a conditional nonzero table malloc.
No constructor manufactures a table request for an empty source or any later phase after a
refusal.  This remains a preparation model until an artifact-execution refinement supplies it;
platform adapters intentionally do not turn this evidence into a `VerifiedProgram` yet. -/
inductive NativePreparationEvidence (target : NativePreparationTarget)
    (context : Spike3NativeExecutionContext) (environment : Environment)
    (storageCapacity readCapacity : Nat) (chunks : List (List UInt8)) where
  | reservationRefused
      (reservation : nativeReservationOutcome context = .refused) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | startupReadBufferRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      /- Startup rejection occurs before stdin is read.  Requiring a full
          future plan here would make an early real failure depend on raw
          records that were never observed (and can be arbitrarily large). -/
      (refused : NativeAllocatorCall arena NativeMallocPurpose.startupReadBuffer.request
        initial initial .refused) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | startupLineBufferRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial afterRead : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      (readBuffer : NativeAllocatorCall arena NativeMallocPurpose.startupReadBuffer.request
        initial afterRead .allocated)
      (readBufferPayload : readBuffer.machineAfter.gprs .rax ≠ 0)
      /- As above, this second startup rejection is still before any input
          record is decoded, so it carries only its reachable startup prefix. -/
      (refused : NativeAllocatorCall arena NativeMallocPurpose.startupLineBuffer.request
        afterRead afterRead .refused) :
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
      (inputPartition : environmentInputLines environment = prepared ++ first :: untouchedTail)
      (plan : NativePreparationPlan (environmentInputLines environment))
      /- This partition is over the lossless scanner records, not merely over
          their line values.  It identifies the failed occurrence by position,
          so repeated equal lines cannot justify a prefix for another record. -/
      (preparedRecords untouchedRecords : List NativeInputRecord) (firstRecord : NativeInputRecord)
      (recordPartition : plan.records = preparedRecords ++ firstRecord :: untouchedRecords)
      (preparedExact : prepared = preparedRecords.map NativeInputRecord.line)
      (firstExact : first = firstRecord.line)
      (untouchedExact : untouchedTail = untouchedRecords.map NativeInputRecord.line)
      /- `priorRecordOperations` is the complete prefix through earlier
          records.  `prefixOperations` is the actual failing-call prefix and
          may additionally contain the current record's payload allocation
          when the node allocation is refused. -/
      (priorRecordOperations prefixOperations : List NativePreparationOperation)
      (remainingIngestionOperations : List NativePreparationOperation)
      (failurePurpose : NativeIngestionFailurePurpose first)
      (recordRefusal : NativeRecordRefusalPosition firstRecord)
      (recordPositionExact : firstExact ▸ failurePurpose = recordRefusal.failurePurpose)
      (prefixIsPriorRecords : ∃ capacity,
        NativeIngestionOperationOrder 256 preparedRecords priorRecordOperations capacity)
      (prefixShape : match recordRefusal with
        | .grow _ => prefixOperations = priorRecordOperations
        | .payload => prefixOperations = priorRecordOperations
        | .node => prefixOperations = priorRecordOperations ++ [.malloc (.retainedPayload first)])
      (ingestionPlanSplit : plan.ingestionOperations = prefixOperations ++
        .malloc failurePurpose.mallocPurpose :: remainingIngestionOperations)
      (failure : NativeOperationRefusal arena plan initial)
      (firstFailedOperation : failure.completedOperations =
        NativePreparationOperation.malloc NativeMallocPurpose.startupReadBuffer ::
          NativePreparationOperation.malloc NativeMallocPurpose.startupLineBuffer :: prefixOperations ∧
        failure.nextPurpose = failurePurpose.mallocPurpose)
      (nodePayloadImmediatelyBefore : failurePurpose = .node →
        prefixOperations = priorRecordOperations ++ [.malloc (.retainedPayload first)]) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | sortTableRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult storageCapacity []
        (environmentInputLines environment))
      (stored : List (List UInt8)) (ingestionCompleted : ingestion = .completed stored)
      (sourceExact : stored = environmentInputLines environment)
      (nonempty : stored ≠ [])
      (plan : NativePreparationPlan stored)
      (failure : NativeOperationRefusal arena plan initial)
      (tableIsNext : plan.operations = failure.completedOperations ++
        [NativePreparationOperation.malloc (NativeMallocPurpose.sortTable stored)] ++
          failure.remainingOperations ∧
        failure.nextPurpose = NativeMallocPurpose.sortTable stored) :
      NativePreparationEvidence target context environment storageCapacity readCapacity chunks
  | ready
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence target context arena)
      (initial finish : SmolAllocatorFrame)
      (initialFrame : NativeAllocatorInitialFrame arena initial)
      (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult storageCapacity []
        (environmentInputLines environment))
      (stored : List (List UInt8)) (ingestionCompleted : ingestion = .completed stored)
      (sourceExact : stored = environmentInputLines environment)
      (plan : NativePreparationPlan stored)
      (finishLive : List (NativeAllocationOwner × UInt64))
      (trace : NativeOperationTrace arena initial [] plan.operations finish finishLive) :
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
  | .reservationRefused .. | .startupReadBufferRefused .. | .startupLineBufferRefused .. |
    .ingestionRefused .. | .sortTableRefused .. => .exhausted

/-- Exactly the refusal constructors which occur after the stdin reader has
started.  Keeping this classifier on the evidence spine makes it impossible
to relabel either startup constructor as a plan-indexed refusal. -/
def NativePreparationEvidence.isPostReadRefusal {target : NativePreparationTarget}
    {context : Spike3NativeExecutionContext} {environment : Environment}
    {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)} :
    NativePreparationEvidence target context environment storageCapacity readCapacity chunks → Bool
  | .ingestionRefused .. | .sortTableRefused .. => true
  | .reservationRefused .. | .startupReadBufferRefused .. | .startupLineBufferRefused .. | .ready .. => false

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

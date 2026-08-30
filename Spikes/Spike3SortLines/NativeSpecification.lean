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

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- A finite arena actually returned by the target's admitted reservation transition.  The extent
is tied to the caller-indexed mapping request; Linux/Win32 adapters separately tie its base to
their platform return convention. -/
structure NativeReservationEvidence (context : Spike3NativeExecutionContext)
    (arena : NativeArenaCapability) where
  admitted : nativeReservationOutcome context = .admitted
  reservationBase : UInt64
  exactReservation : NativeArenaCapability.ofReservation reservationBase
    context.arenaGrant.requestedBytes.toUInt64 = some arena

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
/-- A successful finite sequence of native `smol_malloc` requests.  Each constructor records the
exact standard-library allocation outcome, so its request is rounded, header-sized, and checked
against the same concrete arena as the actual lowering. -/
inductive NativeAllocationLedger (arena : NativeArenaCapability) :
    SmolAllocatorFrame → List UInt64 → SmolAllocatorFrame → Prop where
  | empty (frame : SmolAllocatorFrame) : NativeAllocationLedger arena frame [] frame
  | allocated {before after finish : SmolAllocatorFrame} {request : UInt64} {requests : List UInt64}
      (step : smolFreshAllocationOutcome request arena before = .allocated after)
      (rest : NativeAllocationLedger arena after requests finish) :
      NativeAllocationLedger arena before (request :: requests) finish

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- A concrete failed request after an exact successful ledger prefix.  The standard allocator
model guarantees that the failed result retains `before`, so no post-failure allocation state is
invented. -/
structure NativeAllocationFailure (arena : NativeArenaCapability) (start : SmolAllocatorFrame) where
  successfulRequests : List UInt64
  beforeFailure : SmolAllocatorFrame
  successful : NativeAllocationLedger arena start successfulRequests beforeFailure
  failedRequest : UInt64
  refused : smolFreshAllocationOutcome failedRequest arena beforeFailure = .failed beforeFailure

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The complete phase-indexed evidence for one finite native invocation.  In particular,
reservation refusal carries no fictional ingestion/table result, and a completed ingestion must
carry an exact descriptor-table allocation result.  A target execution proof must establish that
its concrete calls refine these ledgers; this module does not synthesize one. -/
inductive NativePreparationEvidence (context : Spike3NativeExecutionContext)
    (lineCapacity : Nat) (lines : List (List UInt8)) where
  | reservationRefused
      (reservation : nativeReservationOutcome context = .refused) :
      NativePreparationEvidence context lineCapacity lines
  | ingestionRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence context arena)
      (initial : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult lineCapacity [] lines)
      (prepared untouchedTail : List (List UInt8)) (first : List UInt8)
      (ingestionRefused : ingestion = .refused prepared first untouchedTail)
      (allocationFailure : NativeAllocationFailure arena initial) :
      NativePreparationEvidence context lineCapacity lines
  | sortTableRefused
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence context arena)
      (initial afterIngestion : SmolAllocatorFrame) (initialFrame : NativeAllocatorInitialFrame arena initial)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult lineCapacity [] lines)
      (stored : List (List UInt8)) (ingestionCompleted : ingestion = .completed stored)
      (ingestionRequests : List UInt64)
      (ingestionLedger : NativeAllocationLedger arena initial ingestionRequests afterIngestion)
      (retainedRequests : (nativeRetainedLinesRequests stored).Sublist ingestionRequests)
      (tableRequest : UInt64) (tableRequestExact : tableRequest = nativeSortTableRequest stored)
      (tableRefused : smolFreshAllocationOutcome tableRequest arena afterIngestion = .failed afterIngestion) :
      NativePreparationEvidence context lineCapacity lines
  | ready
      (arena : NativeArenaCapability) (reservation : NativeReservationEvidence context arena)
      (initial afterIngestion afterTable : SmolAllocatorFrame)
      (initialFrame : NativeAllocatorInitialFrame arena initial)
      (ingestion : AppendLinesResult (List UInt8))
      (ingestionExact : ingestion = appendLinesResult lineCapacity [] lines)
      (stored : List (List UInt8)) (ingestionCompleted : ingestion = .completed stored)
      (ingestionRequests : List UInt64)
      (ingestionLedger : NativeAllocationLedger arena initial ingestionRequests afterIngestion)
      (retainedRequests : (nativeRetainedLinesRequests stored).Sublist ingestionRequests)
      (tableRequest : UInt64)
      (tableRequestExact : tableRequest = nativeSortTableRequest stored)
      (tableAllocated : smolFreshAllocationOutcome tableRequest arena afterIngestion = .allocated afterTable) :
      NativePreparationEvidence context lineCapacity lines

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Final native preparation classification.  Only the final phase-indexed constructor reaches
`.ready`; all resource refusals remain the specified abort arm. -/
def nativePreparationOutcome {context : Spike3NativeExecutionContext}
    {lineCapacity : Nat} {lines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity lines) : Spike3PreparationOutcome :=
  match evidence with
  | .ready .. => .ready
  | .reservationRefused .. | .ingestionRefused .. | .sortTableRefused .. => .exhausted

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The ready constructor exposes its exact target-owned allocation ledger and concrete final
table request.  This is the only allocation authority carried into the source ready arm. -/
theorem nativePreparationEvidence_ready_ledger
    {context : Spike3NativeExecutionContext} {lineCapacity : Nat} {lines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity lines)
    (ready : nativePreparationOutcome evidence = .ready) :
    ∃ (arena : NativeArenaCapability) (initial afterIngestion afterTable : SmolAllocatorFrame)
      (ingestion : AppendLinesResult (List UInt8)) (stored : List (List UInt8))
      (ingestionRequests : List UInt64) (tableRequest : UInt64)
      (reservation : NativeReservationEvidence context arena)
      (initialFrame : NativeAllocatorInitialFrame arena initial),
      ingestion = appendLinesResult lineCapacity [] lines ∧ ingestion = .completed stored ∧
      NativeAllocationLedger arena initial ingestionRequests afterIngestion ∧
      (nativeRetainedLinesRequests stored).Sublist ingestionRequests ∧
      tableRequest = nativeSortTableRequest stored ∧
      smolFreshAllocationOutcome tableRequest arena afterIngestion = .allocated afterTable := by
  cases evidence with
  | reservationRefused => simp [nativePreparationOutcome] at ready
  | ingestionRefused => simp [nativePreparationOutcome] at ready
  | sortTableRefused => simp [nativePreparationOutcome] at ready
  | ready arena reservation initial afterIngestion afterTable initialFrame ingestion ingestionExact stored
      ingestionCompleted ingestionRequests ingestionLedger retainedRequests tableRequest tableRequestExact
      tableAllocated =>
      exact ⟨arena, initial, afterIngestion, afterTable, ingestion, stored, ingestionRequests,
        tableRequest, reservation, initialFrame, ingestionExact, ingestionCompleted, ingestionLedger,
        retainedRequests, tableRequestExact, tableAllocated⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The independent whole-program specification receives only the combined phase-indexed
preparation classification, never reservation admission by itself. -/
def nativeSpike3Spec {context : Spike3NativeExecutionContext}
    {lineCapacity : Nat} {lines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity lines) (environment : Environment)
    (output : Spike3OutputOutcome) : Spike3ByteSortOutcome :=
  spike3ByteSortSpec environment (nativePreparationOutcome evidence) output

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A bridge that has established the combined ready result may use the pure bounded-ingestion
success law for every finite environment input. -/
theorem boundedLineSortOutcome_agrees_native_ready_accepted
    {context : Spike3NativeExecutionContext} {lineCapacity : Nat} {evidenceLines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity evidenceLines) (environment : Environment)
    (capacity : Nat) (lines : List (List UInt8))
    (ready : nativePreparationOutcome evidence = .ready)
    (input : environmentInputLines environment = lines) (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .accepted =
      nativeSpike3Spec evidence environment .accepted := by
  unfold nativeSpike3Spec
  rw [ready]
  exact boundedLineSortOutcome_of_fits_agrees_ready_accepted environment capacity lines input fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Output refusal remains the selected native specification outcome after a combined ready
preparation result; it cannot be folded into any allocation failure. -/
theorem boundedLineSortOutcome_agrees_native_ready_refused
    {context : Spike3NativeExecutionContext} {lineCapacity : Nat} {evidenceLines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity evidenceLines) (environment : Environment)
    (capacity : Nat) (lines : List (List UInt8))
    (ready : nativePreparationOutcome evidence = .ready)
    (fits : lines.length ≤ capacity) :
    boundedLineSortOutcome capacity lines .refused =
      nativeSpike3Spec evidence environment .refused := by
  unfold nativeSpike3Spec
  rw [ready, spike3ByteSortSpec_output_refused]
  exact boundedLineSortOutcome_of_fits_refused capacity lines fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Every combined preparation abort has no success or output-prefix payload, independently of
the caller's finite stdin. -/
theorem nativeSpike3Spec_exhausted
    {context : Spike3NativeExecutionContext} {lineCapacity : Nat} {lines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity lines) (environment : Environment)
    (output : Spike3OutputOutcome)
    (exhausted : nativePreparationOutcome evidence = .exhausted) :
    nativeSpike3Spec evidence environment output = .preparationFailure := by
  unfold nativeSpike3Spec
  rw [exhausted, spike3ByteSortSpec_exhausted]

end Spikes.Spike3SortLines

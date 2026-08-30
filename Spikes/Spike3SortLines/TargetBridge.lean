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

import Spikes.Spike3SortLines.LogicalWorld

/-! The target-to-ghost interface shared by the native and WASI sorter proofs.

Preparation is deliberately the only resource-fallible phase.  A finite
arena/budget cannot justify a successful preparation for every finite byte
string; the concrete target may take its checked abort path before it seals
line storage and its sort table.  Once `ReadyState` exists, sorting is total
and allocation-free; emission can only complete or report a target-specific
output error.  The readiness relation is an explicit target-owned proposition
over the active world; this file neither creates nor accounts for a second
resource ledger.
-/

namespace Spikes.Spike3SortLines.TargetBridge

open Spikes.Spike3SortLines
open Spikes.Spike3SortLines.LogicalWorld

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- One concrete state which has successfully sealed ingestion/preparation.  Construction requires
    exact line storage and table evidence plus a proof of the explicit target-owned readiness
    relation over the active world.  No locally-definable `governor := True` seam remains. -/
structure ReadyState (World Concrete Storage Table LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8))
    (authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks) where
  prepared : EstablishedPreparation World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority

namespace ReadyState

theorem source_exact
    (state : ReadyState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority) :
    state.prepared.certificate.ready.source = state.prepared.certificate.storage.source :=
  state.prepared.certificate.source_exact

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- A prepared state retains the exact LF-completed records of its input. -/
theorem completed_bytes
    (state : ReadyState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority) :
    state.prepared.certificate.ready.source.map lineUniverse.bytes =
      (ByteLineStream.feed {} stdin).completedLines := by
  calc
    state.prepared.certificate.ready.source.map lineUniverse.bytes =
        state.prepared.certificate.storage.source.map lineUniverse.bytes := by rw [state.source_exact]
    _ = (ByteLineStream.feed {} stdin).completedLines := by
      rw [state.prepared.certificate.storage.source_eq_completed]
      exact state.prepared.certificate.storage.reading.completed_bytes

end ReadyState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The target-owned observation relation for one actual host write.  It is deliberately supplied
    by a platform bridge rather than encoded as a local `True` predicate: the bridge must connect
    the cursor/result pair to its concrete write transition.  `OutputConcrete` is separate from
    preparation state because sorting may change a target's concrete state before emission. -/
abbrev OutputWriteObserved (World OutputConcrete OutputError LineId : Type)
    (lineUniverse : LineUniverse LineId) : Type :=
  World → OutputConcrete → OutputConcrete → {order : List LineId} →
    (cursor : OutputCursor LineId lineUniverse order) →
    OutputCursor.WriteResult OutputError cursor → Prop

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A terminal target observation.  Preparation failure has no fabricated storage/table/source
    witness.  Success and output refusal can occur only after `ReadyState` has sealed all
    allocation-dependent state; output refusal retains the exact emitted prefix and a
    target-specific error payload produced by an actual target-owned write observation. -/
inductive Terminal (World Concrete OutputConcrete Storage Table PreparationError OutputError LineId : Type)
    (lineUniverse : LineUniverse LineId) (stdin : List UInt8) (capacity : Nat)
    (chunks : List (List UInt8))
    (authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks)
    (writeObserved : OutputWriteObserved World OutputConcrete OutputError LineId lineUniverse) where
  | preparationFailure (concrete : Concrete) (error : PreparationError) :
      Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
        lineUniverse stdin capacity chunks authority writeObserved
  | completed (ready : ReadyState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority)
      (emission : EmissionState LineId lineUniverse ready.prepared.certificate.ready.source)
      (done : emission.emitting.remaining = [])
      (cursor : OutputCursor LineId lineUniverse emission.sorting.order)
      (outputDone : cursor.remaining = []) :
      Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
        lineUniverse stdin capacity chunks authority writeObserved
  | outputRefused (ready : ReadyState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority)
      (emission : EmissionState LineId lineUniverse ready.prepared.certificate.ready.source)
      (cursor : OutputCursor LineId lineUniverse emission.sorting.order)
      (cursorExtends : OutputCursor.extendsEmission lineUniverse emission cursor)
      (concreteBefore concreteAfter : OutputConcrete)
      (error : OutputError)
      (observed : writeObserved ready.prepared.world concreteBefore concreteAfter cursor (.refused error)) :
      Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
        lineUniverse stdin capacity chunks authority writeObserved

namespace Terminal

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Successful target completion emits a byte-wise sorted permutation of its exact nominal
    source.  This is a logical consequence of the retained emission certificate, not a claim
    about a trace chosen independently of the execution. -/
theorem completed_sorted_permutation {lineUniverse : LineUniverse LineId}
    {authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks}
    {writeObserved : OutputWriteObserved World OutputConcrete OutputError LineId lineUniverse}
    {terminal : Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved}
    (success : ∃ ready emission done cursor outputDone,
      terminal = .completed ready emission done cursor outputDone) :
    ∃ ready emission done cursor outputDone,
      terminal = .completed ready emission done cursor outputDone ∧
      SortingState.Ordered lineUniverse emission.emitting.emitted ∧
      emission.emitting.emitted.Perm ready.prepared.certificate.ready.source := by
  rcases success with ⟨ready, emission, done, cursor, outputDone, rfl⟩
  exact ⟨ready, emission, done, cursor, outputDone, rfl,
    emission.completed_sorted_permutation done⟩

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- The byte records emitted on success are a permutation of the LF-completed records of the
    exact logical input.  The statement is independent of the number, sizes, and boundaries of
    valid reads because preparation retains its `ChunksOf` derivation. -/
theorem completed_input_permutation
    {authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks}
    {writeObserved : OutputWriteObserved World OutputConcrete OutputError LineId lineUniverse}
    {terminal : Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved}
    (success : ∃ ready emission done cursor outputDone,
      terminal = .completed ready emission done cursor outputDone) :
    ∃ ready emission done cursor outputDone,
      terminal = .completed ready emission done cursor outputDone ∧
      (emission.emitting.emitted.map lineUniverse.bytes).Perm
        ((ByteLineStream.feed {} stdin).completedLines) := by
  rcases success with ⟨ready, emission, done, cursor, outputDone, rfl⟩
  refine ⟨ready, emission, done, cursor, outputDone, rfl, ?_⟩
  have emitted := emission.completed_bytes_permutation done
  rw [← ready.completed_bytes]
  exact emitted

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Successful terminal bytes are the unique canonical byte sorting of the exact universal
    input. Distinct nominal IDs with equal byte contents remain duplicates in that sequence. -/
theorem completed_input_exact
    {authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks}
    {writeObserved : OutputWriteObserved World OutputConcrete OutputError LineId lineUniverse}
    {terminal : Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved}
    (success : ∃ ready emission done cursor outputDone,
      terminal = .completed ready emission done cursor outputDone) :
    ∃ ready emission done cursor outputDone,
      terminal = .completed ready emission done cursor outputDone ∧
      emission.emitting.emitted.map lineUniverse.bytes =
        sortByteLines ((ByteLineStream.feed {} stdin).completedLines) := by
  rcases success with ⟨ready, emission, done, cursor, outputDone, rfl⟩
  refine ⟨ready, emission, done, cursor, outputDone, rfl, ?_⟩
  have completed := emission.completed_sorted_permutation done
  have canonical := SortingState.ordered_permutation_eq_sortByteLines lineUniverse
    completed.1 completed.2
  rw [ready.completed_bytes] at canonical
  exact canonical

end Terminal

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- A target-owned terminal certificate.  Native and WASI proof layers instantiate concrete
    states and their platform-specific preparation/output error types, then prove actual
    reachability.  This generic layer contributes no executable trace surrogate and no unchecked
    evaluation shortcut. -/
structure Completion (World Concrete OutputConcrete Storage Table PreparationError OutputError LineId : Type)
    (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8))
    (authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks)
    (writeObserved : OutputWriteObserved World OutputConcrete OutputError LineId lineUniverse) where
  terminal : Terminal World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
    lineUniverse stdin capacity chunks authority writeObserved

namespace Completion

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- The source-level outcome projected from an already target-owned terminal. This does not turn
    a generic terminal into a WASI observation or grant any platform execution authority. -/
def outcome (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
    lineUniverse stdin capacity chunks authority writeObserved) : Spike3ByteSortOutcome :=
  match completion.terminal with
  | .preparationFailure _ _ => .preparationFailure
  | .completed _ emission _ _ _ =>
      .completed (byteSortOutput (emission.emitting.emitted.map lineUniverse.bytes))
  | .outputRefused _ _ _ _ _ _ _ _ => .outputRefused

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Every successful completion has an exact input-record permutation theorem.  This is the
    composition point target proofs use after they establish that their actual execution reached
    `Completion.terminal`; it does not assume a particular stdin, a byte alphabet subset, or a
    chosen read schedule. -/
theorem success_input_permutation
    (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved)
    (success : ∃ ready emission done cursor outputDone,
      completion.terminal = .completed ready emission done cursor outputDone) :
    ∃ ready emission done cursor outputDone,
      completion.terminal = .completed ready emission done cursor outputDone ∧
      (emission.emitting.emitted.map lineUniverse.bytes).Perm
        ((ByteLineStream.feed {} stdin).completedLines) :=
  Terminal.completed_input_permutation success

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
theorem success_input_exact
    (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved)
    (success : ∃ ready emission done cursor outputDone,
      completion.terminal = .completed ready emission done cursor outputDone) :
    ∃ ready emission done cursor outputDone,
      completion.terminal = .completed ready emission done cursor outputDone ∧
      emission.emitting.emitted.map lineUniverse.bytes =
        sortByteLines ((ByteLineStream.feed {} stdin).completedLines) :=
  Terminal.completed_input_exact success

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
theorem success_outcome
    (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved)
    (success : ∃ ready emission done cursor outputDone,
      completion.terminal = .completed ready emission done cursor outputDone) :
    completion.outcome = .completed
      (byteSortOutput (sortByteLines ((ByteLineStream.feed {} stdin).completedLines))) := by
  rcases completion.success_input_exact success with
    ⟨ready, emission, done, cursor, outputDone, terminalEq, bytesEq⟩
  unfold outcome
  rw [terminalEq]
  simp [bytesEq]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
theorem preparation_failure_outcome
    (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved)
    (failure : ∃ concrete error, completion.terminal = .preparationFailure concrete error) :
    completion.outcome = .preparationFailure := by
  rcases failure with ⟨concrete, error, terminalEq⟩
  unfold outcome
  rw [terminalEq]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
theorem output_refusal_outcome
    (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved)
    (refusal : ∃ ready emission cursor cursorExtends before after error observed,
      completion.terminal = .outputRefused ready emission cursor cursorExtends before after error observed) :
    completion.outcome = .outputRefused := by
  rcases refusal with ⟨ready, emission, cursor, cursorExtends, before, after, error, observed, terminalEq⟩
  unfold outcome
  rw [terminalEq]

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
theorem success_outcome_is_spec
    (completion : Completion World Concrete OutputConcrete Storage Table PreparationError OutputError LineId
      lineUniverse stdin capacity chunks authority writeObserved)
    (environment : Gasm.Core.Platform.Environment)
    (stdinExact : environment.stdin.toList = stdin)
    (success : ∃ ready emission done cursor outputDone,
      completion.terminal = .completed ready emission done cursor outputDone) :
    completion.outcome = spike3ByteSortSpec environment .ready .accepted := by
  rw [spike3ByteSortSpec_ready_accepts]
  simpa [environmentInputLines, decodeStdinLines, stdinExact] using completion.success_outcome success

end Completion

end Spikes.Spike3SortLines.TargetBridge

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

import Spikes.Spike3SortLines.Input
import Spikes.Spike3SortLines.Model

/-! Logical, erased proof state for the streaming line sorter.

This is intentionally not a machine state, allocator model, executable artifact,
or a second program-verification authority. The eventual native/WASI bridges
must relate their concrete state to this world. Keeping line contents in the
fixed `LineUniverse` makes pointer/storage changes irrelevant to sorting proofs:
the mutable part of the world contains only nominal identities and their order.
-/

namespace Spikes.Spike3SortLines.LogicalWorld

open Spikes.Spike3SortLines

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- A fixed, ghost-only mapping origin nominal line identities to their immutable bytes.
    `LineId` is deliberately a type parameter: an implementation chooses a fresh nominal
    identity discipline, but it cannot replace line contents during a transition because every
    transition below is indexed by the same lineUniverse. -/
structure LineUniverse (LineId : Type) where
  bytes : LineId → List UInt8

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- The mutable ghost state of the streaming tokenizer. `consumed` is chronological; pending
    bytes use the target-friendly reverse representation; completed records are nominal IDs in
    arrival order. -/
structure ReadingState (LineId : Type) where
  consumed : List UInt8 := []
  pendingRev : List UInt8 := []
  completed : List LineId := []

namespace ReadingState

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Erases nominal line identities to the existing byte-stream decoder representation. -/
def decoder (lineUniverse : LineUniverse LineId) (state : ReadingState LineId) : ByteLineStream :=
  { currentRev := state.pendingRev
    completedRev := (state.completed.map lineUniverse.bytes).reverse }

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- One byte-level tokenizer transition. LF allocates a fresh nominal identity whose immutable
    bytes equal the completed record; other bytes only extend the pending trailing. -/
inductive Step (lineUniverse : LineUniverse LineId) :
    ReadingState LineId → ReadingState LineId → Prop where
  | byte (state : ReadingState LineId) (byte : UInt8) (notLineFeed : byte ≠ lineFeed) :
      Step lineUniverse state
        { consumed := state.consumed ++ [byte]
          pendingRev := byte :: state.pendingRev
          completed := state.completed }
  | complete (state : ReadingState LineId) (line : LineId)
      (fresh : line ∉ state.completed)
      (contents : lineUniverse.bytes line = trimLineEnding state.pendingRev.reverse) :
      Step lineUniverse state
        { consumed := state.consumed ++ [lineFeed]
          pendingRev := []
          completed := state.completed ++ [line] }

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- A non-delimiter transition has the same decoder effect as consuming that byte. -/
theorem byte_projects_decoder (lineUniverse : LineUniverse LineId) (state : ReadingState LineId)
    (byte : UInt8) (notLineFeed : byte ≠ lineFeed) :
    (decoder lineUniverse
      { consumed := state.consumed ++ [byte]
        pendingRev := byte :: state.pendingRev
        completed := state.completed }) =
      (decoder lineUniverse state).step byte := by
  simp [decoder, ByteLineStream.step, notLineFeed]

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Completing a fresh nominal line has the same decoder effect as consuming LF. -/
theorem complete_projects_decoder (lineUniverse : LineUniverse LineId) (state : ReadingState LineId)
    (line : LineId) (_fresh : line ∉ state.completed)
    (contents : lineUniverse.bytes line = trimLineEnding state.pendingRev.reverse) :
    (decoder lineUniverse
      { consumed := state.consumed ++ [lineFeed]
        pendingRev := []
        completed := state.completed ++ [line] }) =
      (decoder lineUniverse state).step lineFeed := by
  simp [decoder, ByteLineStream.step, contents]

end ReadingState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Mutable sorting order, framed by an immutable source order. The `permutation` proof is
    carried once at every sorting boundary rather than reproved by every comparison client. -/
structure SortingState (LineId : Type) (source : List LineId) where
  order : List LineId
  permutation : order.Perm source

namespace SortingState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def initial (source : List LineId) : SortingState LineId source :=
  { order := source, permutation := List.Perm.refl source }

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- The local compare/swap decision used by an in-place sorter. It exchanges only nominal IDs;
    bytes remain in the fixed lineUniverse. -/
def compareSwap (lineUniverse : LineUniverse LineId) (left right : LineId) : List LineId :=
  if byteLineLe (lineUniverse.bytes right) (lineUniverse.bytes left) then [right, left] else [left, right]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
theorem compareSwap_perm (lineUniverse : LineUniverse LineId) (left right : LineId) :
    (compareSwap lineUniverse left right).Perm [left, right] := by
  unfold compareSwap
  split <;> simp [List.Perm.swap]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def compareSwapAt (lineUniverse : LineUniverse LineId) (state : SortingState LineId source)
    (leading trailing : List LineId) (left right : LineId)
    (split : state.order = leading ++ left :: right :: trailing) : SortingState LineId source :=
  { order := leading ++ compareSwap lineUniverse left right ++ trailing
    permutation := by
      simpa only [List.append_assoc] using
        (List.Perm.append_left leading
          (List.Perm.append_right trailing (compareSwap_perm lineUniverse left right))).trans
            (by simpa [split] using state.permutation) }

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The reusable comparison transition. No source bytes, input decoder state, or resource frame
    appears in the rule, which is the intended proof-economy separation. -/
inductive Step (lineUniverse : LineUniverse LineId) (source : List LineId) :
    SortingState LineId source → SortingState LineId source → Prop where
  | compareSwap (state : SortingState LineId source) (leading trailing : List LineId)
      (left right : LineId) (split : state.order = leading ++ left :: right :: trailing) :
      Step lineUniverse source state (state.compareSwapAt lineUniverse leading trailing left right split)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
theorem Step.preserves_permutation {lineUniverse : LineUniverse LineId} {source : List LineId}
    {before after : SortingState LineId source} (_step : Step lineUniverse source before after) :
    after.order.Perm source :=
  after.permutation

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
def Ordered (lineUniverse : LineUniverse LineId) : List LineId → Prop
  | [] | [_] => True
  | left :: right :: rest =>
      byteLineLe (lineUniverse.bytes left) (lineUniverse.bytes right) = true ∧ Ordered lineUniverse (right :: rest)

end SortingState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- The emission phase separates the output leading origin IDs not yet written. Its partition law
    is independent of the physical `WriteFile`/`write` buffering representation. -/
structure EmittingState (LineId : Type) (order : List LineId) where
  emitted : List LineId := []
  remaining : List LineId := order
  partition : emitted ++ remaining = order

namespace EmittingState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
def initial (order : List LineId) : EmittingState LineId order :=
  { partition := rfl }

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
inductive Step (order : List LineId) :
    EmittingState LineId order → EmittingState LineId order → Prop where
  | emit (emitted : List LineId) (line : LineId) (remaining : List LineId)
      (partition : emitted ++ line :: remaining = order) :
      Step order
        { emitted := emitted, remaining := line :: remaining, partition := partition }
        { emitted := emitted ++ [line]
          remaining := remaining
          partition := by simpa [List.append_assoc] using partition }

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
theorem Step.preserves_partition {order : List LineId}
    {before after : EmittingState LineId order} (_step : Step order before after) :
    after.emitted ++ after.remaining = order :=
  after.partition

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Once the emitter has no remaining IDs, its prefix is the selected order exactly. -/
theorem completed_emits_all (state : EmittingState LineId order) (done : state.remaining = []) :
    state.emitted = order := by
  simpa [done] using state.partition

end EmittingState

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- A read-side certificate is framed solely by a finite chunk sequence and the ghost tokenizer.
    It deliberately says nothing about where those bytes were buffered. -/
structure ReadFragmentCertificate (LineId : Type) (lineUniverse : LineUniverse LineId)
    (chunks : List (List UInt8)) where
  state : ReadingState LineId
  consumed_eq : state.consumed = chunks.flatten

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A storage-side certificate is parameterized by the concrete representation rather than
    placing representation fields in the ghost world. -/
structure StorageCertificate (Storage LineId : Type) (completed : List LineId) where
  storage : Storage
  realizes : Storage → List LineId → Prop
  resident : realizes storage completed

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- A terminal sorting certificate layers orderedness over the permutation frame already carried
    by `SortingState`; sorting implementations need prove orderedness only at their selected exit. -/
structure SortedCertificate (LineId : Type) (lineUniverse : LineUniverse LineId)
    (source : List LineId) where
  state : SortingState LineId source
  ordered : SortingState.Ordered lineUniverse state.order

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- An emission certificate exposes an output prefix without choosing a concrete write buffer or
    syscall representation. -/
structure EmissionPrefixCertificate (LineId : Type) (order : List LineId) where
  state : EmittingState LineId order

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The small cross-phase composition law: a completed emission of a sorted order preserves the
    original nominal line multiset. Orderedness and byte serialization remain independent facts. -/
theorem completed_emission_permutation {lineUniverse : LineUniverse LineId}
    {source : List LineId} (sorting : SortedCertificate LineId lineUniverse source)
    (emission : EmissionPrefixCertificate LineId sorting.state.order)
    (done : emission.state.remaining = []) :
    emission.state.emitted.Perm source := by
  rw [emission.state.completed_emits_all done]
  exact sorting.state.permutation

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- Linear cleanup and retry authority carried through every sorter phase. The model is generic
    over obligation tokens so it composes with the shared obligation algebra when that algebra is
    instantiated; it intentionally adds no concrete TLS, allocator, or machine field. -/
structure ResourceFrame (Obligation : Type) where
  cleanup : List Obligation := []
  recovery : List Obligation := []

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
inductive Phase where
  | reading | sorting | emitting | resourceFailed | completed

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
inductive FailedPhase where
  | reading | sorting | emitting

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- Phase-indexed world states. The lineUniverse is an invariant parameter, so implementations can
    change storage pointers or sort-table layout only after proving they still realize these ghost
    IDs and contents. -/
inductive PhaseState (LineId Obligation : Type) (lineUniverse : LineUniverse LineId) :
    Phase → Type where
  | reading (resources : ResourceFrame Obligation) (state : ReadingState LineId) :
      PhaseState LineId Obligation lineUniverse .reading
  | sorting (resources : ResourceFrame Obligation) (source : List LineId)
      (state : SortingState LineId source) :
      PhaseState LineId Obligation lineUniverse .sorting
  | emitting (resources : ResourceFrame Obligation) (order : List LineId)
      (state : EmittingState LineId order) :
      PhaseState LineId Obligation lineUniverse .emitting
  | resourceFailed (resources : ResourceFrame Obligation) (origin : FailedPhase) :
      PhaseState LineId Obligation lineUniverse .resourceFailed
  | completed (resources : ResourceFrame Obligation) (order : List LineId)
      (emitted : EmittingState LineId order) (done : emitted.remaining = []) :
      PhaseState LineId Obligation lineUniverse .completed

namespace PhaseState

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
def resources : PhaseState LineId Obligation lineUniverse phase → ResourceFrame Obligation
  | .reading resources _ => resources
  | .sorting resources _ _ => resources
  | .emitting resources _ _ => resources
  | .resourceFailed resources _ => resources
  | .completed resources _ _ _ => resources

end PhaseState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- Typed phase transitions. Reads, comparison swaps, and emission each retain their own local
    proof obligations; only phase changes connect the layers. Resource failure preserves the
    exact cleanup/recovery frame rather than discarding it on an error path. -/
inductive PhaseTransition (lineUniverse : LineUniverse LineId) :
    {origin to : Phase} → PhaseState LineId Obligation lineUniverse origin →
      PhaseState LineId Obligation lineUniverse to → Prop where
  | read {resources before after}
      (step : ReadingState.Step lineUniverse before after) :
      PhaseTransition lineUniverse (.reading resources before) (.reading resources after)
  | beginSorting {resources state} :
      PhaseTransition lineUniverse (.reading resources state)
        (.sorting resources state.completed (SortingState.initial state.completed))
  | compareSwap {resources source before after}
      (step : SortingState.Step lineUniverse source before after) :
      PhaseTransition lineUniverse (.sorting resources source before) (.sorting resources source after)
  | beginEmitting {resources source state} :
      PhaseTransition lineUniverse (.sorting resources source state)
        (.emitting resources state.order (EmittingState.initial state.order))
  | emit {resources order before after}
      (step : EmittingState.Step order before after) :
      PhaseTransition lineUniverse (.emitting resources order before) (.emitting resources order after)
  | finish {resources order state} (done : state.remaining = []) :
      PhaseTransition lineUniverse (.emitting resources order state) (.completed resources order state done)
  | resourceFailureReading {resources state} :
      PhaseTransition lineUniverse (.reading resources state) (.resourceFailed resources .reading)
  | resourceFailureSorting {resources source state} :
      PhaseTransition lineUniverse (.sorting resources source state) (.resourceFailed resources .sorting)
  | resourceFailureEmitting {resources order state} :
      PhaseTransition lineUniverse (.emitting resources order state) (.resourceFailed resources .emitting)

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- Framing law shared by success and failure paths: this logical layer cannot silently consume,
    fabricate, or forget cleanup/recovery authority. Concrete allocator and cancellation models
    later refine this equality with their own linear transfer laws. -/
theorem PhaseTransition.resources_preserved {lineUniverse : LineUniverse LineId}
    {before : PhaseState LineId Obligation lineUniverse origin}
    {after : PhaseState LineId Obligation lineUniverse to}
    (_step : PhaseTransition lineUniverse before after) :
    after.resources = before.resources := by
  cases _step <;> rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Starting the sorting phase carries exactly the tokenizer's completed nominal IDs as the source
    permutation. This is the sole reading-to-sorting coupling; byte fragmentation and storage
    layout do not reappear in compare/swap proofs. -/
theorem PhaseTransition.beginSorting_source {lineUniverse : LineUniverse LineId}
    {resources : ResourceFrame Obligation} {state : ReadingState LineId} :
    PhaseTransition lineUniverse (.reading resources state)
      (.sorting resources state.completed (SortingState.initial state.completed)) :=
  .beginSorting

end Spikes.Spike3SortLines.LogicalWorld

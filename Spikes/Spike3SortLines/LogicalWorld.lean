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

/-- The only initial tokenizer state.  Read certificates below start here rather than merely
    asserting a convenient `consumed` equality about an unrelated state. -/
def initial : ReadingState LineId := {}

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

/-- Reachability by the production byte tokenizer.  The byte list is part of the derivation, so
    a completed-line certificate cannot be assembled from an independent partition of input. -/
inductive Reaches (lineUniverse : LineUniverse LineId) :
    ReadingState LineId → List UInt8 → ReadingState LineId → Prop where
  | nil (state : ReadingState LineId) : Reaches lineUniverse state [] state
  | byte {start before : ReadingState LineId} {bytes : List UInt8}
      (reach : Reaches lineUniverse start bytes before) (byte : UInt8)
      (notLineFeed : byte ≠ lineFeed) :
      Reaches lineUniverse start (bytes ++ [byte])
        { consumed := before.consumed ++ [byte]
          pendingRev := byte :: before.pendingRev
          completed := before.completed }
  | complete {start before : ReadingState LineId} {bytes : List UInt8}
      (reach : Reaches lineUniverse start bytes before) (line : LineId)
      (fresh : line ∉ before.completed)
      (contents : lineUniverse.bytes line = trimLineEnding before.pendingRev.reverse) :
      Reaches lineUniverse start (bytes ++ [lineFeed])
        { consumed := before.consumed ++ [lineFeed]
          pendingRev := []
          completed := before.completed ++ [line] }

/-- Erasing a reachable nominal tokenizer run is exactly the existing streaming decoder. -/
theorem reaches_projects_decoder {lineUniverse : LineUniverse LineId}
    {start state : ReadingState LineId} {bytes : List UInt8}
    (reach : Reaches lineUniverse start bytes state) :
    decoder lineUniverse state = (decoder lineUniverse start).feed bytes := by
  induction reach with
  | nil => rfl
  | byte reach byte notLineFeed ih =>
    rw [byte_projects_decoder lineUniverse _ byte notLineFeed, ih, ByteLineStream.feed_append]
    rfl
  | complete reach line fresh contents ih =>
    rw [complete_projects_decoder _ _ line fresh contents, ih, ByteLineStream.feed_append]
    rfl

/-- The reachable state's chronological byte log is exactly the tokenizer input. -/
theorem reaches_consumed {lineUniverse : LineUniverse LineId}
    {start state : ReadingState LineId} {bytes : List UInt8}
    (reach : Reaches lineUniverse start bytes state) :
    state.consumed = start.consumed ++ bytes := by
  induction reach with
  | nil => simp
  | byte reach byte _ ih => simp [ih, List.append_assoc]
  | complete reach _ _ _ ih => simp [ih, List.append_assoc]

/-- Fresh allocation at every delimiter gives nominal line identities unique generations. -/
theorem reaches_completed_nodup {lineUniverse : LineUniverse LineId}
    {start state : ReadingState LineId} {bytes : List UInt8}
    (reach : Reaches lineUniverse start bytes state) (initialNodup : start.completed.Nodup) :
    state.completed.Nodup := by
  induction reach with
  | nil => exact initialNodup
  | byte _ _ _ ih => simpa using ih
  | complete _ line fresh _ ih =>
    simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil]
    constructor
    · exact ih
    · constructor
      · exact ⟨by simp, by simp⟩
      · intro id hmem id' hmem' heq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
        subst id'
        have hline : id = line := by simpa using hmem'
        exact fresh (hline ▸ hmem)

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
  if byteLineLe (lineUniverse.bytes left) (lineUniverse.bytes right) then [left, right] else [right, left]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
theorem compareSwap_of_le (lineUniverse : LineUniverse LineId) (left right : LineId)
    (ordered : byteLineLe (lineUniverse.bytes left) (lineUniverse.bytes right) = true) :
    compareSwap lineUniverse left right = [left, right] := by
  simp [compareSwap, ordered]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
theorem compareSwap_of_not_le (lineUniverse : LineUniverse LineId) (left right : LineId)
    (outOfOrder : byteLineLe (lineUniverse.bytes left) (lineUniverse.bytes right) = false) :
    compareSwap lineUniverse left right = [right, left] := by
  simp [compareSwap, outOfOrder]

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

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
private theorem pairwise_head_le {head other : List UInt8} {tail : List (List UInt8)}
    (ordered : List.Pairwise (fun left right : List UInt8 => left ≤ right) (head :: tail))
    (member : other ∈ head :: tail) : head ≤ other := by
  by_cases same : other = head
  · subst same
    exact Std.Refl.refl _
  · exact (List.pairwise_cons.mp ordered).1 other (by simpa [same] using member)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The nominal-order predicate erases to pairwise lexicographic order over immutable bytes. -/
theorem ordered_pairwise_bytes (lineUniverse : LineUniverse LineId)
    (ids : List LineId) (ordered : Ordered lineUniverse ids) :
    List.Pairwise (fun left right : List UInt8 => left ≤ right) (ids.map lineUniverse.bytes) := by
  cases ids with
  | nil => simp
  | cons left ids =>
    cases ids with
    | nil => simp
    | cons right rest =>
      have tailOrdered : Ordered lineUniverse (right :: rest) := ordered.2
      have tailPairwise := ordered_pairwise_bytes lineUniverse (right :: rest) tailOrdered
      apply List.Pairwise.cons
      · intro next nextMember
        calc
          lineUniverse.bytes left ≤ lineUniverse.bytes right :=
            (byteLineLe_eq_true_iff _ _).mp ordered.1
          _ ≤ next := pairwise_head_le tailPairwise nextMember
      · exact tailPairwise

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
private theorem pairwise_le_perm_eq {left right : List (List UInt8)}
    (leftOrdered : List.Pairwise (fun left right : List UInt8 => left ≤ right) left)
    (rightOrdered : List.Pairwise (fun left right : List UInt8 => left ≤ right) right)
    (permutation : left.Perm right) : left = right := by
  induction left generalizing right with
  | nil =>
    simp at permutation
    exact permutation.symm
  | cons left leftTail ih =>
    cases right with
    | nil => simp at permutation
    | cons right rightTail =>
      have rightInLeft : right ∈ left :: leftTail :=
        (List.Perm.mem_iff permutation.symm).mp (by simp)
      have leftInRight : left ∈ right :: rightTail :=
        (List.Perm.mem_iff permutation).mp (by simp)
      have leftLeRight : left ≤ right := pairwise_head_le leftOrdered rightInLeft
      have rightLeLeft : right ≤ left := pairwise_head_le rightOrdered leftInRight
      have heads : left = right := Std.Antisymm.antisymm _ _ leftLeRight rightLeLeft
      subst right
      exact congrArg (List.cons left) (ih (List.pairwise_cons.mp leftOrdered).2
        (List.pairwise_cons.mp rightOrdered).2 (List.Perm.cons_inv permutation))

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- An ordered nominal permutation has one byte-level representation: the canonical insertion
    sort of its source bytes. Nominal IDs may be distinct while their bytes are equal; the proof
    uses multiset permutation and therefore preserves those duplicates exactly. -/
theorem ordered_permutation_eq_sortByteLines (lineUniverse : LineUniverse LineId)
    {order source : List LineId}
    (ordered : Ordered lineUniverse order)
    (permutation : order.Perm source) :
    order.map lineUniverse.bytes = sortByteLines (source.map lineUniverse.bytes) := by
  apply pairwise_le_perm_eq
  · exact ordered_pairwise_bytes lineUniverse order ordered
  · exact sortByteLines_pairwise_le _
  · exact (permutation.map lineUniverse.bytes).trans (sortByteLines_perm _).symm

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
/-- A read-side certificate ranges over the exact input and a real bounded-read schedule.  Its
    state is reachable by `ReadingState.Reaches`, which is the same byte-at-a-time tokenizer that
    `ByteLineStream.feed` uses; it is therefore not an arbitrary partition with a matching total. -/
structure ReadFragmentCertificate (LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8)) where
  chunksOf : Gasm.Effects.ChunksOf stdin capacity chunks
  state : ReadingState LineId
  reaches : ReadingState.Reaches lineUniverse ReadingState.initial chunks.flatten state

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- A certificate's ghost decoder is exactly the production decoder fed by the logical stdin. -/
theorem ReadFragmentCertificate.projects_stream
    (certificate : ReadFragmentCertificate LineId lineUniverse stdin capacity chunks) :
    ReadingState.decoder lineUniverse certificate.state =
      (ReadingState.decoder lineUniverse ReadingState.initial).feed stdin := by
  rw [ReadingState.reaches_projects_decoder certificate.reaches,
    certificate.chunksOf.flatten_eq_total]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Two legal chunk schedules for one finite input yield the same decoder observation. -/
theorem ReadFragmentCertificate.chunk_boundary_independent
    (left : ReadFragmentCertificate LineId lineUniverse stdin capacity leftChunks)
    (right : ReadFragmentCertificate LineId lineUniverse stdin capacity rightChunks) :
    ReadingState.decoder lineUniverse left.state = ReadingState.decoder lineUniverse right.state := by
  rw [left.projects_stream, right.projects_stream]

/-- The tokenizer-produced nominal IDs erase to precisely the completed records of the exact
    logical stdin, not just to a list with the same length or an arbitrary partition. -/
theorem ReadFragmentCertificate.completed_bytes
    (certificate : ReadFragmentCertificate LineId lineUniverse stdin capacity chunks) :
    certificate.state.completed.map lineUniverse.bytes =
      ((ByteLineStream.feed {} stdin).completedLines) := by
  have projection := congrArg ByteLineStream.completedLines certificate.projects_stream
  simpa [ReadingState.decoder, ReadingState.initial, ByteLineStream.completedLines] using projection

theorem ReadFragmentCertificate.completed_nodup
    (certificate : ReadFragmentCertificate LineId lineUniverse stdin capacity chunks) :
    certificate.state.completed.Nodup := by
  simpa [ReadingState.initial] using
    ReadingState.reaches_completed_nodup certificate.reaches (by simp [ReadingState.initial])

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A concrete storage witness for the *exact* EOF-finalized input-derived line universe.
`locate` is supplied by a target bridge (for example descriptor-table lookup), while this layer
checks that every resident entry has its generation and immutable bytes, and that the storage
exposes no stale entry outside the tokenizer-produced source.  The byte equality deliberately
includes a nonempty unterminated EOF record: that record is retained unchanged, whereas only a
CR immediately preceding LF is trimmed by the decoder. -/
structure StorageCertificate (Storage LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8)) where
  reading : ReadFragmentCertificate LineId lineUniverse stdin capacity chunks
  storage : Storage
  locate : Storage → LineId → Option (Nat × List UInt8)
  generation : LineId → Nat
  source : List LineId
  source_bytes_eq_finalized : source.map lineUniverse.bytes =
    (ByteLineStream.feed {} stdin).finalizedLines
  generation_exact : ∀ id, id ∈ source → source[(generation id)]? = some id
  resident_exact : ∀ id, id ∈ source →
    locate storage id = some (generation id, lineUniverse.bytes id)
  no_stale_entry : ∀ id n bytes,
    locate storage id = some (n, bytes) →
      id ∈ source ∧ n = generation id ∧ bytes = lineUniverse.bytes id

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The sealed logical hand-off from ingestion/preparation to sorting.  `tableOrder` is the
    initially materialized sort table, before the sorter mutates it.  It is deliberately kept
    separate from the physical table representation: a target bridge must show that its table
    realizes this exact order, alongside storage and governor/obligation facts.

    This is the phase boundary for finite resources.  Reaching this value means all allocations
    needed by the sorter (including the post-EOF table) have already succeeded. -/
structure ReadyToSort (LineId : Type) where
  source : List LineId
  tableOrder : List LineId
  table_exact : tableOrder = source

namespace ReadyToSort

/-- The sealed table starts the allocation-free sorting phase with exactly the tokenizer source.
    Later compare/swap steps change only the `SortingState` order. -/
def initialSorting (ready : ReadyToSort LineId) : SortingState LineId ready.source :=
  { order := ready.tableOrder
    permutation := by simp [ready.table_exact] }

end ReadyToSort

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A target-facing preparation certificate ties physical line storage and a physical sort table
    to the one sealed logical hand-off.  Allocation/accounting obligations are intentionally not
    recreated here; `TargetBridge.ReadyState` carries the active governor seam beside this
    certificate. -/
structure ReadyToSortCertificate (Storage Table LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8)) where
  storage : StorageCertificate Storage LineId lineUniverse stdin capacity chunks
  table : Table
  tableOrder : Table → List LineId
  ready : ReadyToSort LineId
  source_exact : ready.source = storage.source
  table_exact : tableOrder table = ready.tableOrder

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The target-owned proposition which connects the repository's one active obligation/capability
    world to a successfully prepared sorter.  This is deliberately an *input* to the bridge,
    rather than a locally-defined governor predicate: the eventual link gate must establish it
    from the canonical world, concrete allocation calls, and their resource outcomes.

    The current repository does not yet contain the sound-v2 obligation world needed to define a
    canonical instance.  Keeping this parameter explicit prevents this staging layer from
    manufacturing one with `True`. -/
abbrev PreparationAuthority (World Concrete Storage Table LineId : Type)
    (lineUniverse : LineUniverse LineId) (stdin : List UInt8) (capacity : Nat)
    (chunks : List (List UInt8)) : Type :=
  World → Concrete → ReadyToSortCertificate Storage Table LineId lineUniverse stdin capacity chunks → Prop

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- The only way this logical layer records a sealed preparation.  It retains both the exact
    physical storage/table certificate and a proof from a caller-supplied authority relation over
    the sole target world. -/
structure EstablishedPreparation (World Concrete Storage Table LineId : Type)
    (lineUniverse : LineUniverse LineId) (stdin : List UInt8) (capacity : Nat)
    (chunks : List (List UInt8))
    (authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks) where
  world : World
  concrete : Concrete
  certificate : ReadyToSortCertificate Storage Table LineId lineUniverse stdin capacity chunks
  established : authority world concrete certificate

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- A terminal sorting certificate layers orderedness over the permutation frame already carried
    by `SortingState`; sorting implementations need prove orderedness only at their selected exit. -/
structure SortedCertificate (LineId : Type) (lineUniverse : LineUniverse LineId)
    (source : List LineId) where
  state : SortingState LineId source
  ordered : SortingState.Ordered lineUniverse state.order

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Emission keeps the sorted terminal fact and its exact source permutation in scope for every
    write transition.  A write-buffer proof need only refine `emitting`; it cannot forget why the
    selected order is sorted or which input-line multiset it came from. -/
structure EmissionState (LineId : Type) (lineUniverse : LineUniverse LineId)
    (source : List LineId) where
  sorting : SortingState LineId source
  ordered : SortingState.Ordered lineUniverse sorting.order
  emitting : EmittingState LineId sorting.order

namespace EmissionState

def initial (sorting : SortedCertificate LineId lineUniverse source) :
    EmissionState LineId lineUniverse source :=
  { sorting := sorting.state
    ordered := sorting.ordered
    emitting := EmittingState.initial sorting.state.order }

/-- A single logical write advances only the prefix.  Sortedness and exact source permutation
    are retained definitionally from the state before the write. -/
inductive Step (lineUniverse : LineUniverse LineId) (source : List LineId) :
    EmissionState LineId lineUniverse source → EmissionState LineId lineUniverse source → Prop where
  | emit (before : EmissionState LineId lineUniverse source)
      (after : EmittingState LineId before.sorting.order)
      (step : EmittingState.Step before.sorting.order before.emitting after) :
      Step lineUniverse source before
        { sorting := before.sorting, ordered := before.ordered, emitting := after }

theorem Step.preserves_ordered {lineUniverse : LineUniverse LineId} {source : List LineId}
    {before after : EmissionState LineId lineUniverse source}
    (_step : Step lineUniverse source before after) :
    SortingState.Ordered lineUniverse after.sorting.order := after.ordered

theorem Step.preserves_source_permutation {lineUniverse : LineUniverse LineId} {source : List LineId}
    {before after : EmissionState LineId lineUniverse source}
    (_step : Step lineUniverse source before after) : after.sorting.order.Perm source :=
  after.sorting.permutation

/-- At completion the emitted IDs are exactly the sorted order, hence are sorted and preserve the
    nominal input multiset. -/
theorem completed_sorted_permutation (state : EmissionState LineId lineUniverse source)
    (done : state.emitting.remaining = []) :
    SortingState.Ordered lineUniverse state.emitting.emitted ∧ state.emitting.emitted.Perm source := by
  rw [state.emitting.completed_emits_all done]
  exact ⟨state.ordered, state.sorting.permutation⟩

/-- The same conclusion after erasing nominal identities to their immutable byte records. -/
theorem completed_bytes_permutation (state : EmissionState LineId lineUniverse source)
    (done : state.emitting.remaining = []) :
    (state.emitting.emitted.map lineUniverse.bytes).Perm (source.map lineUniverse.bytes) :=
  (state.completed_sorted_permutation done).2.map lineUniverse.bytes

end EmissionState

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The exact byte representation of one emitted line.  The logical output protocol is bytes even
    when a concrete host adapter later renders them as a string event. -/
def renderedLineBytes (lineUniverse : LineUniverse LineId) (line : LineId) : List UInt8 :=
  lineUniverse.bytes line ++ [13, 10]

/-- The byte stream selected by a sorted line order. -/
def renderedOrderBytes (lineUniverse : LineUniverse LineId) (order : List LineId) : List UInt8 :=
  order.flatMap (renderedLineBytes lineUniverse)

/-- Constructive list-prefix relation, kept local because the output bridge needs the exact
    residual bytes after a short write. -/
def BytePrefix (leading whole : List UInt8) : Prop := ∃ suffix, whole = leading ++ suffix

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A byte-level output cursor.  Unlike the older line-at-a-time emission state, this records the
    exact split at which a host write can refuse, including inside a line or its CRLF suffix. -/
structure OutputCursor (LineId : Type) (lineUniverse : LineUniverse LineId) (order : List LineId) where
  emitted : List UInt8 := []
  remaining : List UInt8 := renderedOrderBytes lineUniverse order
  partition : emitted ++ remaining = renderedOrderBytes lineUniverse order

namespace OutputCursor

def initial (lineUniverse : LineUniverse LineId) (order : List LineId) :
    OutputCursor LineId lineUniverse order :=
  { partition := rfl }

/-- A target-reported host write result.  A successful write may consume any nonempty prefix,
    which models short writes without silently rounding them to line boundaries. -/
inductive WriteResult (OutputError : Type) (before : OutputCursor LineId lineUniverse order) where
  | accepted (after : OutputCursor LineId lineUniverse order) (written : List UInt8)
      (nonempty : written ≠ [])
      (remaining_exact : before.remaining = written ++ after.remaining)
      (emitted_exact : after.emitted = before.emitted ++ written) :
      WriteResult OutputError before
  | refused (error : OutputError) : WriteResult OutputError before

/-- The bytes already emitted by the line-level state must be an exact prefix of an output cursor
    attached to that same sorted order.  The remainder may be a partial current line/CRLF. -/
def extendsEmission (lineUniverse : LineUniverse LineId)
    (emission : EmissionState LineId lineUniverse source)
    (cursor : OutputCursor LineId lineUniverse emission.sorting.order) : Prop :=
  BytePrefix (renderedOrderBytes lineUniverse emission.emitting.emitted) cursor.emitted

end OutputCursor

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- The small cross-phase composition law: a completed emission of a sorted order preserves the
    original nominal line multiset. Orderedness and byte serialization remain independent facts. -/
theorem completed_emission_permutation {lineUniverse : LineUniverse LineId}
    {source : List LineId} (emission : EmissionState LineId lineUniverse source)
    (done : emission.emitting.remaining = []) :
    emission.emitting.emitted.Perm source :=
  (emission.completed_sorted_permutation done).2

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
inductive Phase where
  | reading | readyToSort | sorting | emitting | resourceFailed | completed

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- Phase-indexed states.  The ready state carries the exact physical preparation certificate and
    an establishment proof over the caller's one target world.  The canonical sound-v2 obligation
    algebra is not integrated yet, so its relation is an explicit parameter rather than a local
    governor model. -/
inductive PhaseState (World Concrete Storage Table LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8))
    (authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks) :
    Phase → Type where
  | reading (state : ReadingState LineId) :
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority .reading
  | readyToSort
      (prepared : EstablishedPreparation World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority) :
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority .readyToSort
  | sorting (source : List LineId)
      (state : SortingState LineId source) :
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority .sorting
  | emitting (source : List LineId) (state : EmissionState LineId lineUniverse source) :
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority .emitting
  /-- Resource failure can occur only before `ReadyToSort` is sealed. -/
  | resourceFailed :
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority .resourceFailed
  | completed (source : List LineId) (emitted : EmissionState LineId lineUniverse source)
      (done : emitted.emitting.remaining = []) :
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority .completed

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- Typed line-content transitions.  Ingestion/preparation is the only resource-fallible phase:
    it reads the input and seals `ReadyToSort` only after the sort table is available.  Sorting
    and emission therefore have no resource-failure constructor.  Output refusal is modeled only
    by the target terminal bridge, where it must carry an exact byte cursor and write result.
    Authority accounting remains in the active obligation layer. -/
inductive PhaseTransition (lineUniverse : LineUniverse LineId)
    (authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks) :
    {origin to : Phase} →
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority origin →
      PhaseState World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority to → Prop where
  | read {before after}
      (step : ReadingState.Step lineUniverse before after) :
      PhaseTransition lineUniverse authority (.reading before) (.reading after)
  | prepared {state prepared}
      (reading_exact : prepared.certificate.storage.reading.state = state) :
      PhaseTransition lineUniverse authority (.reading state)
        (.readyToSort prepared)
  | beginSorting {prepared} :
      PhaseTransition lineUniverse authority (.readyToSort prepared)
        (.sorting prepared.certificate.ready.source prepared.certificate.ready.initialSorting)
  | compareSwap {source before after}
      (step : SortingState.Step lineUniverse source before after) :
      PhaseTransition lineUniverse authority (.sorting source before) (.sorting source after)
  | beginEmitting {source state}
      (ordered : SortingState.Ordered lineUniverse state.order) :
      PhaseTransition lineUniverse authority (.sorting source state)
        (.emitting source
          { sorting := state, ordered := ordered, emitting := EmittingState.initial state.order })
  | emit {source before after}
      (step : EmissionState.Step lineUniverse source before after) :
      PhaseTransition lineUniverse authority (.emitting source before) (.emitting source after)
  | finish {source state} (done : state.emitting.remaining = []) :
      PhaseTransition lineUniverse authority (.emitting source state) (.completed source state done)
  | resourceFailurePreparation {state} :
      PhaseTransition lineUniverse authority (.reading state) .resourceFailed

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Preparation is the sole reading-to-sorting coupling.  It requires an exact input/storage/table
    certificate whose reader state is the current phase state, plus an establishment proof over
    the caller's target world. -/
theorem PhaseTransition.prepared_source
    {lineUniverse : LineUniverse LineId}
    {authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks}
    {state : ReadingState LineId}
    {prepared : EstablishedPreparation World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority}
    (reading_exact : prepared.certificate.storage.reading.state = state) :
    PhaseTransition lineUniverse authority (.reading state) (.readyToSort prepared) :=
  .prepared reading_exact

/-- Once `ReadyToSort` exists, beginning sort needs no allocator premise: all finite resource
    acquisition was discharged by preparation. -/
theorem PhaseTransition.ready_begins_sorting {lineUniverse : LineUniverse LineId}
    {authority : PreparationAuthority World Concrete Storage Table LineId lineUniverse stdin capacity chunks}
    (prepared : EstablishedPreparation World Concrete Storage Table LineId lineUniverse stdin capacity chunks authority) :
    PhaseTransition lineUniverse authority (.readyToSort prepared)
      (.sorting prepared.certificate.ready.source prepared.certificate.ready.initialSorting) :=
  .beginSorting

end Spikes.Spike3SortLines.LogicalWorld

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

This is deliberately a *success-or-resource-failure* interface.  A finite
arena/budget cannot justify a successful sort for every finite byte string;
the concrete target may take its checked failure path instead.  Consequently
only the success constructor contains a `SortedCertificate`.  The governor is
the existing sole-obligation seam, carried alongside the real concrete state;
this file neither creates nor accounts for a second resource ledger.
-/

namespace Spikes.Spike3SortLines.TargetBridge

open Spikes.Spike3SortLines
open Spikes.Spike3SortLines.LogicalWorld

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- A terminal target observation.  Completion retains the exact source-derived sorted emission;
    a checked resource failure intentionally has no fabricated sorted-output witness. -/
inductive Terminal (LineId : Type) (lineUniverse : LineUniverse LineId)
    (source : List LineId) where
  | completed (emission : EmissionState LineId lineUniverse source)
      (done : emission.emitting.remaining = []) : Terminal LineId lineUniverse source
  | resourceFailure (origin : FailedPhase) : Terminal LineId lineUniverse source

namespace Terminal

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#5-mathematical-sortedness-permutation-theorems -/
/-- Successful target completion emits a byte-wise sorted permutation of its exact nominal
    source.  This is a logical consequence of the retained emission certificate, not a claim
    about a trace chosen independently of the execution. -/
theorem completed_sorted_permutation {lineUniverse : LineUniverse LineId} {source : List LineId}
    {terminal : Terminal LineId lineUniverse source}
    (success : ∃ emission done, terminal = .completed emission done) :
    ∃ emission done, terminal = .completed emission done ∧
      SortingState.Ordered lineUniverse emission.emitting.emitted ∧
      emission.emitting.emitted.Perm source := by
  rcases success with ⟨emission, done, rfl⟩
  exact ⟨emission, done, rfl, emission.completed_sorted_permutation done⟩

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- The byte records emitted on success are a permutation of the LF-completed records of the
    exact logical input.  The statement is independent of the number, sizes, and boundaries of
    valid reads because `StorageCertificate.reading` retains its `ChunksOf` derivation. -/
theorem completed_input_permutation
    (storage : StorageCertificate Storage LineId lineUniverse stdin capacity chunks)
    {terminal : Terminal LineId lineUniverse storage.source}
    (success : ∃ emission done, terminal = .completed emission done) :
    ∃ emission done, terminal = .completed emission done ∧
      (emission.emitting.emitted.map lineUniverse.bytes).Perm
        ((ByteLineStream.feed {} stdin).completedLines) := by
  rcases success with ⟨emission, done, rfl⟩
  refine ⟨emission, done, rfl, ?_⟩
  have emitted := emission.completed_bytes_permutation done
  have sourceBytes : storage.source.map lineUniverse.bytes =
      (ByteLineStream.feed {} stdin).completedLines := by
    rw [storage.source_eq_completed]
    exact storage.reading.completed_bytes
  rw [← sourceBytes]
  exact emitted

end Terminal

/- REF: docs/ABI_CONTEXT.md#7-finite-allocation-and-request-accounting -/
/-- One concrete target state related to the source it currently owns.  The relation is supplied
    by the active obligation/governor proof, so target bridges cannot introduce a parallel token
    model merely to state their content invariant. -/
structure State (Concrete Storage LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8)) where
  storage : StorageCertificate Storage LineId lineUniverse stdin capacity chunks
  concrete : Concrete
  governor : ResourceGovernorSeam Concrete LineId
  governed : governor.relates concrete storage.source

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#6-end-to-end-simulation-verification-invariant -/
/-- A target-owned terminal certificate may be attached only to the source carried by its concrete
    state.  Native and WASI proof layers instantiate `Concrete` with their actual machine/runtime
    state and prove their own reachability relation; this generic layer contributes no executable
    trace surrogate and no unchecked evaluation shortcut. -/
structure Completion (Concrete Storage LineId : Type) (lineUniverse : LineUniverse LineId)
    (stdin : List UInt8) (capacity : Nat) (chunks : List (List UInt8)) where
  state : State Concrete Storage LineId lineUniverse stdin capacity chunks
  terminal : Terminal LineId lineUniverse state.storage.source

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Every successful completion has an exact input-record permutation theorem.  This is the
    composition point target proofs use after they establish that their actual execution reached
    `Completion.terminal`; it does not assume a particular stdin, a byte alphabet subset, or a
    chosen read schedule. -/
theorem Completion.success_input_permutation
    (completion : Completion Concrete Storage LineId lineUniverse stdin capacity chunks)
    (success : ∃ emission done, completion.terminal = .completed emission done) :
    ∃ emission done, completion.terminal = .completed emission done ∧
      (emission.emitting.emitted.map lineUniverse.bytes).Perm
        ((ByteLineStream.feed {} stdin).completedLines) :=
  Terminal.completed_input_permutation completion.state.storage success

end Spikes.Spike3SortLines.TargetBridge

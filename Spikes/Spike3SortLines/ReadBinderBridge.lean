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

/-!
The small read-binder bridge for native target proofs.

It turns a target's arbitrary finite `ChunksOf` schedule into the exact
universal `Environment.stdin` line observation before invoking the classified
ingestion/sort composition.  It intentionally has no RIP, placement, or
native evaluator dependency.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Sorter observation after an arbitrary finite read-binder schedule.  The schedule is a
proof-relevant argument rather than a sample input selector. -/
def boundedChunkedLineSortOutcome (storageCapacity : Nat) (chunks : List (List UInt8))
    (output : Spike3OutputOutcome) : Spike3ByteSortOutcome :=
  boundedLineSortOutcome storageCapacity (({} : ByteLineStream).feedChunks chunks).completedLines output

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Every valid finite sequence of bounded reads decodes to precisely the canonical environment
input lines.  In particular this does not choose a read count, chunk partition, or stdin value. -/
theorem chunkedLines_eq_environmentInputLines (environment : Environment)
    {readCapacity : Nat} {chunks : List (List UInt8)}
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks) :
    (({} : ByteLineStream).feedChunks chunks).completedLines = environmentInputLines environment := by
  simpa [environmentInputLines, decodeStdinLines] using
    ByteLineStream.completedLines_of_chunksOf ({} : ByteLineStream) reads

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Read fragmentation is observationally irrelevant to the classified pure sorter. -/
theorem boundedChunkedLineSortOutcome_eq_environment (environment : Environment)
    (storageCapacity : Nat) {readCapacity : Nat} {chunks : List (List UInt8)}
    (output : Spike3OutputOutcome)
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks) :
    boundedChunkedLineSortOutcome storageCapacity chunks output =
      boundedLineSortOutcome storageCapacity (environmentInputLines environment) output := by
  unfold boundedChunkedLineSortOutcome
  rw [chunkedLines_eq_environmentInputLines environment reads]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- With a target-owned ready preparation proof, every finite valid read schedule and fitting
decoded input reaches exactly the independent complete-output specification arm. -/
theorem boundedChunkedLineSortOutcome_agrees_ready_accepted (environment : Environment)
    (storageCapacity : Nat) {readCapacity : Nat} {chunks : List (List UInt8)}
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
    (fits : (environmentInputLines environment).length ≤ storageCapacity) :
    boundedChunkedLineSortOutcome storageCapacity chunks .accepted =
      spike3ByteSortSpec environment .ready .accepted := by
  rw [boundedChunkedLineSortOutcome_eq_environment environment storageCapacity .accepted reads]
  exact boundedLineSortOutcome_of_fits_agrees_ready_accepted environment storageCapacity
    (environmentInputLines environment) rfl fits

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A selected write refusal remains separate after the same arbitrary finite read schedule;
it is neither a preparation failure nor a fabricated complete trace. -/
theorem boundedChunkedLineSortOutcome_agrees_ready_refused (environment : Environment)
    (storageCapacity : Nat) {readCapacity : Nat} {chunks : List (List UInt8)}
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
    (fits : (environmentInputLines environment).length ≤ storageCapacity) :
    boundedChunkedLineSortOutcome storageCapacity chunks .refused =
      spike3ByteSortSpec environment .ready .refused := by
  rw [boundedChunkedLineSortOutcome_eq_environment environment storageCapacity .refused reads,
    boundedLineSortOutcome_of_fits_refused storageCapacity (environmentInputLines environment) fits,
    spike3ByteSortSpec_output_refused]

end Spikes.Spike3SortLines

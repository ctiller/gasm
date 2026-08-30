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

import Gasm.Core.Platform
import Gasm.Effects.ReadBinder

/-! Byte-stream input semantics for Spike 3.

The machine targets read stdin in bounded chunks, while the original model
started from an already-tokenized `List String`.  This file is the common,
executable boundary between those representations.  It deliberately accepts
every byte sequence: a line becomes observable only after LF, and CR
immediately before LF is discarded, exactly as the lowerings do.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
def lineFeed : UInt8 := 10

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
def carriageReturn : UInt8 := 13

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#3-in-memory-line-tokenization-lexicographical-ordering -/
/-- Removes the CR which the target lowerings trim immediately before an LF delimiter. -/
def trimLineEnding (line : List UInt8) : List UInt8 :=
  match line.reverse with
  | b :: rest => if b == carriageReturn then rest.reverse else line
  | [] => []

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- State of a streaming stdin decoder. `currentRev` is the bytes since the most recent LF;
    `completedRev` is the completed-line sequence in reverse arrival order. -/
structure ByteLineStream where
  currentRev : List UInt8 := []
  completedRev : List (List UInt8) := []
deriving Repr, DecidableEq

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Incorporates one byte from stdin. Unterminated final bytes remain pending until the explicit
    EOF observation below, where a nonempty tail becomes Spike 3's final retained line. -/
def ByteLineStream.step (state : ByteLineStream) (byte : UInt8) : ByteLineStream :=
  if byte == lineFeed then
    { currentRev := []
      completedRev := trimLineEnding state.currentRev.reverse :: state.completedRev }
  else
    { state with currentRev := byte :: state.currentRev }

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Feeds an arbitrary finite chunk into the decoder. This is structural on the chunk, so unlike
    the former sample-environment model it is executable for every finite byte input. -/
def ByteLineStream.feed (state : ByteLineStream) : List UInt8 → ByteLineStream
  | [] => state
  | byte :: bytes => (state.step byte).feed bytes

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Completed input lines in arrival order. -/
def ByteLineStream.completedLines (state : ByteLineStream) : List (List UInt8) :=
  state.completedRev.reverse

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Final line observation at EOF.  A nonempty trailing byte run is retained by the native
lowerings; a trailing empty state after LF contributes no extra line. -/
def ByteLineStream.finalizedLines (state : ByteLineStream) : List (List UInt8) :=
  match state.currentRev with
  | [] => state.completedLines
  | _ => state.completedLines ++ [trimLineEnding state.currentRev.reverse]

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- The byte-level stdin model used by Spike 3's universal-environment specification. -/
def decodeStdinLines (stdin : ByteArray) : List (List UInt8) :=
  (ByteLineStream.feed {} stdin.toList).finalizedLines

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Streaming composition: splitting an arbitrary stdin stream into host read chunks cannot
    change the decoded lines. This is the fundamental lemma needed to relate the 512-byte target
    reads to the universal `Environment.stdin` oracle. -/
theorem ByteLineStream.feed_append (state : ByteLineStream) (first second : List UInt8) :
    (state.feed (first ++ second)) = ((state.feed first).feed second) := by
  induction first generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [List.cons_append, ByteLineStream.feed]
    exact ih (state.step byte)

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Feeds a finite sequence of host reads.  The sequence is deliberately a list of byte lists,
    rather than a sample selector: each member can be any finite read result, including an empty
    short read. -/
def ByteLineStream.feedChunks (state : ByteLineStream) : List (List UInt8) → ByteLineStream
  | [] => state
  | chunk :: chunks => (state.feed chunk).feedChunks chunks

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Exact finite-read composition.  A decoder fed by any finite sequence of successful reads has
    exactly the same state as one fed the concatenated stdin stream.  This is the reusable
    boundary lemma for 512-byte native/WASI reads; it neither assumes a fixed chunking nor loses
    a final unterminated record. -/
theorem ByteLineStream.feedChunks_flatten (state : ByteLineStream)
    (chunks : List (List UInt8)) :
    state.feedChunks chunks = state.feed chunks.flatten := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk chunks ih =>
    simp only [ByteLineStream.feedChunks, List.flatten_cons]
    rw [ih, ← ByteLineStream.feed_append]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- The observable line sequence is invariant under arbitrary finite read fragmentation. -/
theorem ByteLineStream.completedLines_feedChunks_flatten (state : ByteLineStream)
    (chunks : List (List UInt8)) :
    ((state.feedChunks chunks).completedLines) =
      ((state.feed chunks.flatten).completedLines) := by
  rw [ByteLineStream.feedChunks_flatten]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- EOF finalization is equally invariant under arbitrary finite read fragmentation. -/
theorem ByteLineStream.finalizedLines_feedChunks_flatten (state : ByteLineStream)
    (chunks : List (List UInt8)) :
    ((state.feedChunks chunks).finalizedLines) =
      ((state.feed chunks.flatten).finalizedLines) := by
  rw [ByteLineStream.feedChunks_flatten]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- A bounded read-binder schedule feeds exactly its source stream to the decoder.  This connects
    the concrete `ChunksOf` continuation contract to the sorter without choosing a sample stdin,
    a read count, or a particular placement of chunk boundaries. -/
theorem ByteLineStream.feedChunks_of_chunksOf (state : ByteLineStream)
    {stdin : List UInt8} {capacity : Nat} {chunks : List (List UInt8)}
    (hchunks : Gasm.Effects.ChunksOf stdin capacity chunks) :
    state.feedChunks chunks = state.feed stdin := by
  rw [ByteLineStream.feedChunks_flatten, hchunks.flatten_eq_total]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Consequently, a bounded read schedule cannot alter the completed-line observation of any
    finite stdin stream. -/
theorem ByteLineStream.completedLines_of_chunksOf (state : ByteLineStream)
    {stdin : List UInt8} {capacity : Nat} {chunks : List (List UInt8)}
    (hchunks : Gasm.Effects.ChunksOf stdin capacity chunks) :
    (state.feedChunks chunks).completedLines = (state.feed stdin).completedLines := by
  rw [ByteLineStream.feedChunks_of_chunksOf state hchunks]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Consequently, every valid bounded read schedule has the exact same EOF-finalized line
observation as its source stream, including a final unterminated record when present. -/
theorem ByteLineStream.finalizedLines_of_chunksOf (state : ByteLineStream)
    {stdin : List UInt8} {capacity : Nat} {chunks : List (List UInt8)}
    (hchunks : Gasm.Effects.ChunksOf stdin capacity chunks) :
    (state.feedChunks chunks).finalizedLines = (state.feed stdin).finalizedLines := by
  rw [ByteLineStream.feedChunks_of_chunksOf state hchunks]

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- The canonical environment's byte oracle is the only Spike 3 input source. -/
def environmentInputLines (environment : Environment) : List (List UInt8) :=
  decodeStdinLines environment.stdin

end Spikes.Spike3SortLines

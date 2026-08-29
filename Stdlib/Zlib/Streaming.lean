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

import Stdlib.Zlib.ContainerRoundtrip

namespace Stdlib.Zlib

/-!
Proof-carrying streaming GZIP/GUNZIP capabilities.

Compression and decompression are both stateful streaming primitives. A
whole-buffer operation below is only a convenience fold which feeds one chunk
to the corresponding streaming operation and joins its emitted chunks. The
contract never derives streaming correctness from a whole-buffer function.

Every operation receives and returns its caller-owned allocation scope. A
failed charge is an explicit, recoverable result; it cannot be confused with a
successful empty or truncated stream.
-/

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def joinChunks : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | chunk :: rest => chunk ++ joinChunks rest

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
structure AllocationScope where
  capacity : Nat
  live : Nat := 0
  peak : Nat := 0
  total : Nat := 0
deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
inductive AllocationAttempt where
  | granted (scope : AllocationScope)
  | exhausted (scope : AllocationScope)
deriving Repr

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
def AllocationScope.charge (scope : AllocationScope) (bytes : Nat) : AllocationAttempt :=
  if scope.live + bytes ≤ scope.capacity then
    .granted
      { capacity := scope.capacity
        live := scope.live + bytes
        peak := max scope.peak (scope.live + bytes)
        total := scope.total + bytes }
  else
    .exhausted scope

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
def AllocationScope.release (scope : AllocationScope) (bytes : Nat) : AllocationScope :=
  { scope with live := scope.live - bytes }

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- One streaming transition. The error type is `Empty` for compression and
    `String` for decompression, making compressor rejection unrepresentable. -/
inductive StreamingResult (ε α : Type) where
  | success (value : α) (scope : AllocationScope)
  | rejected (error : ε) (scope : AllocationScope)
  | resourceExhausted (scope : AllocationScope)
deriving Repr

namespace StreamingResult

def map (f : α → β) : StreamingResult ε α → StreamingResult ε β
  | .success value scope => .success (f value) scope
  | .rejected error scope => .rejected error scope
  | .resourceExhausted scope => .resourceExhausted scope

def scope : StreamingResult ε α → AllocationScope
  | .success _ scope => scope
  | .rejected _ scope => scope
  | .resourceExhausted scope => scope

end StreamingResult

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Execute every finite input chunk in order. Output is retained as chunks;
    no concatenation or whole-buffer transformation is hidden in this driver. -/
def driveStreaming {Error State : Type}
    (push : State → AllocationScope → ByteArray →
      StreamingResult Error (State × List ByteArray)) :
    State → AllocationScope → List ByteArray →
      StreamingResult Error (State × List ByteArray)
  | state, scope, [] => .success (state, []) scope
  | state, scope, chunk :: rest =>
    match push state scope chunk with
    | .rejected error updated => .rejected error updated
    | .resourceExhausted updated => .resourceExhausted updated
    | .success (next, emitted) updated =>
      match driveStreaming push next updated rest with
      | .success (final, tail) finalScope => .success (final, emitted ++ tail) finalScope
      | .rejected error finalScope => .rejected error finalScope
      | .resourceExhausted finalScope => .resourceExhausted finalScope

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Primitive operations in both directions. A target is free to emit zero,
    one, or many chunks from each push and finish operation. -/
structure StreamingZlibOperations where
  CompressionState : Type
  DecompressionState : Type
  startCompression : AllocationScope → StreamingResult Empty CompressionState
  pushCompression : CompressionState → AllocationScope → ByteArray →
    StreamingResult Empty (CompressionState × List ByteArray)
  finishCompression : CompressionState → AllocationScope →
    StreamingResult Empty (List ByteArray)
  startDecompression : AllocationScope → StreamingResult String DecompressionState
  pushDecompression : DecompressionState → AllocationScope → ByteArray →
    StreamingResult String (DecompressionState × List ByteArray)
  finishDecompression : DecompressionState → AllocationScope →
    StreamingResult String (List ByteArray)

private def completeStreaming {Error State : Type}
    (finish : State → AllocationScope → StreamingResult Error (List ByteArray)) :
    StreamingResult Error (State × List ByteArray) → StreamingResult Error (List ByteArray)
  | .rejected error scope => .rejected error scope
  | .resourceExhausted scope => .resourceExhausted scope
  | .success (state, emitted) scope =>
    match finish state scope with
    | .success tail finalScope => .success (emitted ++ tail) finalScope
    | .rejected error finalScope => .rejected error finalScope
    | .resourceExhausted finalScope => .resourceExhausted finalScope

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def runCompression (operations : StreamingZlibOperations)
    (scope : AllocationScope) (input : List ByteArray) :
    StreamingResult Empty (List ByteArray) :=
  match operations.startCompression scope with
  | .rejected error updated => .rejected error updated
  | .resourceExhausted updated => .resourceExhausted updated
  | .success initial updated =>
    completeStreaming operations.finishCompression
      (driveStreaming operations.pushCompression initial updated input)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def runDecompression (operations : StreamingZlibOperations)
    (scope : AllocationScope) (input : List ByteArray) :
    StreamingResult String (List ByteArray) :=
  match operations.startDecompression scope with
  | .rejected error updated => .rejected error updated
  | .resourceExhausted updated => .resourceExhausted updated
  | .success initial updated =>
    completeStreaming operations.finishDecompression
      (driveStreaming operations.pushDecompression initial updated input)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Proof-carrying streaming Zlib ABI. Compression correctness is stated by
    decoding the complete emitted GZIP stream, so implementations may choose
    any valid RFC 1951 encoding and any output partition. Decompression is
    related directly to the library's RFC parser. -/
structure StreamingZlibCapability extends StreamingZlibOperations where
  compressionSound : ∀ scope input output finalScope,
    runCompression toStreamingZlibOperations scope input = .success output finalScope →
      gzipDecompress (joinChunks output) = .ok (joinChunks input)
  decompressionSound : ∀ scope input output finalScope,
    runDecompression toStreamingZlibOperations scope input = .success output finalScope →
      gzipDecompress (joinChunks input) = .ok (joinChunks output)
  decompressionMalformedSound : ∀ scope input message finalScope,
    runDecompression toStreamingZlibOperations scope input = .rejected message finalScope →
      gzipDecompress (joinChunks input) = .error message

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Whole-buffer compression is a one-chunk fold over the streaming primitive. -/
def compressAll (capability : StreamingZlibCapability)
    (scope : AllocationScope) (input : ByteArray) : StreamingResult Empty ByteArray :=
  (runCompression capability.toStreamingZlibOperations scope [input]).map joinChunks

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Whole-buffer decompression is a one-chunk fold over the streaming primitive. -/
def decompressAll (capability : StreamingZlibCapability)
    (scope : AllocationScope) (input : ByteArray) : StreamingResult String ByteArray :=
  (runDecompression capability.toStreamingZlibOperations scope [input]).map joinChunks

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
theorem compressAll_sound (capability : StreamingZlibCapability)
    (scope : AllocationScope) (input output : ByteArray) (finalScope : AllocationScope)
    (h : compressAll capability scope input = .success output finalScope) :
    gzipDecompress output = .ok input := by
  unfold compressAll at h
  cases hr : runCompression capability.toStreamingZlibOperations scope [input] with
  | rejected error updated => exact Empty.elim error
  | resourceExhausted updated => simp [StreamingResult.map, hr] at h
  | success chunks updated =>
    have hs := capability.compressionSound scope [input] chunks updated hr
    simp only [StreamingResult.map, hr] at h
    cases h
    simpa [joinChunks] using hs

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
theorem decompressAll_sound (capability : StreamingZlibCapability)
    (scope : AllocationScope) (input output : ByteArray) (finalScope : AllocationScope)
    (h : decompressAll capability scope input = .success output finalScope) :
    gzipDecompress input = .ok output := by
  unfold decompressAll at h
  cases hr : runDecompression capability.toStreamingZlibOperations scope [input] with
  | rejected message updated => simp [StreamingResult.map, hr] at h
  | resourceExhausted updated => simp [StreamingResult.map, hr] at h
  | success chunks updated =>
    have hs := capability.decompressionSound scope [input] chunks updated hr
    simp only [StreamingResult.map, hr] at h
    cases h
    simpa [joinChunks] using hs

private def bufferChunk (Error : Type) (state : List ByteArray) (scope : AllocationScope)
    (chunk : ByteArray) : StreamingResult Error (List ByteArray × List ByteArray) :=
  match scope.charge chunk.size with
  | .granted updated => .success (state ++ [chunk], []) updated
  | .exhausted updated => .resourceExhausted updated

private def bufferedFinishCompression (state : List ByteArray) (scope : AllocationScope) :
    StreamingResult Empty (List ByteArray) :=
  let input := joinChunks state
  let output := gzipCompress input
  match scope.charge output.size with
  | .granted updated => .success [output] (updated.release input.size)
  | .exhausted updated => .resourceExhausted (updated.release input.size)

private def bufferedFinishDecompression (state : List ByteArray) (scope : AllocationScope) :
    StreamingResult String (List ByteArray) :=
  let input := joinChunks state
  match gzipDecompress input with
  | .error message => .rejected message (scope.release input.size)
  | .ok output =>
    match scope.charge output.size with
    | .granted updated => .success [output] (updated.release input.size)
    | .exhausted updated => .resourceExhausted (updated.release input.size)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- A deliberately simple realization of the streaming ABI. It retains input
    chunks and performs the transform at `finish`; this is a valid (though not
    latency-optimal) target lowering because callers interact only through the
    stateful streaming operations. The whole-buffer helpers above remain folds
    over this interface, never its definition. -/
def bufferedStreamingOperations : StreamingZlibOperations where
  CompressionState := List ByteArray
  DecompressionState := List ByteArray
  startCompression scope := .success [] scope
  pushCompression := bufferChunk Empty
  finishCompression := bufferedFinishCompression
  startDecompression scope := .success [] scope
  pushDecompression := bufferChunk String
  finishDecompression := bufferedFinishDecompression

private theorem drive_bufferChunk_success (Error : Type) (initial input final : List ByteArray)
    (scope finalScope : AllocationScope) (emitted : List ByteArray)
    (h : driveStreaming (bufferChunk Error) initial scope input =
      .success (final, emitted) finalScope) :
    final = initial ++ input ∧ emitted = [] := by
  induction input generalizing initial scope final finalScope emitted with
  | nil =>
    simp only [driveStreaming] at h
    injection h with hp hs
    injection hp with hf he
    subst final
    subst emitted
    exact ⟨(List.append_nil initial).symm, rfl⟩
  | cons chunk rest ih =>
    simp only [driveStreaming] at h
    unfold bufferChunk at h
    cases hc : scope.charge chunk.size with
    | exhausted failed =>
      simp only [hc] at h
      cases h
    | granted updated =>
      simp only [hc] at h
      cases hd : driveStreaming (bufferChunk Error) (initial ++ [chunk]) updated rest with
      | rejected error failed =>
        have hd' := hd
        unfold bufferChunk at hd'
        rw [hd'] at h
        cases h
      | resourceExhausted failed =>
        have hd' := hd
        unfold bufferChunk at hd'
        rw [hd'] at h
        cases h
      | success value finished =>
        rcases value with ⟨next, tail⟩
        have hi := ih (initial ++ [chunk]) next updated finished tail hd
        have hd' := hd
        unfold bufferChunk at hd'
        rw [hd'] at h
        injection h with hp hs
        injection hp with hf he
        subst final
        subst emitted
        rcases hi with ⟨rfl, rfl⟩
        simp [List.append_assoc]

private theorem drive_bufferChunk_no_rejected (Error : Type) (initial input : List ByteArray)
    (scope finalScope : AllocationScope) (error : Error)
    (h : driveStreaming (bufferChunk Error) initial scope input = .rejected error finalScope) :
    False := by
  induction input generalizing initial scope finalScope error with
  | nil => simp [driveStreaming] at h
  | cons chunk rest ih =>
    simp only [driveStreaming] at h
    unfold bufferChunk at h
    cases hc : scope.charge chunk.size with
    | exhausted failed =>
      simp only [hc] at h
      cases h
    | granted updated =>
      simp only [hc] at h
      cases hd : driveStreaming (bufferChunk Error) (initial ++ [chunk]) updated rest with
      | rejected nested failed =>
        have contradiction := ih (initial ++ [chunk]) updated failed nested hd
        exact contradiction
      | resourceExhausted failed =>
        have hd' := hd
        unfold bufferChunk at hd'
        rw [hd'] at h
        cases h
      | success value finished =>
        have hd' := hd
        unfold bufferChunk at hd'
        rw [hd'] at h
        cases h

set_option maxHeartbeats 1000000 in
private theorem runCompression_buffered (scope : AllocationScope) (input : List ByteArray) :
    runCompression bufferedStreamingOperations scope input =
      completeStreaming bufferedFinishCompression
        (driveStreaming (bufferChunk Empty) [] scope input) := by
  rfl

set_option maxHeartbeats 1000000 in
private theorem runDecompression_buffered (scope : AllocationScope) (input : List ByteArray) :
    runDecompression bufferedStreamingOperations scope input =
      completeStreaming bufferedFinishDecompression
        (driveStreaming (bufferChunk String) [] scope input) := by
  rfl

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
set_option maxHeartbeats 1000000 in
def bufferedStreamingZlibCapability : StreamingZlibCapability where
  toStreamingZlibOperations := bufferedStreamingOperations
  compressionSound := by
    intro scope input output finalScope h
    rw [runCompression_buffered] at h
    cases hd : driveStreaming (bufferChunk Empty) [] scope input with
    | rejected error failed => exact Empty.elim error
    | resourceExhausted failed => simp [hd, completeStreaming] at h
    | success value afterInput =>
      rcases value with ⟨state, emitted⟩
      have hs := drive_bufferChunk_success Empty [] input state scope afterInput emitted hd
      rcases hs with ⟨hstate, hemitted⟩
      simp only [List.nil_append] at hstate
      subst state
      subst emitted
      rw [hd] at h
      unfold completeStreaming bufferedFinishCompression at h
      cases hc : afterInput.charge (gzipCompress (joinChunks input)).size with
      | exhausted failed => simp [hc] at h
      | granted afterOutput =>
        simp only [hc] at h
        cases h
        simpa [joinChunks] using gzip_roundtrip_soundness (joinChunks input)
  decompressionSound := by
    intro scope input output finalScope h
    rw [runDecompression_buffered] at h
    cases hd : driveStreaming (bufferChunk String) [] scope input with
    | rejected message failed => simp [hd, completeStreaming] at h
    | resourceExhausted failed => simp [hd, completeStreaming] at h
    | success value afterInput =>
      rcases value with ⟨state, emitted⟩
      have hs := drive_bufferChunk_success String [] input state scope afterInput emitted hd
      rcases hs with ⟨hstate, hemitted⟩
      simp only [List.nil_append] at hstate
      subst state
      subst emitted
      rw [hd] at h
      unfold completeStreaming bufferedFinishDecompression at h
      cases hg : gzipDecompress (joinChunks input) with
      | error message => simp [hg] at h
      | ok decoded =>
        cases hc : afterInput.charge decoded.size with
        | exhausted failed => simp [hg, hc] at h
        | granted afterOutput =>
          simp only [hg, hc] at h
          cases h
          simpa [joinChunks] using hg
  decompressionMalformedSound := by
    intro scope input message finalScope h
    rw [runDecompression_buffered] at h
    cases hd : driveStreaming (bufferChunk String) [] scope input with
    | rejected driveMessage failed =>
      exact (drive_bufferChunk_no_rejected String [] input scope failed driveMessage hd).elim
    | resourceExhausted failed => simp [hd, completeStreaming] at h
    | success value afterInput =>
      rcases value with ⟨state, emitted⟩
      have hs := drive_bufferChunk_success String [] input state scope afterInput emitted hd
      rcases hs with ⟨hstate, hemitted⟩
      simp only [List.nil_append] at hstate
      subst state
      subst emitted
      rw [hd] at h
      unfold completeStreaming bufferedFinishDecompression at h
      cases hg : gzipDecompress (joinChunks input) with
      | error actual =>
        simp only [hg] at h
        cases h
        simpa using hg
      | ok decoded =>
        cases hc : afterInput.charge decoded.size with
        | exhausted failed => simp [hg, hc] at h
        | granted afterOutput => simp [hg, hc] at h

end Stdlib.Zlib

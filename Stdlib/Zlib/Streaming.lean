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

import Stdlib.Zlib.Gzip

namespace Stdlib.Zlib

/-!
Proof-carrying streaming GZIP/GUNZIP capabilities.

The domain is every finite byte stream.  Finite storage is represented by an
explicit, recoverable outcome; it is never used to truncate the input domain or
turn a prefix into a successful result.
-/

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def joinChunks (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) ByteArray.empty

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
structure StreamingBudget where
  inputBytes : Nat
  outputBytes : Nat
deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
inductive StreamingResult (α : Type) where
  | success (value : α)
  | resourceExhausted
deriving Repr

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def boundedGzip (budget : StreamingBudget) (input : ByteArray) : StreamingResult ByteArray :=
  let output := gzipCompress input
  if input.size ≤ budget.inputBytes && output.size ≤ budget.outputBytes then
    .success output
  else
    .resourceExhausted

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def boundedGunzip (budget : StreamingBudget) (input : ByteArray) :
    StreamingResult (Except String ByteArray) :=
  if input.size ≤ budget.inputBytes then
    match gzipDecompress input with
    | .error err => .success (.error err)
    | .ok output =>
      if output.size ≤ budget.outputBytes then .success (.ok output)
      else .resourceExhausted
  else
    .resourceExhausted

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
structure StreamingZlibCapability where
  budget : StreamingBudget
  compress : List ByteArray → StreamingResult ByteArray
  decompress : List ByteArray → StreamingResult (Except String ByteArray)
  compress_sound : ∀ chunks, compress chunks = boundedGzip budget (joinChunks chunks)
  decompress_sound : ∀ chunks, decompress chunks = boundedGunzip budget (joinChunks chunks)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def boundedZlibCapability (budget : StreamingBudget) : StreamingZlibCapability where
  budget := budget
  compress chunks := boundedGzip budget (joinChunks chunks)
  decompress chunks := boundedGunzip budget (joinChunks chunks)
  compress_sound _ := rfl
  decompress_sound _ := rfl

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
structure StreamingByteTransport where
  readAll : ByteArray → List ByteArray
  writeAll : ByteArray → List ByteArray
  read_sound : ∀ input, joinChunks (readAll input) = input
  write_sound : ∀ output, joinChunks (writeAll output) = output

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def composeStreamingGzip (transport : StreamingByteTransport)
    (zlib : StreamingZlibCapability) (input : ByteArray) : StreamingResult ByteArray :=
  match zlib.compress (transport.readAll input) with
  | .success output => .success (joinChunks (transport.writeAll output))
  | .resourceExhausted => .resourceExhausted

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
theorem compose_streaming_gzip (transport : StreamingByteTransport)
    (zlib : StreamingZlibCapability) (input : ByteArray) :
    composeStreamingGzip transport zlib input = boundedGzip zlib.budget input := by
  unfold composeStreamingGzip
  rw [zlib.compress_sound, transport.read_sound]
  cases boundedGzip zlib.budget input with
  | success output => simp [transport.write_sound]
  | resourceExhausted => rfl

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def composeStreamingGunzip (transport : StreamingByteTransport)
    (zlib : StreamingZlibCapability) (input : ByteArray) :
    StreamingResult (Except String ByteArray) :=
  match zlib.decompress (transport.readAll input) with
  | .success (.ok output) => .success (.ok (joinChunks (transport.writeAll output)))
  | .success (.error err) => .success (.error err)
  | .resourceExhausted => .resourceExhausted

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
theorem compose_streaming_gunzip (transport : StreamingByteTransport)
    (zlib : StreamingZlibCapability) (input : ByteArray) :
    composeStreamingGunzip transport zlib input = boundedGunzip zlib.budget input := by
  unfold composeStreamingGunzip
  rw [zlib.decompress_sound, transport.read_sound]
  cases h : boundedGunzip zlib.budget input with
  | resourceExhausted => rfl
  | success result =>
    cases result with
    | error err => rfl
    | ok output => simp [transport.write_sound]

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
inductive ScopedStreamingResult (α : Type) where
  | success (value : α) (scope : AllocationScope)
  | resourceExhausted (scope : AllocationScope)
deriving Repr

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def scopedBoundedGzip (scope : AllocationScope) (input : ByteArray) :
    ScopedStreamingResult ByteArray :=
  match scope.charge input.size with
  | .exhausted failed => .resourceExhausted failed
  | .granted withInput =>
    let output := gzipCompress input
    match withInput.charge output.size with
    | .granted withOutput => .success output (withOutput.release input.size)
    | .exhausted failedOutput => .resourceExhausted (failedOutput.release input.size)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
structure ScopedStreamingZlibCapability where
  compress : AllocationScope → List ByteArray → ScopedStreamingResult ByteArray
  compress_sound : ∀ scope chunks,
    compress scope chunks = scopedBoundedGzip scope (joinChunks chunks)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def scopedBoundedZlibCapability : ScopedStreamingZlibCapability where
  compress scope chunks := scopedBoundedGzip scope (joinChunks chunks)
  compress_sound _ _ := rfl

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def composeScopedStreamingGzip (transport : StreamingByteTransport)
    (zlib : ScopedStreamingZlibCapability) (scope : AllocationScope) (input : ByteArray) :
    ScopedStreamingResult ByteArray :=
  match zlib.compress scope (transport.readAll input) with
  | .success output updated =>
    .success (joinChunks (transport.writeAll output)) updated
  | .resourceExhausted updated => .resourceExhausted updated

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
theorem compose_scoped_streaming_gzip (transport : StreamingByteTransport)
    (zlib : ScopedStreamingZlibCapability) (scope : AllocationScope) (input : ByteArray) :
    composeScopedStreamingGzip transport zlib scope input = scopedBoundedGzip scope input := by
  unfold composeScopedStreamingGzip
  rw [zlib.compress_sound, transport.read_sound]
  cases scopedBoundedGzip scope input with
  | success output updated => simp [transport.write_sound]
  | resourceExhausted updated => rfl

end Stdlib.Zlib

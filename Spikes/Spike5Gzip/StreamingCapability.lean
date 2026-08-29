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

import Gasm.Core.Verification
import Gasm.Targets.WASI.ABI
import Spikes.Spike5Gzip.Spec

/-!
The streaming boundary for Spike 5.

This is deliberately a capability contract, not a maximum-buffer assumption.
`ByteArray` values and lists of chunks are finite, but there is no fixed upper
bound on either their number or their sizes.  A target is allowed to choose a
small reusable WASI iovec; its proof must establish that repeated `fd_read` and
`fd_write` calls refine this contract.  Thus a finite input is never rejected
merely because it is longer than a workspace.
-/

namespace Spikes.Spike5Gzip

open Gasm.Core.Verification
open Gasm.Targets.WASI
open Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Concatenate a finite sequence of stream chunks.  This is the semantic
    stream, independent of how an implementation chooses its I/O chunk sizes. -/
def joinChunks (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (fun acc chunk => acc ++ chunk) ByteArray.empty

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- A proof-carrying incremental Zlib implementation.  `state` may grow while
    finite input arrives; importantly, this interface contains no capacity or
    resource-exhaustion result.  The two laws state exactly what a target
    library boundary must preserve after *every finite list* of chunks. -/
structure StreamingZlibCapability where
  State : Type
  initial : State
  push : State → ByteArray → State
  finishCompress : State → ByteArray
  finishDecompress : State → Except String ByteArray
  compress_sound : ∀ chunks,
    finishCompress (chunks.foldl push initial) = gzipCompress (joinChunks chunks)
  decompress_sound : ∀ chunks,
    finishDecompress (chunks.foldl push initial) = gzipDecompress (joinChunks chunks)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Reference streaming Zlib capability.  Its state grows with the finite input
    stream, making the all-finite-input resource policy explicit.  A bounded
    native/Wasm implementation must refine this contract by retaining only the
    working window, but may not weaken either law. -/
def growingZlibCapability : StreamingZlibCapability where
  State := ByteArray
  initial := ByteArray.empty
  push := fun state chunk => state ++ chunk
  finishCompress := gzipCompress
  finishDecompress := gzipDecompress
  compress_sound := by
    intro chunks
    rfl
  decompress_sound := by
    intro chunks
    rfl

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- The external byte-stream portion of a WASI capability.  `readAll` models
    the complete sequence of successful `fd_read` calls and `writeAll` the
    complete sequence of successful `fd_write` calls.  The laws rule out both
    truncation and invented bytes without imposing a fixed buffer cap. -/
structure WasiStreamingCapability where
  readAll : ByteArray → List ByteArray
  writeAll : ByteArray → List ByteArray
  read_sound : ∀ stdin, joinChunks (readAll stdin) = stdin
  write_sound : ∀ stdout, joinChunks (writeAll stdout) = stdout

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- The minimal semantic WASI stream capability.  The singleton presentation is
    intentionally only a *semantic partition*: it asserts no physical read
    size.  A concrete lowering may refine it with arbitrarily many `fd_read`
    calls, since the sole observable law is concatenation. -/
def wasiFdReadWriteCapability : WasiStreamingCapability where
  readAll := fun stdin => [stdin]
  writeAll := fun stdout => [stdout]
  read_sound := by intro stdin; rfl
  write_sound := by intro stdout; rfl

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Required imports for a streaming Spike 5 WASI component.  Keeping this in
    the capability composition makes it impossible for a later artifact proof
    to silently substitute an embedded sample for the `fd_read` boundary. -/
def spike5StreamingWasiImports : List String := ["fd_read", "fd_write", "proc_exit"]

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
theorem spike5_streaming_imports_include_fd_read :
    "fd_read" ∈ spike5StreamingWasiImports := by decide

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
theorem spike5_streaming_imports_include_fd_write :
    "fd_write" ∈ spike5StreamingWasiImports := by decide

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Composition of the external WASI stream with an incremental Zlib library.
    This is the capability law a `VerifiedProgram` migration consumes: the
    target may split I/O any way it likes, but the complete output is the GZIP
    transform of the complete input. -/
structure StreamingZlibWasiComposition where
  wasi : WasiStreamingCapability
  zlib : StreamingZlibCapability
  writes_compressed : ∀ stdin,
    joinChunks (wasi.writeAll (zlib.finishCompress
      ((wasi.readAll stdin).foldl zlib.push zlib.initial))) = gzipCompress stdin
  writes_decompressed : ∀ stdin,
    joinChunks (wasi.writeAll (match zlib.finishDecompress
      ((wasi.readAll stdin).foldl zlib.push zlib.initial) with
      | .ok bytes => bytes
      | .error _ => ByteArray.empty)) =
      match gzipDecompress stdin with
      | .ok bytes => bytes
      | .error _ => ByteArray.empty

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- The compression composition law follows solely from the two component
    contracts.  In particular it is insensitive to the number, placement, or
    size of successful WASI reads and writes. -/
theorem compose_streaming_gzip (wasi : WasiStreamingCapability)
    (zlib : StreamingZlibCapability) (stdin : ByteArray) :
    joinChunks (wasi.writeAll (zlib.finishCompress
      ((wasi.readAll stdin).foldl zlib.push zlib.initial))) = gzipCompress stdin := by
  rw [wasi.write_sound, zlib.compress_sound, wasi.read_sound]

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- The corresponding decompression composition law, including the CLI's
    explicit empty-output representation for a decompression error. -/
theorem compose_streaming_gunzip (wasi : WasiStreamingCapability)
    (zlib : StreamingZlibCapability) (stdin : ByteArray) :
    joinChunks (wasi.writeAll (match zlib.finishDecompress
      ((wasi.readAll stdin).foldl zlib.push zlib.initial) with
      | .ok bytes => bytes
      | .error _ => ByteArray.empty)) =
      match gzipDecompress stdin with
      | .ok bytes => bytes
      | .error _ => ByteArray.empty := by
  rw [wasi.write_sound, zlib.decompress_sound, wasi.read_sound]

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- The reference composition is kernel-checked from the component laws. -/
def growingZlibWasiComposition : StreamingZlibWasiComposition where
  wasi := wasiFdReadWriteCapability
  zlib := growingZlibCapability
  writes_compressed := by
    exact compose_streaming_gzip wasiFdReadWriteCapability growingZlibCapability
  writes_decompressed := by
    exact compose_streaming_gunzip wasiFdReadWriteCapability growingZlibCapability

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The all-finite-environment compression law at Spike 5's real input boundary.
    It composes `Environment.stdin`, WASI's read/write capability, and Zlib's
    universal transform without selecting a sample input. -/
theorem spike5_streaming_compresses_every_environment (env : Environment) :
    joinChunks
      (growingZlibWasiComposition.wasi.writeAll
        (growingZlibWasiComposition.zlib.finishCompress
          ((growingZlibWasiComposition.wasi.readAll env.stdin).foldl
            growingZlibWasiComposition.zlib.push
            growingZlibWasiComposition.zlib.initial))) = gzipCompress env.stdin := by
  exact growingZlibWasiComposition.writes_compressed env.stdin

end Spikes.Spike5Gzip

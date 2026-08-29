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
import Gasm.Effects.Inject
import Gasm.Effects.Process
import Gasm.Effects.Trace
import Gasm.Targets.WASI.ABI
import Spikes.Spike5Gzip.Spec

/-!
The bounded streaming boundary for Spike 5.

The input domain remains every finite `Environment.stdin`; a finite target
budget does not turn an over-budget input into a truncated successful run. It
instead yields the explicit `resourceExhausted` result. A target may split reads
and writes at any sizes, but must refine the composition law for every resulting
finite chunk sequence.
-/

namespace Spikes.Spike5Gzip

open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.WASI
open Stdlib.Zlib

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def joinChunks (chunks : List ByteArray) : ByteArray :=
  chunks.foldl (fun acc chunk => acc ++ chunk) ByteArray.empty

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
structure StreamingBudget where
  inputBytes : Nat
  outputBytes : Nat
deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- An allocation/growth-sensitive outcome. Resource exhaustion has no output
    payload, so it cannot be mistaken for a successful empty stream. -/
inductive StreamingResult (α : Type) where
  | success (value : α) : StreamingResult α
  | resourceExhausted : StreamingResult α
deriving Repr

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Exact finite-budget GZIP behavior. Input retention and compressed-output
    allocation are separate fallible growth operations. -/
def boundedGzip (budget : StreamingBudget) (input : ByteArray) : StreamingResult ByteArray :=
  let compressed := gzipCompress input
  if input.size ≤ budget.inputBytes && compressed.size ≤ budget.outputBytes then
    .success compressed
  else
    .resourceExhausted

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Exact finite-budget GUNZIP behavior. A malformed GZIP stream remains a
    normal GZIP error; only failed storage growth is `resourceExhausted`. -/
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
/-- A proof-carrying incremental Zlib capability with finite, fallible growth.
    Its laws are exact: an implementation cannot return a prefix as success or
    hide an over-budget stream behind a successful empty output. -/
structure StreamingZlibCapability where
  budget : StreamingBudget
  compress : List ByteArray → StreamingResult ByteArray
  decompress : List ByteArray → StreamingResult (Except String ByteArray)
  compress_sound : ∀ chunks, compress chunks = boundedGzip budget (joinChunks chunks)
  decompress_sound : ∀ chunks, decompress chunks = boundedGunzip budget (joinChunks chunks)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Reference Zlib capability. A target allocator must refine these exact
    results; no target-specific fixed-size limit appears in the contract. -/
def boundedZlibCapability (budget : StreamingBudget) : StreamingZlibCapability where
  budget := budget
  compress := fun chunks => boundedGzip budget (joinChunks chunks)
  decompress := fun chunks => boundedGunzip budget (joinChunks chunks)
  compress_sound := by intro chunks; rfl
  decompress_sound := by intro chunks; rfl

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Complete successful `fd_read`/`fd_write` sequences. The laws are agnostic
    about physical I/O chunk size and rule out truncation or fabricated bytes. -/
structure WasiStreamingCapability where
  readAll : ByteArray → List ByteArray
  writeAll : ByteArray → List ByteArray
  read_sound : ∀ stdin, joinChunks (readAll stdin) = stdin
  write_sound : ∀ stdout, joinChunks (writeAll stdout) = stdout

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
def wasiFdReadWriteCapability : WasiStreamingCapability where
  readAll := fun stdin => [stdin]
  writeAll := fun stdout => [stdout]
  read_sound := by intro stdin; rfl
  write_sound := by intro stdout; rfl

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Imports which a concrete Spike 5 streaming WASI artifact must retain. -/
def spike5StreamingWasiImports : List String := ["fd_read", "fd_write", "proc_exit"]

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
theorem spike5_streaming_imports_include_fd_read :
    "fd_read" ∈ spike5StreamingWasiImports := by decide

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
theorem spike5_streaming_imports_include_fd_write :
    "fd_write" ∈ spike5StreamingWasiImports := by decide

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def composeStreamingGzip (wasi : WasiStreamingCapability)
    (zlib : StreamingZlibCapability) (stdin : ByteArray) : StreamingResult ByteArray :=
  match zlib.compress (wasi.readAll stdin) with
  | .success output => .success (joinChunks (wasi.writeAll output))
  | .resourceExhausted => .resourceExhausted

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- All finite inputs have an exact observable result: complete GZIP bytes or
    explicit resource failure, independently of the fd_read/fd_write partition. -/
theorem compose_streaming_gzip (wasi : WasiStreamingCapability)
    (zlib : StreamingZlibCapability) (stdin : ByteArray) :
    composeStreamingGzip wasi zlib stdin = boundedGzip zlib.budget stdin := by
  unfold composeStreamingGzip
  rw [zlib.compress_sound, wasi.read_sound]
  cases boundedGzip zlib.budget stdin with
  | success output => simp [wasi.write_sound]
  | resourceExhausted => simp

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Spike 5 reserves exit status 2 for a failed allocation/growth request.
    No compressed prefix is emitted on this trace. -/
def gzipResourceFailureTrace : List AnyEvent :=
  [Inject.inject (ProcessEvent.exit 2)]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- The trace specification to be supplied to the sole `VerifiedProgram`: the
    successful CLI behavior is unchanged, and finite-resource failure is now an
    explicit alternative rather than a narrowed stdin domain. -/
def gzipBudgetedEnvironmentTrace (budget : StreamingBudget) (env : Environment) : List AnyEvent :=
  match boundedGzip budget env.stdin with
  | .success _ => gzipParametricModelTrace env.stdin
  | .resourceExhausted => gzipResourceFailureTrace

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
theorem spike5_streaming_outcome_every_environment (budget : StreamingBudget)
    (env : Environment) :
    composeStreamingGzip wasiFdReadWriteCapability (boundedZlibCapability budget) env.stdin =
      boundedGzip budget env.stdin := by
  exact compose_streaming_gzip wasiFdReadWriteCapability (boundedZlibCapability budget) env.stdin

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Per-request allocation scope supplied by the caller.  `live` is memory
    currently owned by the request, `peak` is its high-water mark, and `total`
    is cumulative allocation charged to that request.  The library never owns a
    hidden global budget. -/
structure AllocationScope where
  capacity : Nat
  live : Nat := 0
  peak : Nat := 0
  total : Nat := 0
deriving DecidableEq, Repr, Inhabited

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
inductive AllocationAttempt where
  | granted (scope : AllocationScope) : AllocationAttempt
  | exhausted (scope : AllocationScope) : AllocationAttempt
deriving Repr

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Charge an allocation to its caller's scope.  A failed charge preserves the
    caller's scope, making exhaustion recoverable at request/server boundaries. -/
def AllocationScope.charge (scope : AllocationScope) (bytes : Nat) : AllocationAttempt :=
  if scope.live + bytes ≤ scope.capacity then
    let updated : AllocationScope :=
      { capacity := scope.capacity
        live := scope.live + bytes
        peak := max scope.peak (scope.live + bytes)
        total := scope.total + bytes }
    .granted updated
  else
    .exhausted scope

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Release live request memory without erasing historical total/peak charges. -/
def AllocationScope.release (scope : AllocationScope) (bytes : Nat) : AllocationScope :=
  { scope with live := scope.live - bytes }

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
inductive ScopedStreamingResult (α : Type) where
  | success (value : α) (scope : AllocationScope) : ScopedStreamingResult α
  | resourceExhausted (scope : AllocationScope) : ScopedStreamingResult α
deriving Repr

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Reference compression accounting.  Input and output allocations are both
    charged to the supplied scope. If output growth fails, input is released
    before returning, so one failed request cannot retain live memory or poison
    a later request. -/
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
/-- The scoped library contract.  Its input scope is caller-owned and its result
    returns the updated same-request scope, which is the composition rule for
    crossing a Zlib library boundary. -/
structure ScopedStreamingZlibCapability where
  compress : AllocationScope → List ByteArray → ScopedStreamingResult ByteArray
  compress_sound : ∀ scope chunks,
    compress scope chunks = scopedBoundedGzip scope (joinChunks chunks)

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
def scopedBoundedZlibCapability : ScopedStreamingZlibCapability where
  compress := fun scope chunks => scopedBoundedGzip scope (joinChunks chunks)
  compress_sound := by intro scope chunks; rfl

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Composition preserves caller accounting across WASI and Zlib boundaries:
    fd_read/fd_write merely partition bytes; the scope returned by Zlib is the
    scope returned to the request owner. -/
def composeScopedStreamingGzip (wasi : WasiStreamingCapability)
    (zlib : ScopedStreamingZlibCapability) (scope : AllocationScope) (stdin : ByteArray) :
    ScopedStreamingResult ByteArray :=
  match zlib.compress scope (wasi.readAll stdin) with
  | .success output updated => .success (joinChunks (wasi.writeAll output)) updated
  | .resourceExhausted updated => .resourceExhausted updated

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
theorem compose_scoped_streaming_gzip (wasi : WasiStreamingCapability)
    (zlib : ScopedStreamingZlibCapability) (scope : AllocationScope) (stdin : ByteArray) :
    composeScopedStreamingGzip wasi zlib scope stdin = scopedBoundedGzip scope stdin := by
  unfold composeScopedStreamingGzip
  rw [zlib.compress_sound, wasi.read_sound]
  cases h : scopedBoundedGzip scope stdin with
  | success output updated => simp [wasi.write_sound]
  | resourceExhausted updated => simp

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Scope-aware trace contract for the eventual sole `VerifiedProgram`.
    Recoverable exhaustion exits this invocation only; the returned scope is
    available to its request/server caller for later independent work. -/
def gzipScopedEnvironmentTrace (scope : AllocationScope) (env : Environment) : List AnyEvent :=
  match scopedBoundedGzip scope env.stdin with
  | .success _ _ => gzipParametricModelTrace env.stdin
  | .resourceExhausted _ => gzipResourceFailureTrace

end Spikes.Spike5Gzip

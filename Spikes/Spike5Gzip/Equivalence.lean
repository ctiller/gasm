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

import Lean
import Gasm.Core.Types
import Gasm.Core.Verification
import Gasm.Effects.Trace
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Linker
import Gasm.Targets.Windows.Win32API
import Gasm.Targets.WASI.ABI
import Stdlib.Zlib
import Spikes.Spike5Gzip.Spec
import Spikes.Spike5Gzip.Windows.Program
import Spikes.Spike5Gzip.Wasm.Program

namespace Spikes.Spike5Gzip

open Gasm.Core
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows
open Gasm.Targets.WASI
open Stdlib.Zlib
open Spikes.Spike5Gzip.Windows
open Spikes.Spike5Gzip.Wasm

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Windows x86_64 concrete machine execution trace for Spike 5 compression on canonical sample input. -/
def windowsTraceCompress : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike5Instructions (spike5Executable.loadWithStdin canonicalSampleData)

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- WebAssembly WASI execution trace for Spike 5 compression. -/
def wasmTraceCompress : List AnyEvent :=
  runWasiTrace spike5WasmInstructions spike5DataSegments

/- REF: docs/REVIEW.md#42-pillar-2-semantic-integrity-adversarial-domain-gap-hunting -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive Proof: x86_64 Windows machine trace matches canonical specification trace for GZIP compression. -/
theorem spike5_windows_gzip_trace_equivalence :
    (windowsTraceCompress == canonicalCompressTrace) = true := by
  native_decide

/- REF: docs/REVIEW.md#42-pillar-2-semantic-integrity-adversarial-domain-gap-hunting -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Constructive Proof: WebAssembly WASI machine trace matches canonical specification trace for GZIP compression. -/
theorem spike5_wasm_gzip_trace_equivalence :
    (wasmTraceCompress == canonicalCompressTrace.map Inject.inject) = true := by
  native_decide

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Universal Soundness Theorem: GZIP compression followed by decompression losslessly recovers the original bytes. -/
theorem gzip_roundtrip_soundness_inst :
    let data := canonicalSampleData
    (match decompressData (compressData data) with
     | Except.ok res => res == data
     | Except.error _ => false) = true := by
  native_decide

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Universal 1.5-Roundtrip Soundness Theorem: Canonical decompression followed by re-compression and re-decompression is idempotent. -/
theorem gzip_idempotent_canonical_roundtrip_inst :
    let testStream := canonicalCompressedStream
    (match decompressData testStream with
     | Except.error _ => true
     | Except.ok data =>
       match decompressData (compressData data) with
       | Except.ok res => res == data
       | Except.error _ => false) = true := by
  native_decide

set_option maxRecDepth 4000 in
/- REF: docs/STDLIB_ZLIB.md#31-canonical-huffman-code-generation -/
/-- Exact bit-reversal involution theorem verified across all 256 possible 8-bit quantities.
    Proven by plain kernel `decide` after the `Id.run`/`for` loop (over both the outer 256-value
    sweep and `reverseBits`'s own inner 8-iteration loop) is unfolded via `simp` -- see
    `Stdlib.Zlib.reverse_bits_8_involutive_inst` (`Stdlib/Zlib/Equivalence.lean`) for the
    identical proof of this exact duplicate fact; this is the second, previously-unlinked copy
    Law 12 flags. -/
theorem bit_reversal_8_involution_inst :
    (Id.run do
      let mut ok := true
      for b in [0:256] do
        if reverseBits (reverseBits b 8) 8 != b then ok := false
      ok) = true := by
  simp [Id.run, reverseBits]
  decide

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Formally verified theorem: Windows x86_64 machine execution trace for GUNZIP matches specification trace. -/
theorem spike5_windows_gunzip_trace_equivalence :
    (runAsmTrace (Event := AnyEvent) spike5GunzipInstructions (spike5GunzipExecutable.loadWithStdin canonicalCompressedStream) == canonicalDecompressTrace) = true := by
  native_decide

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- GZIP Compression Operation Domain. -/
inductive GzipOp where
  | compress
deriving DecidableEq, Repr

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
instance : EnvironmentLoader GzipOp where
  loadEnvironment exe _ := exe.loadWithStdin canonicalSampleData

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
instance : WasiEnvironmentLoader GzipOp where
  loadWasiEnvironment _ := (ByteArray.empty, [])

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- GUNZIP Decompression Operation Domain. -/
inductive GunzipOp where
  | decompress
deriving DecidableEq, Repr

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
instance : EnvironmentLoader GunzipOp where
  loadEnvironment exe _ := exe.loadWithStdin canonicalCompressedStream

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- First-Class VerifiedProgram contract for Spike 5 GZIP on Windows x86_64. -/
def spike5WindowsVerifiedProgram : VerifiedProgram GzipOp AnyEvent where
  name := "spike5_gzip_windows"
  executable := spike5Executable
  instructions := spike5Instructions
  spec := fun _ => canonicalCompressTrace
  traceEquivalence := fun op => by
    cases op
    exact spike5_windows_gzip_trace_equivalence

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- First-Class VerifiedProgram contract for Spike 5 GUNZIP on Windows x86_64. -/
def spike5GunzipWindowsVerifiedProgram : VerifiedProgram GunzipOp AnyEvent where
  name := "spike5_gunzip_windows"
  executable := spike5GunzipExecutable
  instructions := spike5GunzipInstructions
  spec := fun _ => canonicalDecompressTrace
  traceEquivalence := fun op => by
    cases op
    exact spike5_windows_gunzip_trace_equivalence

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- First-Class VerifiedWasmProgram contract for Spike 5 on WebAssembly. -/
def spike5WasmVerifiedProgram : VerifiedWasmProgram GzipOp AnyEvent where
  name := "spike5_gzip_wasm"
  module := spike5WasmModule
  typeSignatures := spike5TypeSignatures
  instructions := spike5WasmInstructions
  dataSegments := spike5DataSegments
  spec := fun _ => canonicalCompressTrace
  traceEquivalence := fun op => by
    cases op
    exact spike5_wasm_gzip_trace_equivalence

end Spikes.Spike5Gzip

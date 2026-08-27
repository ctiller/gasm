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
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.FileSystem
import Gasm.Effects.Trace
import Stdlib.Zlib.Gzip

namespace Spikes.Spike5Gzip

open Gasm.Core
open Gasm.Effects
open Stdlib.Zlib

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- CLI operating mode for Spike 5. -/
inductive GzipMode where
  | Compress
  | Decompress
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Configuration record for GZIP execution. -/
structure GzipConfig where
  mode       : GzipMode := .Compress
  keepSource : Bool     := true
  level      : Nat      := 6
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Parses CLI flags into GzipMode (-d / --decompress). -/
def parseGzipFlags (args : List String) : GzipMode :=
  if args.contains "-d" || args.contains "--decompress" || args.contains "-dc" || args.contains "-cd" then
    GzipMode.Decompress
  else
    GzipMode.Compress

/- REF: docs/SPIKES/SPIKE5_GZIP.md#21-pure-transformation-functions -/
/-- Pure functional compression transformation using Stdlib.Zlib.gzipCompress. -/
def compressData (input : ByteArray) : ByteArray :=
  gzipCompress input

/- REF: docs/SPIKES/SPIKE5_GZIP.md#21-pure-transformation-functions -/
/-- Pure functional decompression transformation using Stdlib.Zlib.gzipDecompress. -/
def decompressData (input : ByteArray) : Except String ByteArray :=
  gzipDecompress input

/- REF: docs/SPIKES/SPIKE5_GZIP.md#22-end-to-end-monadic-pipeline -/
/-- Monadic pipeline processing input byte stream with Gzip transformation. -/
def gzipPipelineMonadic (m : Type → Type) [Monad m] [MonadConsole m]
    (mode : GzipMode) (input : ByteArray) : m (Except String ByteArray) := do
  match mode with
  | .Compress =>
    let compressed := compressData input
    let _ ← MonadConsole.printStr s!"Compressed {input.size} bytes -> {compressed.size} bytes\n"
    pure (.ok compressed)
  | .Decompress =>
    match decompressData input with
    | .ok uncompressed =>
      let _ ← MonadConsole.printStr s!"Decompressed {input.size} bytes -> {uncompressed.size} bytes\n"
      pure (.ok uncompressed)
    | .error err =>
      let _ ← MonadConsole.printStr s!"GZIP decompression error: {err}\n"
      pure (.error err)

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- High-level model trace for compression. -/
def gzipModelTraceCompress (input : ByteArray) : List AnyEvent :=
  runModelTrace (gzipPipelineMonadic (TraceM AnyEvent) GzipMode.Compress input) [] []

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- High-level model trace for decompression. -/
def gzipModelTraceDecompress (input : ByteArray) : List AnyEvent :=
  runModelTrace (gzipPipelineMonadic (TraceM AnyEvent) GzipMode.Decompress input) [] []

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Canonical compression sample data. -/
def canonicalSampleData : ByteArray :=
  "gasm Spike 5: High-performance verified GZIP / GUNZIP utility.\n".toUTF8

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Canonical compressed stream using Fixed Huffman format matching assembly engine. -/
def canonicalCompressedStream : ByteArray :=
  gzipCompress canonicalSampleData

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Console output string for verified GZIP compression execution. -/
def gzipOutputMessage : ByteArray :=
  s!"GZIP Stream Verified: in_size={canonicalSampleData.size} out_size={canonicalCompressedStream.size} crc32={crc32 canonicalSampleData}\n".toUTF8

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- High-level behavioral specification for Spike 5 compression run: emits binary GZIP stream to standard output. -/
def gzipSpec [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  let byteStr := match String.fromUTF8? canonicalCompressedStream with
    | some s => s
    | none => String.ofList (canonicalCompressedStream.toList.map (fun b => Char.ofNat b.toNat))
  let _ ← MonadConsole.printStr byteStr
  MonadProcess.exitProcess 0

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- High-level dynamic behavioral specification for GZIP stream compression over arbitrary stdin input. -/
def gzipStreamSpec (input : ByteArray) [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  let compressed := gzipCompress input
  let byteStr := match String.fromUTF8? compressed with
    | some s => s
    | none => String.ofList (compressed.toList.map (fun b => Char.ofNat b.toNat))
  let _ ← MonadConsole.printStr byteStr
  MonadProcess.exitProcess 0

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Pure canonical compression trace with process exit. -/
def canonicalCompressTrace : List AnyEvent :=
  runModelTrace (gzipSpec : TraceM AnyEvent Unit)

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- High-level behavioral specification for Spike 5 decompression run: emits decompressed byte stream to standard output. -/
def gunzipSpec [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  let byteStr := match String.fromUTF8? canonicalSampleData with
    | some s => s
    | none => String.ofList (canonicalSampleData.toList.map (fun b => Char.ofNat b.toNat))
  let _ ← MonadConsole.printStr byteStr
  MonadProcess.exitProcess 0

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- High-level dynamic behavioral specification for GUNZIP stream decompression over arbitrary stdin input. -/
def gunzipStreamSpec (input : ByteArray) [Monad m] [MonadConsole m] [MonadProcess m] : m Unit := do
  match gzipDecompress input with
  | Except.ok uncompressed =>
    let byteStr := match String.fromUTF8? uncompressed with
      | some s => s
      | none => String.ofList (uncompressed.toList.map (fun b => Char.ofNat b.toNat))
    let _ ← MonadConsole.printStr byteStr
    MonadProcess.exitProcess 0
  | Except.error _ =>
    MonadProcess.exitProcess 1

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Pure canonical decompression trace with process exit. -/
def canonicalDecompressTrace : List AnyEvent :=
  runModelTrace (gunzipSpec : TraceM AnyEvent Unit)

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Dynamic high-level model trace for GZIP compression over arbitrary input. -/
def gzipParametricModelTrace (input : ByteArray) : List AnyEvent :=
  runModelTrace (gzipStreamSpec input : TraceM AnyEvent Unit)

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
/-- Dynamic high-level model trace for GUNZIP decompression over arbitrary input. -/
def gunzipParametricModelTrace (input : ByteArray) : List AnyEvent :=
  runModelTrace (gunzipStreamSpec input : TraceM AnyEvent Unit)

end Spikes.Spike5Gzip


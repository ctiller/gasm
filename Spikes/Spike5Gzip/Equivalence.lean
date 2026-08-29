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

import Spikes.Spike5Gzip.NativeProofs

namespace Spikes.Spike5Gzip

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.WASI

set_option maxRecDepth 100000

/- Spike 5 has one proof authority: the universal `VerifiedProgram`.  These
   names are target/direction projections of the reusable streaming
   certificates in `Runtime` and `NativeProofs`; there is no sample-only or
   target-specific verified-program record. -/
def spike5WindowsVerifiedProgram := windowsStreamingVerifiedProgram .compress
def spike5GunzipWindowsVerifiedProgram := windowsStreamingVerifiedProgram .decompress
def spike5LinuxVerifiedProgram := linuxStreamingVerifiedProgram .compress
def spike5GunzipLinuxVerifiedProgram := linuxStreamingVerifiedProgram .decompress
def spike5WasmVerifiedProgram := wasiStreamingVerifiedProgram .compress
def spike5GunzipWasmVerifiedProgram := wasiStreamingVerifiedProgram .decompress

/- REF: docs/SPIKES/SPIKE5_GZIP.md#5-semantic-trace-equivalence-verification-contract -/
theorem spike5_windows_gzip_trace_equivalence (environment : Environment) :
    Platform.run
      ((windowsStreamingCapabilities .compress).realize (windowsStreamArtifact .compress)
        (windowsStreamEntry .compress environment))
      (windowsStreamArtifact .compress)
      (Platform.load (P := WindowsX86_64 AnyEvent) (windowsStreamArtifact .compress) environment) =
        streamingInvocationTrace .compress spike5AllocationScope environment.stdin :=
  windows_streaming_trace_equivalence .compress environment

theorem spike5_windows_gunzip_trace_equivalence (environment : Environment) :
    Platform.run
      ((windowsStreamingCapabilities .decompress).realize (windowsStreamArtifact .decompress)
        (windowsStreamEntry .decompress environment))
      (windowsStreamArtifact .decompress)
      (Platform.load (P := WindowsX86_64 AnyEvent) (windowsStreamArtifact .decompress) environment) =
        streamingInvocationTrace .decompress spike5AllocationScope environment.stdin :=
  windows_streaming_trace_equivalence .decompress environment

theorem spike5_linux_gzip_trace_equivalence (environment : Environment) :
    Platform.run
      ((linuxStreamingCapabilities .compress).realize (linuxStreamArtifact .compress)
        (linuxStreamEntry .compress environment))
      (linuxStreamArtifact .compress)
      (Platform.load (P := LinuxX86_64 AnyEvent) (linuxStreamArtifact .compress) environment) =
        streamingInvocationTrace .compress spike5AllocationScope environment.stdin :=
  linux_streaming_trace_equivalence .compress environment

theorem spike5_linux_gunzip_trace_equivalence (environment : Environment) :
    Platform.run
      ((linuxStreamingCapabilities .decompress).realize (linuxStreamArtifact .decompress)
        (linuxStreamEntry .decompress environment))
      (linuxStreamArtifact .decompress)
      (Platform.load (P := LinuxX86_64 AnyEvent) (linuxStreamArtifact .decompress) environment) =
        streamingInvocationTrace .decompress spike5AllocationScope environment.stdin :=
  linux_streaming_trace_equivalence .decompress environment

theorem spike5_wasm_gzip_trace_equivalence (environment : Environment) :
    Platform.run (P := WasiPlatform)
      (wasiStreamingHost (wasiStreamingEntryContext .compress environment))
      (wasiStreamArtifact .compress) environment = wasiStreamingSpec .compress environment :=
  wasi_streaming_trace_equivalence .compress environment

theorem spike5_wasm_gunzip_trace_equivalence (environment : Environment) :
    Platform.run (P := WasiPlatform)
      (wasiStreamingHost (wasiStreamingEntryContext .decompress environment))
      (wasiStreamArtifact .decompress) environment = wasiStreamingSpec .decompress environment :=
  wasi_streaming_trace_equivalence .decompress environment

end Spikes.Spike5Gzip

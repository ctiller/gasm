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
import Gasm.Targets.Linux.Linker
import Gasm.Targets.Windows.Win32API
import Gasm.Targets.WASI.ABI
import Stdlib.Zlib.ContainerRoundtrip
import Spikes.Spike5Gzip.Spec
import Spikes.Spike5Gzip.Windows.Program
import Spikes.Spike5Gzip.Linux.Program
import Spikes.Spike5Gzip.Wasm.Program

/-!
The first universal-input boundary for Spike 5.

The old Spike 5 contracts selected `canonicalSampleData` through a one-element
operation type.  That does not describe a CLI program: its input is the byte
stream supplied by the external environment.  This module names that boundary,
records the concrete target injection points, and connects the resulting
arbitrary byte stream to the library's universal GZIP container theorem.

It intentionally does *not* assert machine-code trace equivalence.  The current
target artifacts still embed the canonical stream and therefore do not yet read
stdin.  A future `VerifiedProgram` migration must change the target programs to
consume these injection points and prove the corresponding trace theorem.
-/

namespace Spikes.Spike5Gzip

open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.Windows
open Gasm.Targets.Linux
open Gasm.Targets.WASI
open Stdlib.Zlib

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The logical byte stream presented to Spike 5 is exactly `Environment.stdin`.
    This is deliberately not `canonicalSampleData`: every byte array is in the
    input domain of a CLI compression invocation. -/
def gzipInput (env : Environment) : ByteArray :=
  env.stdin

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- The compression model trace under the canonical external environment. -/
def gzipEnvironmentTrace (env : Environment) : List AnyEvent :=
  gzipParametricModelTrace (gzipInput env)

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- The decompression model trace under the canonical external environment. -/
def gunzipEnvironmentTrace (env : Environment) : List AnyEvent :=
  gunzipParametricModelTrace (gzipInput env)

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Windows's concrete Spike 5 input injection point.  `ReadFile` consumes this
    state's `stdinBuffer`; target-level proofs must start from this state. -/
def spike5WindowsInitialState (env : Environment) :=
  Windows.spike5Executable.loadWithStdin (gzipInput env)

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Linux's concrete Spike 5 input injection point.  `read(2)` consumes this
    state's `stdinBuffer`; target-level proofs must start from this state. -/
def spike5LinuxInitialState (env : Environment) :=
  Linux.spike5Executable.loadWithStdin (gzipInput env)

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- WASI's concrete Spike 5 input injection point.  `fd_read` consumes the first
    component and networking imports consume the request queue. -/
def spike5WasiInitialInput (env : Environment) : ByteArray × List String :=
  (gzipInput env, env.incomingRequests)

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The target loaders preserve the arbitrary stdin bytes selected by the
    canonical environment.  These equalities expose the exact state component a
    machine refinement proof has to relate to the source-level byte stream. -/
theorem spike5_windows_stdin_injection (env : Environment) :
    (spike5WindowsInitialState env).stdinBuffer = gzipInput env := by
  rfl

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
theorem spike5_linux_stdin_injection (env : Environment) :
    (spike5LinuxInitialState env).stdinBuffer = gzipInput env := by
  rfl

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
theorem spike5_wasi_stdin_injection (env : Environment) :
    (spike5WasiInitialInput env).1 = gzipInput env := by
  rfl

/- REF: docs/STDLIB_ZLIB.md#52-gzip-format-rfc-1952 -/
/-- Reusable arbitrary-input container theorem at Spike 5's environment boundary.
    It is a direct kernel-checked specialization of the Stdlib GZIP theorem and
    covers empty, malformed-as-source, and all other byte streams uniformly. -/
theorem gzip_environment_roundtrip_soundness (env : Environment) :
    decompressData (compressData (gzipInput env)) = .ok (gzipInput env) := by
  exact gzip_roundtrip_soundness (gzipInput env)

end Spikes.Spike5Gzip

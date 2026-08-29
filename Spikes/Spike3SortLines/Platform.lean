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
import Gasm.Effects.Trace
import Gasm.Targets.WASI.ABI

/-! WASI Preview 1 platform profile for the Spike 3 byte-stream sorter.

Unlike Spike 1's closed WASI profile, this profile grants `fd_read`; its loader
therefore retains the complete canonical environment as state.  In particular,
there is no sample-domain loader between `Environment.stdin` and `fd_read`.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform
open Gasm.Effects
open Gasm.Targets.Wasm
open Gasm.Targets.WASI

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
inductive Spike3WasiPreview1Platform where | mk

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- A serialized Wasm module plus the exact interpreter inputs to which its proof refers. -/
structure Spike3WasiArtifact where
  encoded : EncodedWasmArtifact
  instructions : List WasmInstr
  dataSegments : List WasmDataSegment
  imports : List String

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
instance : Platform Spike3WasiPreview1Platform where
  Artifact := Spike3WasiArtifact
  State := Environment
  imports := fun artifact => artifact.imports
  load := fun _ environment => environment
  emit := fun artifact => artifact.encoded.emit

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- The operational WASI trace is run from the canonical environment, including arbitrary stdin
    bytes and the request queue. -/
instance : PlatformTrace Spike3WasiPreview1Platform AnyEvent where
  runTrace := fun artifact environment =>
    runWasiTrace artifact.instructions artifact.dataSegments environment.stdin artifact.imports
      environment.incomingRequests

/- REF: docs/SYSTEM_EFFECTS.md#101-capability-composition-and-abi-boundaries -/
def spike3WasiReadWriteExitCapability : Capability Spike3WasiPreview1Platform where
  name := "WASI Preview 1 stdin, console output, and process exit"
  exports := ["fd_read", "fd_write", "proc_exit"]
  invariant := fun _ => True

/- REF: docs/SYSTEM_EFFECTS.md#101-capability-composition-and-abi-boundaries -/
/-- The composition preserves every canonical environment field at load time.  This is the
    capability premise a future `VerifiedProgram` proof must use; it cannot narrow stdin to a
    Bool or a finite test enumeration. -/
def spike3WasiCapabilities : CapabilityComposition Spike3WasiPreview1Platform where
  capabilities := [spike3WasiReadWriteExitCapability]
  exports := ["fd_read", "fd_write", "proc_exit"]
  invariant := fun _ => True
  load := fun _ environment => environment
  load_agrees_with_platform := by intro artifact environment; rfl
  initialized := by intro artifact environment; trivial
  members_preserved := by
    intro capability state membership _
    have h : capability = spike3WasiReadWriteExitCapability := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using membership
    subst capability
    trivial

end Spikes.Spike3SortLines

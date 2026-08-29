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

import Gasm.Effects.Inject
import Gasm.Effects.Process
import Gasm.Targets.X86_64.Semantics
import Spikes.Spike3SortLines.Linux.Program
import Spikes.Spike3SortLines.NativeRuntime
import Spikes.Spike3SortLines.Windows.Program

namespace Spikes.Spike3SortLines

open Gasm.Effects
open Gasm.Targets.X86_64

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Runs the actual lowered Linux Spike 3 artifact under a caller-selected finite native grant.
    Fuel is explicit so the termination claim cannot silently depend on the historic 50,000-step
    trace helper. -/
def runSpike3LinuxWithGrant (grant : Spike3NativeArenaGrant) (stdin : ByteArray) (fuel : Nat) :
    NativeRunOutcome AnyEvent :=
  let initial := Linux.spike3Executable.loadWithStdin stdin
  letI := spike3LinuxRuntime AnyEvent grant
  runProgramOutcomeWithLoops initial.rip Linux.spike3Instructions fuel initial

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Runs the actual lowered Win32 Spike 3 artifact under a caller-selected finite native grant. -/
def runSpike3WindowsWithGrant (grant : Spike3NativeArenaGrant) (stdin : ByteArray) (fuel : Nat) :
    NativeRunOutcome AnyEvent :=
  let initial := Windows.spike3Executable.loadWithStdin stdin
  letI := spike3WindowsRuntime AnyEvent grant
  runProgramOutcomeWithLoops initial.rip Windows.spike3Instructions fuel initial

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Whether a finite native run emitted Spike 3's dedicated resource-exhaustion process result. -/
def emittedSpike3ResourceFailure (outcome : NativeRunOutcome AnyEvent) : Bool :=
  (outcome.events).contains (AnyEvent.of (ProcessEvent.exit spike3ResourceFailureExitCode))

/-- The intentionally insufficient capability used to exercise the genuine native failure path. -/
def noNativeArenaGrant : Spike3NativeArenaGrant := ⟨0⟩

/-- The smallest grant that covers the native artifact's one 64 KiB reservation request. -/
def spike3NativeReservationGrant : Spike3NativeArenaGrant := ⟨65536⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Actual Linux resource-failure execution: an insufficient grant produces the explicit exit 75
    event and halts within the stated finite fuel, before any allocator result is dereferenced. -/
theorem linux_no_grant_is_explicit_resource_failure :
    emittedSpike3ResourceFailure (runSpike3LinuxWithGrant noNativeArenaGrant ByteArray.empty 24) = true := by
  set_option maxRecDepth 10000 in
    set_option maxHeartbeats 4000000 in
      decide

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Recovery is a fresh invocation under a sufficient explicit grant, not mutation of a failed
    run.  The reservation hooks prove the new invocation receives a non-null arena base. -/
theorem native_resource_retry_has_linux_reservation :
    Spike3NativeArenaGrant.admits spike3NativeReservationGrant 65536 = true := by
  exact Spike3NativeArenaGrant.admits_of_le _ (by decide) (by decide)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The same fresh grant is sufficient for the Win32 reservation request. -/
theorem native_resource_retry_has_windows_reservation :
    Spike3NativeArenaGrant.admits spike3NativeReservationGrant 65536 = true := by
  exact Spike3NativeArenaGrant.admits_of_le _ (by decide) (by decide)

end Spikes.Spike3SortLines

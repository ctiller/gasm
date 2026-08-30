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

import Spikes.Spike3SortLines.NativeSpecification
import Spikes.Spike3SortLines.ReadBinderBridge

/-!
Win32-facing logical adapter for the shared classified Spike 3 specification.

It keeps exact context-indexed artifact selection and read-binder observation
outside the machine reachability proof, so neither abstract placement nor a
native evaluator can select a source success result by itself.
-/

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core.Platform

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The caller context determines the exact Win32 linked executable, including its reservation
immediate, independently of platform load placement. -/
theorem artifactForContext_executable (context : Spike3NativeExecutionContext) :
    (spike3WindowsArtifactForContext context).executable =
      spike3ExecutableWithArena context.arenaGrant.requestedBytes := rfl

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/- The instruction view is selected from the same context-indexed Win32 artifact. -/
set_option maxRecDepth 4096 in
theorem artifactForContext_instructions (context : Spike3NativeExecutionContext) :
    (spike3WindowsArtifactForContext context).instructions =
      spike3InstructionsWithArena context.arenaGrant.requestedBytes := rfl

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- The Win32 arena capability establishes only the exact caller-indexed artifact and platform
load state.  A caller must provide this evidence at the verified-program boundary. -/
theorem arenaCapability_establishes_iff (context : Spike3NativeExecutionContext)
    (environment : Environment)
    (state : Platform.State (Gasm.Core.Verification.WindowsX86_64 AnyEvent)) :
    (spike3WindowsArenaCapability AnyEvent).establishes
      (spike3WindowsArtifactForContext context) environment state context ↔
      state = Platform.load (P := Gasm.Core.Verification.WindowsX86_64 AnyEvent)
        (spike3WindowsArtifactForContext context) environment := by
  simp [spike3WindowsArenaCapability]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A Win32 execution certificate that establishes combined ready preparation and valid finite
reads obtains exactly the complete-output source arm for every finite environment input. -/
theorem chunkedOutcome_agrees_native_ready_accepted (context : Spike3NativeExecutionContext)
    (environment : Environment) {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence .windows context environment storageCapacity readCapacity chunks)
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
    (ready : nativePreparationOutcome evidence = .ready)
    (fits : (environmentInputLines environment).length ≤ storageCapacity) :
    boundedChunkedLineSortOutcome storageCapacity chunks .accepted =
      nativeSpike3Spec evidence .accepted := by
  rw [boundedChunkedLineSortOutcome_agrees_ready_accepted environment storageCapacity reads fits]
  unfold nativeSpike3Spec
  rw [ready]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Win32 output refusal remains an externally selected failure after ready preparation. -/
theorem chunkedOutcome_agrees_native_ready_refused (context : Spike3NativeExecutionContext)
    (environment : Environment) {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence .windows context environment storageCapacity readCapacity chunks)
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
    (ready : nativePreparationOutcome evidence = .ready)
    (fits : (environmentInputLines environment).length ≤ storageCapacity) :
    boundedChunkedLineSortOutcome storageCapacity chunks .refused =
      nativeSpike3Spec evidence .refused := by
  rw [boundedChunkedLineSortOutcome_agrees_ready_refused environment storageCapacity reads fits]
  unfold nativeSpike3Spec
  rw [ready]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A Win32 certificate of any combined preparation abort has only the explicit abort outcome,
not a successful event list or an output-refusal surrogate. -/
theorem nativeOutcome_of_exhausted_preparation (context : Spike3NativeExecutionContext)
    (environment : Environment) {storageCapacity readCapacity : Nat} {chunks : List (List UInt8)}
    (evidence : NativePreparationEvidence .windows context environment storageCapacity readCapacity chunks)
    (output : Spike3OutputOutcome)
    (exhausted : nativePreparationOutcome evidence = .exhausted) :
    nativeSpike3Spec evidence output = .preparationFailure :=
  nativeSpike3Spec_exhausted evidence output exhausted

end Spikes.Spike3SortLines.Windows

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
Linux-facing logical adapter for the shared classified Spike 3 specification.

This module binds the caller-selected arena grant to the exact Linux artifact
and turns an already-established read schedule into source outcomes.  Native
instruction/RIP reachability remains in a separate execution certificate.
-/

namespace Spikes.Spike3SortLines.Linux

open Gasm.Core.Platform

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The caller context determines the exact Linux linked executable, including its reservation
immediate.  This is deliberately independent of load placement and instruction reachability. -/
theorem artifactForContext_executable (context : Spike3NativeExecutionContext) :
    (spike3LinuxArtifactForContext context).executable =
      spike3ExecutableWithArena context.arenaGrant.requestedBytes := rfl

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/- The proof-side instruction view is selected from the same context-indexed Linux artifact. -/
set_option maxRecDepth 4096 in
theorem artifactForContext_instructions (context : Spike3NativeExecutionContext) :
    (spike3LinuxArtifactForContext context).instructions =
      spike3InstructionsWithArena context.arenaGrant.requestedBytes := rfl

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- At the call boundary, the Linux arena capability accepts exactly the context-indexed artifact
and platform load state; no no-grant default can establish this premise. -/
theorem arenaCapability_establishes_iff (context : Spike3NativeExecutionContext)
    (environment : Environment)
    (state : Platform.State (Gasm.Core.Verification.LinuxX86_64 AnyEvent)) :
    (spike3LinuxArenaCapability AnyEvent).establishes
      (spike3LinuxArtifactForContext context) environment state context ↔
      state = Platform.load (P := Gasm.Core.Verification.LinuxX86_64 AnyEvent)
        (spike3LinuxArtifactForContext context) environment := by
  simp [spike3LinuxArenaCapability]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A Linux execution certificate that establishes this ready grant and a valid finite read
schedule obtains exactly the complete-output source arm for every finite environment input. -/
theorem chunkedOutcome_agrees_native_ready_accepted (context : Spike3NativeExecutionContext)
    {lineCapacity : Nat} {evidenceLines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity evidenceLines)
    (environment : Environment) (storageCapacity : Nat) {readCapacity : Nat}
    {chunks : List (List UInt8)}
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
    (ready : nativePreparationOutcome evidence = .ready)
    (fits : (environmentInputLines environment).length ≤ storageCapacity) :
    boundedChunkedLineSortOutcome storageCapacity chunks .accepted =
      nativeSpike3Spec evidence environment .accepted := by
  rw [boundedChunkedLineSortOutcome_agrees_ready_accepted environment storageCapacity reads fits]
  unfold nativeSpike3Spec
  rw [ready]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Linux output refusal is a separate target-observable failure after a ready reservation. -/
theorem chunkedOutcome_agrees_native_ready_refused (context : Spike3NativeExecutionContext)
    {lineCapacity : Nat} {evidenceLines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity evidenceLines)
    (environment : Environment) (storageCapacity : Nat) {readCapacity : Nat}
    {chunks : List (List UInt8)}
    (reads : Gasm.Effects.ChunksOf environment.stdin.toList readCapacity chunks)
    (ready : nativePreparationOutcome evidence = .ready)
    (fits : (environmentInputLines environment).length ≤ storageCapacity) :
    boundedChunkedLineSortOutcome storageCapacity chunks .refused =
      nativeSpike3Spec evidence environment .refused := by
  rw [boundedChunkedLineSortOutcome_agrees_ready_refused environment storageCapacity reads fits]
  unfold nativeSpike3Spec
  rw [ready]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A Linux certificate of rejected reservation has only the explicit preparation-failure arm,
with no output trace or output-refusal classification. -/
theorem nativeOutcome_of_exhausted_reservation (context : Spike3NativeExecutionContext)
    {lineCapacity : Nat} {lines : List (List UInt8)}
    (evidence : NativePreparationEvidence context lineCapacity lines)
    (environment : Environment) (output : Spike3OutputOutcome)
    (exhausted : nativePreparationOutcome evidence = .exhausted) :
    nativeSpike3Spec evidence environment output = .preparationFailure :=
  nativeSpike3Spec_exhausted evidence environment output exhausted

end Spikes.Spike3SortLines.Linux

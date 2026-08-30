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

import Spikes.Spike3SortLines.NativeRuntime

/-!
Linux-facing logical adapter for the shared classified Spike 3 specification.

This module binds the caller-selected arena grant to the exact Linux artifact.
Preparation/outcome claims remain outside this adapter until a selected-artifact
execution refinement has projected its ordered allocator trace.
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

end Spikes.Spike3SortLines.Linux

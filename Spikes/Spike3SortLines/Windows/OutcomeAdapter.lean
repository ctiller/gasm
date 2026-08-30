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
Win32-facing logical adapter for the shared classified Spike 3 specification.

It keeps exact context-indexed artifact selection outside the machine
reachability proof.  Outcome claims are deliberately absent until a selected
artifact execution refinement projects the ordered allocator trace.
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

end Spikes.Spike3SortLines.Windows

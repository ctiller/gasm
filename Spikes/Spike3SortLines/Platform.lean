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

import Gasm.Targets.WASI.ABI

/-! WASI Preview 1 platform profile for the Spike 3 byte-stream sorter.

Unlike Spike 1's closed WASI profile, this profile grants `fd_read`; its loader
therefore retains the complete canonical environment as state.  In particular,
there is no sample-domain loader between `Environment.stdin` and `fd_read`.
-/

namespace Spikes.Spike3SortLines

open Gasm.Core.Platform
open Gasm.Targets.WASI

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
abbrev Spike3WasiPreview1Platform := WasiPlatform

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Spike 3 uses the repository's sole WASI artifact and execution profile. -/
abbrev Spike3WasiArtifact := WasiArtifact

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The composition preserves every canonical environment field at load time.  This is the
    capability premise a future `VerifiedProgram` proof must use; it cannot narrow stdin to a
    Bool or a finite test enumeration. -/
def spike3WasiProvider (index : Nat) : WasiProvider :=
  { protocol := .preview1
    imports := ["fd_read", "fd_write", "proc_exit"]
    importIndex := index }

def spike3WasiReadWriteExitCapability : Capability Spike3WasiPreview1Platform where
  Context := Unit
  providers := [0, 1, 2].map spike3WasiProvider
  establishes := fun _ _ _ _ => True

def spike3WasiCapabilities : CapabilityComposition Spike3WasiPreview1Platform where
  root := spike3WasiReadWriteExitCapability
  realize := fun _ => wasiHostCall
  realizeSupports := by
    intro context provider hprovider
    simp only [spike3WasiReadWriteExitCapability, List.mem_map] at hprovider
    rcases hprovider with ⟨index, hindex, rfl⟩
    intro state
    rfl

end Spikes.Spike3SortLines

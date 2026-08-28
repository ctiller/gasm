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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.CheckedAsm
import Stdlib.SmolAlloc.Program

/-
Stdlib/SmolAlloc/MemSafety.lean -- MH3's pathfinder acceptance evidence
(`docs/tasks/MH3-capability-authoring-surface.md`): the `MemSafe` soundness shape
(`docs/MEMORY_HOOK.md` #4.4) discharged for `Stdlib/SmolAlloc/Program.lean`'s
`freshAllocHeaderChecked` -- the real, shipped fresh-allocation header-initialization sequence of
`smol_malloc`, now authored through Layer A. Every declared access lands inside the 32-byte
`freshAllocFrame` region, proved directly from the four instructions' own step semantics and
`CheckedAsm.AccessOK.addresses_subset_granted`, the general bridge from a discharged obligation to
list-level footprint containment -- not merely carried as an unproved obligation.
-/

namespace Stdlib.SmolAlloc

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.CheckedAsm

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- `freshAllocFrame` is well-formed at any state whose `rax` leaves room for the 32-byte region:
    a single-region frame's `DisjointTokens` obligation is vacuous (no second region to collide
    with), so well-formedness reduces to the region's own `MemoryPerm` obligations. -/
theorem freshAllocFrame.wf {s : X86_64MachineState} (hroom : (s.gprs .rax).toNat + 32 ≤ 2 ^ 64) :
    Frame.WF freshAllocFrame s := by
  refine ⟨?_, ?_⟩
  · intro rs hrs
    simp only [freshAllocFrame, List.mem_singleton] at hrs
    subst hrs
    exact ⟨hroom, by decide⟩
  · intro i j hi hj hij
    simp [freshAllocFrame] at hi hj
    omega

/- REF: docs/MEMORY_HOOK.md#44-the-soundness-theorem-what-the-carried-proofs-mean -/
/-- MH3's pathfinder acceptance instance: `freshAllocHeaderChecked`'s `MemSafe` theorem, per
    `docs/MEMORY_HOOK.md` #4.4's shape. Every byte address the checked program's four stores touch
    (its `dynamicFootprint`) lies inside the 32-byte region `freshAllocFrame` grants at `rax`
    (its `grantedFootprint`). This is P2's "instruction-level obligation shape ... exercised on at
    least one real instruction family end-to-end," discharged for a real, shipped routine fragment
    (`Stdlib/SmolAlloc/Program.lean`'s `smol_malloc` fresh-allocation path) rather than a
    synthetic example. -/
theorem freshAllocHeaderMemSafe :
    MemSafeStatement freshAllocHeaderChecked (fun s₀ => (s₀.gprs .rax).toNat + 32 ≤ 2 ^ 64) := by
  intro s₀ hpre _hinv hwf a ha
  -- Register-file invariance across the four stores (`mov_mem64_disp_step_gprs`/
  -- `mov_mem64_disp_imm_step_gprs`) is what makes `rax` describe every access's address
  -- regardless of how many earlier stores have run; `simp`'s own iota/projection unfolding of
  -- each concrete `step` application already normalizes `ha`'s addresses down to `s₀`-relative
  -- form below, so those two lemmas are not separately invoked here (Lean's own reduction, not
  -- an assumption, is what discharges the invariance).
  have hok1 : AccessOK freshAllocFrame (fun _ : X86_64MachineState => True)
      ⟨.store, .w64, ⟨some .rax, none, signExtend8To64 (0x00 : UInt8)⟩⟩ := by mem_bounds
  have hok2 : AccessOK freshAllocFrame (fun _ : X86_64MachineState => True)
      ⟨.store, .w64, ⟨some .rax, none, signExtend8To64 (0x08 : UInt8)⟩⟩ := by mem_bounds
  have hok3 : AccessOK freshAllocFrame (fun _ : X86_64MachineState => True)
      ⟨.store, .w64, ⟨some .rax, none, signExtend8To64 (0x10 : UInt8)⟩⟩ := by mem_bounds
  have hok4 : AccessOK freshAllocFrame (fun _ : X86_64MachineState => True)
      ⟨.store, .w64, ⟨some .rax, none, signExtend8To64 (0x18 : UInt8)⟩⟩ := by mem_bounds
  simp only [freshAllocHeaderChecked, storeReg64, storeImm64, CheckedProgram.dynamicFootprint,
    List.foldl, X86_64Instruction.memAccesses, List.flatMap, List.nil_append,
    List.mem_append] at ha
  rcases ha with (((ha | ha) | ha) | ha)
  · exact hok1.addresses_subset_granted trivial hwf a ha
  · exact hok2.addresses_subset_granted trivial hwf a ha
  · exact hok3.addresses_subset_granted trivial hwf a ha
  · exact hok4.addresses_subset_granted trivial hwf a ha

end Stdlib.SmolAlloc

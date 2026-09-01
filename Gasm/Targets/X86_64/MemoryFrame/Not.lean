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
import Gasm.Targets.X86_64.MemoryFrame.Common
import Gasm.Targets.X86_64.Instructions.Not

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- NOT is register-only (`memAccesses _ := []`): see MemoryFrame/Add.lean's header comment for the
-- batch-lemma-instantiation rationale (identical here).

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR64.writesWithin (i : NotR64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR64.readsWithin (i : NotR64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hrip, hgprs, hflags, hstdin,
        hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR32.writesWithin (i : NotR32) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR32.readsWithin (i : NotR32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR16.writesWithin (i : NotR16) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR16.readsWithin (i : NotR16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR8.writesWithin (i : NotR8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem NotR8.readsWithin (i : NotR8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end Gasm.Targets.X86_64.MemoryFrame

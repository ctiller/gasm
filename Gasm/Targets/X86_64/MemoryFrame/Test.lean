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
import Gasm.Targets.X86_64.Instructions.Test

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- TEST is register-only (`memAccesses _ := []` for both forms): see MemoryFrame/Add.lean's header
-- comment for the batch-lemma-instantiation rationale (identical here).

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR64R64.writesWithin (i : TestR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setFlagsLogic64,
      X86_64MachineState.setFlagsLogic] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR64R64.readsWithin (i : TestR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setFlagsLogic64,
        X86_64MachineState.setFlagsLogic, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR64Imm32.writesWithin (i : TestR64Imm32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setFlagsLogic64,
      X86_64MachineState.setFlagsLogic] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR64Imm32.readsWithin (i : TestR64Imm32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setFlagsLogic64,
        X86_64MachineState.setFlagsLogic, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR32R32.writesWithin (i : TestR32R32) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR32R32.readsWithin (i : TestR32R32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR32Imm32.writesWithin (i : TestR32Imm32) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR32Imm32.readsWithin (i : TestR32Imm32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR16R16.writesWithin (i : TestR16R16) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR16R16.readsWithin (i : TestR16R16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR16Imm16.writesWithin (i : TestR16Imm16) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR16Imm16.readsWithin (i : TestR16Imm16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR8R8.writesWithin (i : TestR8R8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR8R8.readsWithin (i : TestR8R8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR8Imm8.writesWithin (i : TestR8Imm8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem TestR8Imm8.readsWithin (i : TestR8Imm8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end Gasm.Targets.X86_64.MemoryFrame

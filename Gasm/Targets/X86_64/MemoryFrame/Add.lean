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
import Gasm.Targets.X86_64.Instructions.Add

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- ADD is register-only (`memAccesses _ := []` for all 5 forms): each pair below instantiates the
-- shared batch lemma (`registerOnly_writesWithin`/`registerOnly_readsWithin`,
-- MemoryFrame/Common.lean) instead of re-deriving a bespoke connection proof, since `step` never
-- reads or writes `.memory` for these forms -- part of docs/MEMORY_HOOK.md §3.3's "74
-- register-only" batch that MH1 built the shared lemma for but did not instantiate.

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR64R64.writesWithin (i : AddR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
      X86_64MachineState.setFlagsAdd64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR64R64.readsWithin (i : AddR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        X86_64MachineState.setFlagsAdd64, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR64Imm8.writesWithin (i : AddR64Imm8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
      X86_64MachineState.setFlagsAdd64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR64Imm8.readsWithin (i : AddR64Imm8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        X86_64MachineState.setFlagsAdd64, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddRspImm8.writesWithin (i : AddRspImm8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
      X86_64MachineState.setFlagsAdd64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddRspImm8.readsWithin (i : AddRspImm8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        X86_64MachineState.setFlagsAdd64, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddRspImm32.writesWithin (i : AddRspImm32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
      X86_64MachineState.setFlagsAdd64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddRspImm32.readsWithin (i : AddRspImm32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        X86_64MachineState.setFlagsAdd64, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR64Imm32.writesWithin (i : AddR64Imm32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
      X86_64MachineState.setFlagsAdd64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR64Imm32.readsWithin (i : AddR64Imm32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        X86_64MachineState.setFlagsAdd64, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR32R32.writesWithin (i : AddR32R32) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR32R32.readsWithin (i : AddR32R32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR32Imm8.writesWithin (i : AddR32Imm8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR32Imm8.readsWithin (i : AddR32Imm8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR32Imm32.writesWithin (i : AddR32Imm32) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR32Imm32.readsWithin (i : AddR32Imm32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR16R16.writesWithin (i : AddR16R16) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR16R16.readsWithin (i : AddR16R16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR16Imm8.writesWithin (i : AddR16Imm8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR16Imm8.readsWithin (i : AddR16Imm8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR16Imm16.writesWithin (i : AddR16Imm16) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR16Imm16.readsWithin (i : AddR16Imm16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR8R8.writesWithin (i : AddR8R8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR8R8.readsWithin (i : AddR8R8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR8Imm8.writesWithin (i : AddR8Imm8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem AddR8Imm8.readsWithin (i : AddR8Imm8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end Gasm.Targets.X86_64.MemoryFrame

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
import Gasm.Targets.X86_64.Instructions.Div

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- DIV/IDIV/MUL is register-only (`memAccesses _ := []`): see MemoryFrame/Add.lean's header comment for the
-- batch-lemma-instantiation rationale (identical here). `step`'s divide-by-zero and
-- quotient-overflow branches each still leave `.memory` untouched -- the `(try split)` chain
-- discharges those branches for `writesWithin`.
--
-- For `readsWithin`, `agreeOutsideMemory_eq` bridges `agreeOutsideMemory s1 s2` to an exact state
-- update `s1 = { s2 with memory := s1.memory }`, equating all non-memory operands between pre-states
-- so `(try split)` splits the `step` branching conditions identically on both sides and closes
-- by reflexivity.

theorem agreeOutsideMemory_eq (s1 s2 : X86_64MachineState) (h : agreeOutsideMemory s1 s2) :
    s1 = { s2 with memory := s1.memory } := by
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := h
  cases s1; cases s2
  dsimp at hrip hgprs hflags hstdin hreq hfault
  subst hrip hgprs hflags hstdin hreq hfault
  rfl

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR64.writesWithin (i : DivR64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR64.readsWithin (i : DivR64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR32.writesWithin (i : DivR32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr32] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR32.readsWithin (i : DivR32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr32,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR16.writesWithin (i : DivR16) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr16] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR16.readsWithin (i : DivR16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr16, X86_64MachineState.setGpr64,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR8.writesWithin (i : DivR8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr16] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem DivR8.readsWithin (i : DivR8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr16, X86_64MachineState.setGpr64,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem IdivR64.writesWithin (i : IdivR64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem IdivR64.readsWithin (i : IdivR64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem IdivR32.writesWithin (i : IdivR32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr32] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem IdivR32.readsWithin (i : IdivR32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr32,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem IdivR16.writesWithin (i : IdivR16) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr16] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
set_option maxHeartbeats 1000000 in
theorem IdivR16.readsWithin (i : IdivR16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr16, X86_64MachineState.setGpr64,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem IdivR8.writesWithin (i : IdivR8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr16] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
set_option maxHeartbeats 1000000 in
theorem IdivR8.readsWithin (i : IdivR8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr16, X86_64MachineState.setGpr64,
        hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))




/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR64.writesWithin (i : MulR64) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR64.readsWithin (i : MulR64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR32.writesWithin (i : MulR32) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR32.readsWithin (i : MulR32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR16.writesWithin (i : MulR16) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR16.readsWithin (i : MulR16) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR8.writesWithin (i : MulR8) : WritesWithin i :=
  registerOnly_writesWithin i (fun _ => rfl)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem MulR8.readsWithin (i : MulR8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    cases s1; cases s2
    subst hrip hgprs hflags hstdin hreq hfault
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end Gasm.Targets.X86_64.MemoryFrame

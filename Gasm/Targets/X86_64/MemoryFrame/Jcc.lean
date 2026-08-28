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
import Gasm.Targets.X86_64.Instructions.Jcc

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- JMP/Jcc are register-only (`memAccesses _ := []` for all 19 forms): see MemoryFrame/Add.lean's
-- header comment for the batch-lemma-instantiation rationale (identical here), and
-- MemoryFrame/Cmov.lean's header comment for why the flags readers (`zf`/`sf`/`cf`/`of_`) are
-- deliberately left un-unfolded for `writesWithin` (bare `split` handles them) but aligned via
-- `hzf`/`hsf`/`hcf`/`hof` before splitting for `readsWithin` (so the two states' branch conditions
-- become one shared term instead of two syntactically different ones). Unlike CMOVcc, every
-- Jcc/JMP branch only selects between two *target RIP values*, not two whole states, so the
-- `.gprs`/`.flags`/... conjuncts never need splitting at all -- only `.rip` does.

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JmpRel8.writesWithin (i : JmpRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JmpRel8.readsWithin (i : JmpRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JmpRel32.writesWithin (i : JmpRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JmpRel32.readsWithin (i : JmpRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JeRel8.writesWithin (i : JeRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JeRel8.readsWithin (i : JeRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JeRel32.writesWithin (i : JeRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JeRel32.readsWithin (i : JeRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JneRel8.writesWithin (i : JneRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JneRel8.readsWithin (i : JneRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JneRel32.writesWithin (i : JneRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JneRel32.readsWithin (i : JneRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JlRel8.writesWithin (i : JlRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JlRel8.readsWithin (i : JlRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hsf, hof, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JleRel8.writesWithin (i : JleRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JleRel8.readsWithin (i : JleRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hsf, hof, hrip, hgprs, hflags, hstdin, hreq,
        hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JgRel8.writesWithin (i : JgRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JgRel8.readsWithin (i : JgRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hsf, hof, hrip, hgprs, hflags, hstdin, hreq,
        hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JgeRel8.writesWithin (i : JgeRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JgeRel8.readsWithin (i : JgeRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hsf, hof, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JgeRel32.writesWithin (i : JgeRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JgeRel32.readsWithin (i : JgeRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hsf, hof, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JbRel8.writesWithin (i : JbRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JbRel8.readsWithin (i : JbRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaeRel8.writesWithin (i : JaeRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaeRel8.readsWithin (i : JaeRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaeRel32.writesWithin (i : JaeRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaeRel32.readsWithin (i : JaeRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaRel8.writesWithin (i : JaRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaRel8.readsWithin (i : JaRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JbeRel8.writesWithin (i : JbeRel8) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JbeRel8.readsWithin (i : JbeRel8) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JleRel32.writesWithin (i : JleRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JleRel32.readsWithin (i : JleRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hsf, hof, hrip, hgprs, hflags, hstdin, hreq,
        hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JbRel32.writesWithin (i : JbRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JbRel32.readsWithin (i : JbRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaRel32.writesWithin (i : JaRel32) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem JaRel32.readsWithin (i : JaRel32) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, hzf, hcf, hrip, hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

end Gasm.Targets.X86_64.MemoryFrame

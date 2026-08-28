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
import Gasm.Targets.X86_64.Instructions.Cmov

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

-- CMOVcc is register-only (`memAccesses _ := []` for all 8 forms): see MemoryFrame/Add.lean's
-- header comment for the batch-lemma-instantiation rationale (identical here). `step` branches on
-- the pre-step flags (via `zf`/`sf`/`cf`/`of_`) to decide whether to copy `src` into `dst`; every
-- branch leaves `.memory` untouched.
--
-- `writesWithin` splits directly on the opaque `s.zf`/`s.sf`/`s.cf`/`s.of_` condition (a single
-- state, no cross-state alignment needed) -- `split` handles a bare `Bool`-valued condition like
-- `s.zf` cleanly, but fails to recognize it once unfolded into its `(s.flags &&& mask) != 0 = true`
-- shape, so these readers are deliberately left un-unfolded here.
--
-- `readsWithin` needs the two states' conditions (`s1.zf` vs `s2.zf`) aligned into one shared term
-- before splitting; `hzf`/`hsf`/`hcf`/`hof` do that via `hflags` without unfolding `zf` itself (for
-- the same reason `writesWithin` leaves it folded), so `split` still sees a plain opaque condition
-- after the rewrite. The `else` branch of CMOVcc's `step` is the pre-step state itself (unchanged),
-- so that branch's goal is closed by `assumption` (it's literally one of `hgprs`/`hflags`/...)
-- rather than by `rfl`.

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmoveR64R64.writesWithin (i : CmoveR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmoveR64R64.readsWithin (i : CmoveR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovneR64R64.writesWithin (i : CmovneR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovneR64R64.readsWithin (i : CmovneR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovlR64R64.writesWithin (i : CmovlR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovlR64R64.readsWithin (i : CmovlR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovleR64R64.writesWithin (i : CmovleR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovleR64R64.readsWithin (i : CmovleR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovgR64R64.writesWithin (i : CmovgR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovgR64R64.readsWithin (i : CmovgR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovgeR64R64.writesWithin (i : CmovgeR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovgeR64R64.readsWithin (i : CmovgeR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovbR64R64.writesWithin (i : CmovbR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovbR64R64.readsWithin (i : CmovbR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovaeR64R64.writesWithin (i : CmovaeR64R64) : WritesWithin i :=
  registerOnly_writesWithin i (fun s => by
    simp only [X86_64Instruction.step, X86_64MachineState.setGpr64] <;>
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
theorem CmovaeR64R64.readsWithin (i : CmovaeR64R64) : ReadsWithin i :=
  registerOnly_readsWithin i (by
    intro s1 s2 hout
    obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
    have hzf : s1.zf = s2.zf := by simp [X86_64MachineState.zf, hflags]
    have hsf : s1.sf = s2.sf := by simp [X86_64MachineState.sf, hflags]
    have hcf : s1.cf = s2.cf := by simp [X86_64MachineState.cf, hflags]
    have hof : s1.of_ = s2.of_ := by simp [X86_64MachineState.of_, hflags]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [X86_64Instruction.step, X86_64MachineState.setGpr64, hzf, hsf, hcf, hof, hrip,
        hgprs, hflags, hstdin, hreq, hfault] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> (first | rfl | assumption))

end Gasm.Targets.X86_64.MemoryFrame

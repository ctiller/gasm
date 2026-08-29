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
import Gasm.Targets.X86_64.Memory
import Gasm.Targets.X86_64.Instructions.Base

-- Mirrors the `RoundtripGate/*.lean` shard convention (`docs/MEMORY_HOOK.md` §3.3): this file
-- hosts the per-family connection-obligation SHAPE and the shared register-only batch lemma;
-- `MemoryFrame/<Family>.lean` shards host the 14 real memory forms' concrete `writesWithin`/
-- `readsWithin` instances. It cannot live in `Memory.lean` itself: `WritesWithin`/`ReadsWithin`
-- quantify over `X86_64Instruction.step`/`memAccesses`, and that typeclass (declared in
-- `Instructions/Base.lean`) already imports `Memory.lean` for the `memAccesses` field's type --
-- importing back would cycle.

namespace Gasm.Targets.X86_64.MemoryFrame

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Per-family connection obligation (Law 12): `step` never writes outside its declared store
    footprint. -/
def WritesWithin {ι : Type} [X86_64Instruction ι] (i : ι) : Prop :=
  ∀ (s : X86_64MachineState) (a : Address),
    a ∉ storeFootprint (X86_64Instruction.memAccesses i) s →
    X86_64Mem.read .w8 a (X86_64Instruction.step i s).memory = X86_64Mem.read .w8 a s.memory

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The bytes `step` writes into its declared store footprint agree between two pre-states -- the
    second half of `ReadsWithin` below.

    This conjunct exists because without it `ReadsWithin` is unsound as a read-frame condition.
    Its original form concluded only `agreeOutsideMemory (step s1) (step s2)`, which says nothing
    about the resulting MEMORY; an instruction could therefore load from a completely undeclared
    address and store the loaded value, and still satisfy the obligation, because the illicitly
    read bytes land in memory where the conclusion never looks. That is not hypothetical: it is
    `MemoryFrame/NegativeControl.lean`'s `evilMemMem_readsWithin_oldForm`, and adding this
    conjunct is exactly what makes the same instruction's `ReadsWithin` refutable
    (`evilMemMem_not_readsWithin` there). Found by adversarial review, 2026-08-28. -/
def StoreAgreeOn {ι : Type} [X86_64Instruction ι] (i : ι) (s1 s2 : X86_64MachineState) : Prop :=
  ∀ a ∈ storeFootprint (X86_64Instruction.memAccesses i) s1,
    X86_64Mem.read .w8 a (X86_64Instruction.step i s1).memory =
      X86_64Mem.read .w8 a (X86_64Instruction.step i s2).memory

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Per-family connection obligation (Law 12): `step`'s result depends on memory only through its
    declared load footprint -- two pre-states agreeing everywhere but memory, and agreeing on the
    declared load footprint's bytes, step to states agreeing everywhere but memory AND writing
    identical bytes into the declared store footprint (`StoreAgreeOn`, whose docstring explains
    why the second conjunct is required for soundness).

    Together with `WritesWithin` (nothing outside the store footprint changes at all) this pins
    the whole post-state: everything outside the store footprint is untouched, and everything
    inside it is a function of the pre-state's non-memory fields plus the declared load
    footprint. Neither half is redundant -- `WritesWithin` bounds *where* `step` writes,
    `ReadsWithin` bounds *what the written bytes may depend on*. -/
def ReadsWithin {ι : Type} [X86_64Instruction ι] (i : ι) : Prop :=
  ∀ (s1 s2 : X86_64MachineState),
    agreeOutsideMemory s1 s2 →
    agreeOn (loadFootprint (X86_64Instruction.memAccesses i) s1) s1.memory s2.memory →
    agreeOutsideMemory (X86_64Instruction.step i s1) (X86_64Instruction.step i s2) ∧
      StoreAgreeOn i s1 s2

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The shared batch lemma covering every `memAccesses _ := []` (register-only) form
    (`docs/MEMORY_HOOK.md`'s "one shared batch lemma covering the `[]` forms"):
    if `step` never changes the memory field at all, `WritesWithin` holds vacuously against the
    empty footprint. Reduces each of the 74 register-only forms' proof obligation to the single,
    `rfl`-discharged fact that their `step` doesn't touch `.memory` (true by construction: none of
    their `step` bodies mention it), rather than needing a bespoke connection-theorem proof per
    type. -/
theorem registerOnly_writesWithin {ι : Type} [X86_64Instruction ι] (i : ι)
    (hNoMem : ∀ s : X86_64MachineState, (X86_64Instruction.step i s).memory = s.memory) :
    WritesWithin i := by
  intro s a _
  rw [hNoMem]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The `ReadsWithin` half of the register-only batch lemma: if `step` commutes with
    `agreeOutsideMemory` unconditionally (true for every register-only form, since their `step`
    bodies read only `gprs`/`rip`/`flags`, never `.memory`), the empty load footprint's hypothesis
    is simply unused.

    `hEmpty` carries the register-only forms' defining property (`memAccesses _ := []`) and is an
    AUTO-PARAM defaulted to `by rfl`, not an extra explicit argument. That is deliberate: when
    `ReadsWithin` gained its `StoreAgreeOn` conjunct, the conjunct is vacuous for these forms
    (an empty `memAccesses` gives an empty `storeFootprint`, so the `∀ a ∈ ...` has no
    instances) -- but the batch lemma still needs to *know* the list is empty to discharge it.
    Defaulting it keeps every existing `registerOnly_readsWithin i hCongr` call site compiling
    unchanged rather than requiring a mechanical edit across all the register-only shards. -/
theorem registerOnly_readsWithin {ι : Type} [X86_64Instruction ι] (i : ι)
    (hCongr : ∀ s1 s2 : X86_64MachineState, agreeOutsideMemory s1 s2 →
      agreeOutsideMemory (X86_64Instruction.step i s1) (X86_64Instruction.step i s2))
    (hEmpty : X86_64Instruction.memAccesses i = [] := by rfl) :
    ReadsWithin i := by
  intro s1 s2 hout _
  refine ⟨hCongr s1 s2 hout, ?_⟩
  intro a ha
  simp [storeFootprint, footprintFor, hEmpty] at ha

end Gasm.Targets.X86_64.MemoryFrame

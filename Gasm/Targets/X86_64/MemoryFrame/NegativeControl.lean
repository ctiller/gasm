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

/-
Gasm/Targets/X86_64/MemoryFrame/NegativeControl.lean -- the frame conditions' mutation tests.

`MemoryFrame/<Family>.lean` proves `WritesWithin`/`ReadsWithin` for every real instruction form.
Those are positive results: they show the obligations are SATISFIABLE. They cannot show the
obligations are non-vacuous -- a frame condition that everything satisfies constrains nothing,
and `ReadsWithin` was exactly that until 2026-08-28 (see below).

This file is the other half: two deliberately mis-declared instruction forms whose frame
obligations must be REFUTABLE, each with the refutation proved. If a future change to
`WritesWithin`/`ReadsWithin` (or to the footprint machinery they rest on) weakens them back into
vacuity, these proofs stop compiling, and that is the intended alarm.

The two forms here are NOT registered as `X86_64Instruction` instances -- they are plain `def`s
of the typeclass structure, applied explicitly with `@`. Registering them would trip
`Registry.lean`'s environment audit, which requires every live `X86_64Instruction` instance to
appear in `expectedInstructionTypes`; these are proof fixtures, not instructions, and must not
enter that population.
-/

namespace Gasm.Targets.X86_64.MemoryFrame.NegativeControl

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MemoryFrame

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Fixture: a memory-to-memory form. Its `step` loads 8 bytes from `[rsi]` and stores them to
    `[rdi]`, but its declared `memAccesses` mentions ONLY the store. The load from `[rsi]` is
    undeclared -- the lie this fixture exists to catch. -/
structure EvilMemMem where
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Fixture: a form whose `step` writes at `[rsi]` but which DECLARES a store at `[rdi]`. The
    store address itself is the lie here. -/
structure MisdeclaredStore where
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `EvilMemMem`'s typeclass witness. A `def`, deliberately not an `instance` -- see this file's
    header for why registering it would break `Registry.lean`'s audit. -/
def evilInst : X86_64Instruction EvilMemMem where
  encode _ := ByteArray.mk #[0x90]
  step _ s := (s.write64 (s.gprs .rdi) (s.read64 (s.gprs .rsi))).setGpr64 .rax 0
  toUops _ := []
  toNASM _ := "evil.memmem"
  toLean _ := "evil_memmem"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := []
  validationOracle _ := .nasmEncoding "proof fixture; never assembled"
  costProvenance _ := .modelInternalUnvalidated "proof fixture; never scheduled"
  memAccesses _ := [⟨.store, .w64, ⟨some .rdi, none, 0⟩⟩]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- `MisdeclaredStore`'s typeclass witness. A `def`, not an `instance`, for the same reason. -/
def misdeclaredInst : X86_64Instruction MisdeclaredStore where
  encode _ := ByteArray.mk #[0x90]
  step _ s := s.write64 (s.gprs .rsi) 0xAA
  toUops _ := []
  toNASM _ := "misdeclared.store"
  toLean _ := "misdeclared_store"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := []
  validationOracle _ := .nasmEncoding "proof fixture; never assembled"
  costProvenance _ := .modelInternalUnvalidated "proof fixture; never scheduled"
  memAccesses _ := [⟨.store, .w64, ⟨some .rdi, none, 0⟩⟩]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Shared counterexample base: `rdi = 0` (so the DECLARED store footprint is `[0, 8)`) and
    `rsi = 0x100` (the address actually touched, well outside it). -/
def cexBase : X86_64MachineState :=
  { rip := 0, flags := 0, memory := X86_64Mem.zero,
    gprs := fun r => if r == Reg64.rsi then 0x100 else 0 }

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Counterexample state 1: all-zero memory. -/
def cex1 : X86_64MachineState := cexBase

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Counterexample state 2: identical to `cex1` outside memory, differing ONLY at `[0x100, 0x108)`
    -- an address `EvilMemMem` reads but never declares. -/
def cex2 : X86_64MachineState :=
  { cexBase with memory := X86_64Mem.write .w64 0x100 0xAA X86_64Mem.zero }

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The two counterexample states really do agree outside memory. -/
theorem cex_agreeOutsideMemory : agreeOutsideMemory cex1 cex2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The two counterexample states agree on `EvilMemMem`'s DECLARED load footprint -- which is
    empty, because the form declares no load at all. This is the hypothesis `ReadsWithin` gets to
    assume, and it is satisfied. -/
theorem cex_agreeOn_declared_loads :
    agreeOn (loadFootprint (@X86_64Instruction.memAccesses _ evilInst EvilMemMem.mk) cex1)
      cex1.memory cex2.memory := by
  have hnil : loadFootprint (@X86_64Instruction.memAccesses _ evilInst EvilMemMem.mk) cex1 = [] :=
    rfl
  intro a ha
  rw [hnil] at ha
  exact absurd ha (List.not_mem_nil)

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- **The reason `ReadsWithin` needed strengthening.** `ReadsWithin`'s ORIGINAL conclusion was
    `agreeOutsideMemory (step s1) (step s2)` alone. This theorem shows that conclusion holds for
    `EvilMemMem` -- i.e. the old obligation was fully DISCHARGEABLE by a form that loads from a
    completely undeclared address, because the illicitly-read bytes land in memory, which the old
    conclusion never inspected. Kept as a permanent record of what the old definition permitted;
    contrast `evilMemMem_not_readsWithin` immediately below. -/
theorem evilMemMem_readsWithin_oldForm :
    ∀ s1 s2 : X86_64MachineState, agreeOutsideMemory s1 s2 →
      agreeOutsideMemory
        (@X86_64Instruction.step _ evilInst EvilMemMem.mk s1)
        (@X86_64Instruction.step _ evilInst EvilMemMem.mk s2) := by
  intro s1 s2 hout
  obtain ⟨hrip, hgprs, hflags, hstdin, hreq, hfault⟩ := hout
  -- `step` touches only `gprs` (via `setGpr64`) and `memory` (via `write64`); every other
  -- field is preserved definitionally, so five of the six components are the hypotheses.
  refine ⟨hrip, ?_, hflags, hstdin, hreq, hfault⟩
  show ((s1.write64 (s1.gprs .rdi) (s1.read64 (s1.gprs .rsi))).setGpr64 .rax 0).gprs
     = ((s2.write64 (s2.gprs .rdi) (s2.read64 (s2.gprs .rsi))).setGpr64 .rax 0).gprs
  simp only [X86_64MachineState.setGpr64, X86_64MachineState.write64]
  simp [hgprs]

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- **The strengthening bites.** With the `StoreAgreeOn` conjunct in place, the same
    undeclared-load form is REFUTABLE: `cex1`/`cex2` agree outside memory and agree on the
    declared (empty) load footprint, yet `step` writes different bytes into the declared store
    footprint, because those bytes came from `[rsi]` -- an address the descriptor never mentioned.
    This is the mutation test for `ReadsWithin`; if it stops compiling, the read-frame condition
    has been weakened back into vacuity. -/
theorem evilMemMem_not_readsWithin : ¬ @ReadsWithin EvilMemMem evilInst EvilMemMem.mk := by
  intro h
  have hstore := (h cex1 cex2 cex_agreeOutsideMemory cex_agreeOn_declared_loads).2
  have hmem : (0 : Address) ∈
      storeFootprint (@X86_64Instruction.memAccesses _ evilInst EvilMemMem.mk) cex1 := by
    decide
  have := hstore 0 hmem
  revert this
  decide

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- The `WritesWithin` mutation test: a form that writes at `[rsi]` while declaring a store at
    `[rdi]` is refutable, so `WritesWithin` genuinely pins the store ADDRESS rather than merely
    asserting that some store happened. -/
theorem misdeclared_not_writesWithin :
    ¬ @WritesWithin MisdeclaredStore misdeclaredInst MisdeclaredStore.mk := by
  intro h
  have hnot : (0x100 : Address) ∉
      storeFootprint (@X86_64Instruction.memAccesses _ misdeclaredInst MisdeclaredStore.mk)
        cexBase := by
    decide
  have := h cexBase 0x100 hnot
  revert this
  decide

end Gasm.Targets.X86_64.MemoryFrame.NegativeControl

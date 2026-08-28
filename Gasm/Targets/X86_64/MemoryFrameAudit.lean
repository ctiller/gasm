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
import Gasm.Targets.X86_64.Registry

/-
Gasm/Targets/X86_64/MemoryFrameAudit.lean -- two elaboration-time environment audits closing
gaps that adversarial review (2026-08-28) found in the MH1 memory hook.

Both mirror `Registry.lean`'s own `run_cmd` audit design: walk the live compiled environment and
fail the BUILD, rather than relying on a convention a reviewer has to notice.

AUDIT 1 (the seal lint). `X86_64Memory`'s `private mk ::` / `private raw` does NOT privatize the
auto-generated eliminators, so `X86_64Memory.casesOn`/`.rec`/`.recOn` remain public and can
project the raw `Address -> Byte` out of the sealed cell from any module. That leak is
semantically empty -- `X86_64Mem.readByte` is public and total, and is `rfl`-equal to the same
function -- but it defeats the property the hook actually exists to provide: that every memory
touch goes through a NAMED function in `MemoryCell.lean`, so the access sites are enumerable and
future instrumentation has one place to land. This audit enforces that property as a lint. It is
`docs/MEMORY_HOOK.md` §3.2's own named tier-3 fallback, adopted after the tier-1 claim there was
shown to be false; see `MemoryCell.lean`'s `X86_64Memory` docstring.

AUDIT 2 (frame-theorem coverage). `memAccesses` is defaultless, so an instruction cannot be
declared without stating its memory behaviour -- but nothing forced a matching
`writesWithin`/`readsWithin` pair to exist. `MemoryFrame.lean` is a hand-maintained import list;
a new memory-touching form could land with descriptors and no frame proof and nothing would
notice. This audit ties frame-theorem coverage to `expectedInstructionTypes`, the same manifest
`Registry.lean` already checks against the live environment.

SCOPE LIMIT, stated plainly: both audits see only what THIS module's import graph transitively
contains (via `Registry.lean`, the whole `Gasm.Targets.X86_64` tree plus its dependencies). They
do not scan `Stdlib` or `Spikes`. For AUDIT 1 that is a real residual gap -- a `Spikes/` file
could name `X86_64Memory.casesOn` and go unflagged. Closing it fully needs a standalone
`lean_exe` importing all three libraries, the way `Tools/CheckGatesAxioms.lean` does; that is
deliberately not done here because this is a tier-3 lint over a semantically empty leak, and the
executable costs a full-tree import (~830s measured) on every gate run.
-/

namespace Gasm.Targets.X86_64.MemoryFrameAudit

open Lean
open Gasm.Targets.X86_64.Instructions

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- The eliminators Lean auto-generates for `X86_64Memory`. `private mk ::` does not make these
    private, so each one can project the sealed `raw` field out of the cell. Only
    `Gasm.Targets.X86_64.MemoryCell` may mention them. -/
def sealBypassNames : List Name :=
  [``X86_64Memory.casesOn, ``X86_64Memory.rec, ``X86_64Memory.recOn]

/- REF: docs/MEMORY_HOOK.md#32-sealing-the-raw-field-what-makes-the-chokepoint-mechanical-not-conventional -/
/-- The one module the seal permits to touch `X86_64Memory`'s representation. -/
def sealOwningModule : Name := `Gasm.Targets.X86_64.MemoryCell

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Namespace the per-form `writesWithin`/`readsWithin` connection theorems live in. -/
def frameNamespace : Name := `Gasm.Targets.X86_64.MemoryFrame

/- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read -/
/-- Number of registered instruction forms currently allowed to lack a `writesWithin`/
    `readsWithin` pair.

    This is DEBT, recorded as a shrinking ceiling rather than a name list so that adding any new
    form without frame theorems turns the gate red immediately (the count rises above the
    ceiling), while the known-outstanding backlog does not.

    The value is now 0: the debt is fully paid. It was 74 -- the register-only forms, whose `step`
    bodies provably never mention `.memory` and whose obligations `MemoryFrame/Common.lean`'s
    `registerOnly_writesWithin`/`registerOnly_readsWithin` batch lemmas reduce to a one-liner each.
    Those 74 instantiations landed (`MemoryFrame/{Add,Sub,And,Or,Xor,Not,Neg,Shift,Test,Xchg,Cmp,
    Cmov,Jcc,Div,Imul,Lea,In,Out,Hlt,Syscall}.lean`), the audit below reported `0 form(s) missing`,
    and the ceiling was lowered to match in the same change.

    At 0 the ceiling is no longer debt but a ratchet: every registered instruction form now has a
    `writesWithin`/`readsWithin` pair, and any new form added without one turns this gate red
    immediately. Do not raise this value to land a new form -- write the form's frame theorems
    instead (register-only forms are a one-liner via the batch lemmas). -/
def frameCoverageDebtCeiling : Nat := 0

-- AUDIT 1: no module outside `MemoryCell.lean` may name an `X86_64Memory` eliminator.
run_cmd do
  let env ← Lean.getEnv
  let banned := sealBypassNames
  let mut offenders : Array (Name × Name) := #[]
  for i in [0 : env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if modName == sealOwningModule then continue
    unless (`Gasm).isPrefixOf modName do continue
    let modData := env.header.moduleData[i]!
    for declName in modData.constNames do
      if declName.isInternal then continue
      let some info := env.find? declName | continue
      let mut used : Array Name := info.type.getUsedConstants
      if let some v := info.value? then used := used ++ v.getUsedConstants
      for b in banned do
        if used.contains b then
          offenders := offenders.push (declName, modName)
  unless offenders.isEmpty do
    throwError s!"Memory-hook seal audit failed.\n\
      `X86_64Memory.casesOn`/`.rec`/`.recOn` project the sealed `raw : Address -> Byte` field out \
      of the memory cell. They are public only because Lean does not privatize auto-generated \
      eliminators alongside `private mk ::`; naming them outside \
      `Gasm/Targets/X86_64/MemoryCell.lean` bypasses the hook's named-chokepoint property (see \
      docs/MEMORY_HOOK.md §3.2). Use `X86_64Mem.readByte`/`read`/`write`/`initRegion` instead.\n\
      Offending declarations (declaration, module): {offenders.toList}"

-- AUDIT 2: every registered instruction form needs a `writesWithin`/`readsWithin` pair.
run_cmd do
  let env ← Lean.getEnv
  let mut missing : Array Name := #[]
  for tyName in Registry.expectedInstructionTypes do
    -- The open existential wrapper has no memory behaviour of its own; it forwards to whatever
    -- concrete instruction it holds, each of which is audited on its own row.
    if tyName == ``AnyX86_64Instruction then continue
    let base := frameNamespace.str tyName.getString!
    let hasW := env.contains (base.str "writesWithin")
    let hasR := env.contains (base.str "readsWithin")
    unless hasW && hasR do
      missing := missing.push tyName
  if missing.size > frameCoverageDebtCeiling then
    throwError s!"Memory frame-theorem coverage audit failed.\n\
      {missing.size} registered instruction form(s) lack a `writesWithin`/`readsWithin` pair in \
      `{frameNamespace}`, above the recorded ceiling of {frameCoverageDebtCeiling}. A form \
      declaring `memAccesses` without a matching frame theorem means its declared access list is \
      never connected to what `step` actually does (docs/MEMORY_HOOK.md §3.3, Law 12). Add \
      `<Form>.writesWithin`/`<Form>.readsWithin` in a `MemoryFrame/<Family>.lean` shard -- \
      register-only forms are one-liners via `registerOnly_writesWithin`/`registerOnly_readsWithin`.\n\
      Forms missing frame theorems: {missing.toList}"
  if missing.size < frameCoverageDebtCeiling then
    logInfo s!"Memory frame-theorem coverage: {missing.size} form(s) missing, ceiling is \
      {frameCoverageDebtCeiling}. The ceiling is now stale and should be lowered to \
      {missing.size} in Gasm/Targets/X86_64/MemoryFrameAudit.lean."

end Gasm.Targets.X86_64.MemoryFrameAudit

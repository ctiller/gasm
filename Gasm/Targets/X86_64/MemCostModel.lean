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

/-
Gasm/Targets/X86_64/MemCostModel.lean -- Layer P of the memory hook
(`docs/MEMORY_HOOK.md` §5, historical phase MH2). Collapses the 14 memory-touching instruction
forms' duplicated, uncited inline uop literal blocks (`MOV.storeAddr`/`MOV.storeData` hand-copied
verbatim across every store form; every load `latencyCycles := 4`) into ONE small, Law-14
provenance-marked coefficient table, from which every form's memory uops are DERIVED via its MH1
`memAccesses` descriptor rather than hand-written. This is the Law 12 fix for the twin population
`docs/X86_ISA_EXPANSION_PREREQUISITES.md` measured at "0 of 88 forms cite any source"
(`docs/X86_ISA_EXPANSION_PREREQUISITES.md` P5) -- collapsing 14 unlinked copies to one derivation makes the memory half of
that debt honestly countable instead of invisible.

MODULE LAYOUT (own leaf module, per docs/MEMORY_HOOK.md §7's cascade note): this file imports
`Uop.lean` (`X86_64Uop`, `PortId`) and `Memory.lean` (`MemAccessSpec`, `MemAccessKind`) but
deliberately NOT `Instructions/Base.lean` -- so a cost-table edit (recalibrating a coefficient)
rebuilds only this file's own dependents, not the full ~39-module semantic-hook cascade a
`memAccesses`/`step` edit would trigger. `Instructions/*.lean` (Mov.lean, Push.lean, Pop.lean,
Call.lean, Ret.lean) import THIS file in addition to `Instructions.Base` to call `memUops`.

REUSING RATIFIED VOCABULARY INSTEAD OF INVENTING A PARALLEL ONE: `docs/MEMORY_HOOK.md` §5.1's
literal sketch proposes a fresh `Provenance | modelInternal | calibrated <artifact>` inductive and
a `Cited` wrapper. `Instructions/Obligations.lean` (P4/P5, landed before this task) already defines
exactly this vocabulary as `CoefficientProvenance | cited (artifact) | modelInternalUnvalidated
(reason)`, with its own header comment stating the reason to reuse it verbatim: "so a report or a
future `check_calibration.py` reading either type's output means the same thing by 'unvalidated'."
This file's `Cited` wraps `Instructions.CoefficientProvenance` rather than a fresh `Provenance`
type -- a deliberate, documented deviation from the design's literal sketch, in the same spirit as
MH1's own documented deviations (`MemRef.base : Option Reg64` vs the design's plain `Reg64`, `disp
: UInt64` vs `Int`).

WHY 6 COEFFICIENTS, NOT "~8": the design's own count is approximate ("~8 named coefficients").
Reading all 14 memory forms' pre-existing inline literals (`Mov.lean`, `Push.lean`, `Pop.lean`,
`Call.lean`, `Ret.lean`) shows every load uop uniform (`latencyCycles := 4`,
`eligiblePorts := [.p2, .p3]`) regardless of width or form, and every store's two uops likewise
uniform (`storeAddr`: latency 1, ports `[.p2, .p3, .p7, .p8]`; `storeData`: latency 1, ports
`[.p4, .p9]`) -- so today's ENTIRE de-facto memory cost model is fully captured by 3 uop kinds x
2 attributes (latency, ports) = 6 named coefficients. The design's own placeholder for the missing
~2 ("per-width / indexed-addressing deltas as they become measurable, F1") is deliberately NOT
built here: §5.2 says the hook "designs the seam... without the model", and no width-dependent
behavior exists in the 14 forms to derive a delta FROM today -- adding an unused coefficient would
itself be an invented, uncited number, the exact defect this file exists to retire.

THE reciprocalThroughput DEAD-FIELD DECISION (MH2's own acceptance criterion: "memUops must not
populate reciprocalThroughput or other zero-read-site fields... either the field is deleted in a
coordinated change or this task records explicitly why it still exists"): grep-verified
(`grep -rn "reciprocalThroughput" --include=*.lean .`, excluding literal-assignment sites) zero
read sites anywhere in the tree, confirming `docs/X86_ISA_EXPANSION_PREREQUISITES.md` P5's finding independently for this
change. `memUops` below deliberately does NOT set it (leaving `X86_64Uop`'s struct default,
`0.25`, in place of the 14 forms' previous invented `0.5` literal) rather than perpetuating a
literal for a field nothing reads. Full field deletion is NOT done here: it remains in
`docs/X86_ISA_EXPANSION_PREREQUISITES.md` P5's backlog ("Reconcile X86_64.md §3 TSO claim + dead profile fields with the
code (B1, A3)"), and deleting it touches every one of the 88 forms' `toUops` (all `UopClass`
variants set it, not just the 3 memory-class ones), which is out of MH2's scope (the 14 memory
forms only). Recorded here, per the acceptance criterion's second branch, rather than silently
left unaddressed.

SEALING DECISION (MH2's acceptance criterion: "closed off structurally (private cost tag) or,
failing that, by a build-failing linter -- state which was achieved and why"): `memUops` is written
as the ONLY function in the tree that constructs a `.load`/`.storeAddr`/`.storeData`-class
`X86_64Uop` value from the cost table (every one of the 14 forms' `toUops` below is rewritten to
call it). But `X86_64Uop` itself is one flat structure literal syntax (`{ mnemonic := ..., uopClass
:= ..., ... }`) shared by ALL 11 `UopClass` variants across all 88 registered forms' `toUops` --
`.intALU`, `.branch`, `.serializing`, etc. all use the same public constructor. Sealing
CONSTRUCTION of memory-class uops specifically the way `MemoryCell.lean` seals `X86_64Memory`
(`private mk :: private raw`) would require bifurcating `X86_64Uop` into a memory/non-memory sum
type and touching every one of the 88 forms' `toUops`, not just the 14 memory ones -- out of MH2's
scope and a materially larger, differently-shaped change. The achieved mechanism is therefore
`docs/MEMORY_HOOK.md` §3.2's own named tier-3 fallback ("a compiled-environment audit in the
`Registry.lean`/`check_refs_coverage` style, only if tier 1 proves untenable"): a build-failing
DERIVATION-INVARIANT check, wired into `Tools/CheckX86Obligations.lean` (which already walks
`Registry.allEncodableInstructions`), asserting that every registered form's memory-class `toUops`
subset equals `memAccesses` mapped through `memUops` at the shared `defaultMemCostModel` -- a hand-
written memory-class uop that diverges from the table fails the gate. See that file for the check
and its Law-13 negative-control demonstration.
-/
import Lean
import Gasm.Targets.X86_64.Uop
import Gasm.Targets.X86_64.Memory
import Gasm.Targets.X86_64.Instructions.Obligations

namespace Gasm.Targets.X86_64

open Gasm.Targets.X86_64.Instructions (CoefficientProvenance)

/- REF: docs/MEMORY_HOOK.md#51-one-table-provenance-marked-instead-of-14-sets-of-inline-literals -/
/-- A value paired with its Law-14 provenance mark, reusing `Instructions.CoefficientProvenance`
    (P4/P5's already-ratified vocabulary) instead of `docs/MEMORY_HOOK.md` §5.1's literal
    `Provenance` sketch -- see this file's header comment for why. -/
structure Cited (α : Type) where
  value  : α
  source : CoefficientProvenance
  deriving Inhabited

/- REF: docs/MEMORY_HOOK.md#51-one-table-provenance-marked-instead-of-14-sets-of-inline-literals -/
/-- Layer P's memory cost coefficient table: every memory-class uop in the tree (load,
    store-address, store-data) is constructed from exactly these 6 named, independently
    Law-14-marked coefficients via `memUops` below -- replacing the 14 forms' previously
    hand-copied inline literal blocks (a Law-12 unlinked-twin population). Calibrating one
    coefficient here recalibrates every form that uses it at once; see this file's header
    comment for why 6 (not the design's approximate "~8"). -/
structure MemCostModel where
  loadLatency      : Cited Nat
  loadPorts        : Cited (List PortId)
  storeAddrLatency : Cited Nat
  storeAddrPorts   : Cited (List PortId)
  storeDataLatency : Cited Nat
  storeDataPorts   : Cited (List PortId)
  deriving Inhabited

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- Today's de-facto memory cost model, relabeled honestly as `modelInternalUnvalidated` rather
    than left as 14 sets of implicit, uncited literals (`docs/X86_ISA_EXPANSION_PREREQUISITES.md`
    P5: "0 of 88 forms cite any source"). Values are UNCHANGED from what the
    14 forms' inline `toUops` literals encoded before this migration -- verified by reading every
    memory form's pre-migration `toUops` in `Mov.lean` (9 forms), `Push.lean`, `Pop.lean`,
    `Call.lean` (2 forms), `Ret.lean`: every load uop was `latencyCycles := 4, eligiblePorts :=
    [.p2, .p3]`; every store's address uop was `latencyCycles := 1, eligiblePorts := [.p2, .p3,
    .p7, .p8]`; every store's data uop was `latencyCycles := 1, eligiblePorts := [.p4, .p9]` --
    this migration is a pure re-derivation, not a re-calibration.

    PER-COEFFICIENT MEASUREMENT RECIPES (`docs/MEMORY_HOOK.md` §5.2 item 2 -- named, but not yet
    accepted as governed coefficient bindings):
    - `loadLatency`/`loadPorts`: a dependent pointer-chase microbenchmark resident in L1 (each
      load's address depends on the previous load's result, isolating load-to-use latency from
      throughput; port occupancy read from `perf`/PMU counters on the same run).
    - `storeAddrLatency`/`storeAddrPorts`: a store/reload chain isolating the address-generation
      uop's port and latency contribution (store-to-load forwarding stalls are a confound to
      control for, not measure here).
    - `storeDataLatency`/`storeDataPorts`: the same store/reload chain, isolating the data-write
      uop once the address-generation contribution above is subtracted out.
    Each recipe is the refuting experiment for its coefficient: F1's containment criterion
    (`real ∈ [min, max]`) and rank-order checks apply per-coefficient once it lands, not per-form
    (`docs/MEMORY_HOOK.md` §5.2 item 2). -/
def defaultMemCostModel : MemCostModel where
  loadLatency := {
    value := 4
    source := .modelInternalUnvalidated
      "toUops coefficients predate Law 14 and are uncalibrated inline literals; no accepted \
      governed calibration binding exists, and intel-sdm (the registered combined architecture SDM) does not publish \
      cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5" }
  loadPorts := {
    value := [.p2, .p3]
    source := .modelInternalUnvalidated
      "toUops coefficients predate Law 14 and are uncalibrated inline literals; no accepted \
      governed calibration binding exists, and intel-sdm (the registered combined architecture SDM) does not publish \
      cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5" }
  storeAddrLatency := {
    value := 1
    source := .modelInternalUnvalidated
      "toUops coefficients predate Law 14 and are uncalibrated inline literals; no accepted \
      governed calibration binding exists, and intel-sdm (the registered combined architecture SDM) does not publish \
      cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5" }
  storeAddrPorts := {
    value := [.p2, .p3, .p7, .p8]
    source := .modelInternalUnvalidated
      "toUops coefficients predate Law 14 and are uncalibrated inline literals; no accepted \
      governed calibration binding exists, and intel-sdm (the registered combined architecture SDM) does not publish \
      cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5" }
  storeDataLatency := {
    value := 1
    source := .modelInternalUnvalidated
      "toUops coefficients predate Law 14 and are uncalibrated inline literals; no accepted \
      governed calibration binding exists, and intel-sdm (the registered combined architecture SDM) does not publish \
      cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5" }
  storeDataPorts := {
    value := [.p4, .p9]
    source := .modelInternalUnvalidated
      "toUops coefficients predate Law 14 and are uncalibrated inline literals; no accepted \
      governed calibration binding exists, and intel-sdm (the registered combined architecture SDM) does not publish \
      cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5" }

/- REF: docs/MEMORY_HOOK.md#51-one-table-provenance-marked-instead-of-14-sets-of-inline-literals -/
/-- Every coefficient in a `MemCostModel`, as a flat list -- the source `check_x86_obligations`
    reads to count "N of M memory coefficients calibrated" (Law 14's honesty-in-output clause,
    `docs/MEMORY_HOOK.md` §5.3(b)). -/
def MemCostModel.provenances (m : MemCostModel) : List CoefficientProvenance :=
  [m.loadLatency.source, m.loadPorts.source, m.storeAddrLatency.source, m.storeAddrPorts.source,
   m.storeDataLatency.source, m.storeDataPorts.source]

/- REF: docs/MEMORY_HOOK.md#51-one-table-provenance-marked-instead-of-14-sets-of-inline-literals -/
/-- How many of the table's 6 coefficients are `.cited` (calibrated against a real artifact),
    versus honestly `.modelInternalUnvalidated`. Both are always well-defined and their sum is
    always `MemCostModel.provenances`'s length -- there is no third state, matching every other
    Law-14 marker in this tree. -/
def MemCostModel.calibratedCount (m : MemCostModel) : Nat :=
  (m.provenances.filter (fun p => p matches .cited _)).length

/- REF: docs/MEMORY_HOOK.md#5-layer-p-the-perf-side-and-how-it-stays-falsifiable -/
/-- Whether an `X86_64Uop`'s class is one `memUops` constructs (as opposed to `.intALU`,
    `.branch`, etc., which mixed memory/control-flow forms like `CallRipRel`/`RetOp` still
    hand-write alongside their derived memory uops). The predicate the derivation-invariant audit
    (`Tools/CheckX86Obligations.lean`) filters `toUops` by. -/
def isMemoryClassUop (u : X86_64Uop) : Bool :=
  u.uopClass == .load || u.uopClass == .storeAddr || u.uopClass == .storeData

/- REF: docs/MEMORY_HOOK.md#51-one-table-provenance-marked-instead-of-14-sets-of-inline-literals -/
/-- The hook's ONLY constructor of memory-class uops (`docs/MEMORY_HOOK.md` §5.1: "the hook
    exposes the only constructors of memory-class uops"). Every one of the 14 memory-touching
    forms' `toUops` is rewritten to derive its memory-class uops by mapping `memAccesses` through
    this function instead of hand-writing the literal blocks `Mov.lean`/`Push.lean`/`Pop.lean`/
    `Call.lean`/`Ret.lean` previously duplicated. A `.load` access produces one uop; a `.store`
    access produces two (address-generation then data-write, matching real store execution and
    every pre-migration form's uop count) -- `spec.width` does not otherwise vary the result
    (see `defaultMemCostModel`'s doc comment: no width-dependent behavior exists in the 14 forms
    to derive a delta from today). Deliberately does NOT set `reciprocalThroughput` (see this
    file's header comment: the field is dead, `docs/X86_ISA_EXPANSION_PREREQUISITES.md` P5, zero read sites tree-wide) --
    it is left at `X86_64Uop`'s struct default rather than perpetuating an invented literal for a
    field nothing reads. The generic `"MEM.load"`/`"MEM.storeAddr"`/`"MEM.storeData"` mnemonics
    replace the 14 forms' previous family-specific labels (`"MOV.load"`, `"MOVZX.load"`,
    `"POP.load"`, `"RET.popTarget"`, `"CALL.loadTarget"`, `"PUSH.storeAddr"`, ...) -- `mnemonic`
    is display-only debug text with zero read sites that key off its exact string content
    (`Performance.lean` formats it generically for report output; grep-verified no consumer
    branches on a specific mnemonic value), so collapsing 14 cosmetic spellings to one canonical
    triple is exactly the kind of duplication Law 12 asks a hook to retire, not a behavior
    change. -/
def memUops (spec : MemAccessSpec) (model : MemCostModel) : List X86_64Uop :=
  match spec.kind with
  | .load =>
    [{ mnemonic := "MEM.load", uopClass := .load,
       eligiblePorts := model.loadPorts.value, latencyCycles := model.loadLatency.value }]
  | .store =>
    [{ mnemonic := "MEM.storeAddr", uopClass := .storeAddr,
       eligiblePorts := model.storeAddrPorts.value, latencyCycles := model.storeAddrLatency.value },
     { mnemonic := "MEM.storeData", uopClass := .storeData,
       eligiblePorts := model.storeDataPorts.value, latencyCycles := model.storeDataLatency.value }]

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- The full derived memory-uop stream for a form's declared accesses, in declaration order --
    exactly what every memory-touching form's `toUops` now computes for its memory-class uops
    (mixed forms like `CallRipRel`/`RetOp` concatenate their remaining control-flow uops after
    this). This is also the right-hand side of the derivation invariant
    `Tools/CheckX86Obligations.lean` checks against the registry. -/
def derivedMemUops (accesses : List MemAccessSpec) (model : MemCostModel) : List X86_64Uop :=
  accesses.flatMap (memUops · model)

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- Cost-relevant equality between two uops: class, eligible ports, and latency must match.
    Deliberately ignores `mnemonic` (display-only debug text -- MH2 collapsed 14 family-specific
    spellings to 3 generic ones, see `memUops`'s doc comment) and `reciprocalThroughput` (the
    dead field, see this file's header comment) -- neither carries cost-model content the
    derivation invariant needs to protect. Used by `Tools/CheckX86Obligations.lean`'s
    registry-wide derivation-invariant check: "the memory-class subset of a form's `toUops`
    equals `memAccesses` mapped through `memUops`" (`docs/MEMORY_HOOK.md` §5.2 item 3). -/
def memUopCostEq (a b : X86_64Uop) : Bool :=
  decide (a.uopClass = b.uopClass) && decide (a.eligiblePorts = b.eligiblePorts) &&
  a.latencyCycles == b.latencyCycles

/- REF: docs/MEMORY_HOOK.md#52-why-this-is-falsifiable-where-todays-numbers-are-not -/
/-- Pointwise `memUopCostEq` over two uop lists, order-sensitive (declaration order is part of
    what `derivedMemUops` promises -- see its own doc comment) and length-checked first so a
    dropped or extra uop cannot pair-shift into a false pass. -/
def memUopListEq (a b : List X86_64Uop) : Bool :=
  a.length == b.length && (a.zip b).all (fun p => memUopCostEq p.1 p.2)

end Gasm.Targets.X86_64

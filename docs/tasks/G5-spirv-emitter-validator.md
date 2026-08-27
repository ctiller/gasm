---
id: G5
title: SPIR-V emitter + Lean validator + registry-style shader gate
status: ready
blocked_on: ""
after: [G2, G3]
related: []
bar: ""
track: graphics
priority: 7.3
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G5: SPIR-V emitter + Lean validator + registry-style shader gate

## Context

`GRAPHICS_PREBUILD_AUDIT.md` §9 ranked amendment #7 states the fix directly: **"Replace
the spirv-val claim with a gate: Lean SPIR-V validator + ∀-registered-shaders validity
theorem; grammar-driven encode/decode roundtrip."** This task is sequenced `after: [G2,
G3]` because the validator's job is to make *unrepresentable* the exact classes of bug G2
(synchronization) and G3 (FP determinism) define as invalid — a SPIR-V emitter that can
produce a module violating either DSL's invariants defeats both designs at the encoding
layer, so this task needs both DSLs' invariant shapes settled before it can state what
"valid" means for the emitter it gates.

### The current overclaim

`docs/TARGETS/SPIRV_VULKAN.md:46` states: "The `gasm` SPIR-V DSL automatically generates
and typechecks structured merge declarations, guaranteeing that emitted SPIR-V passes
Khronos validation (`spirv-val`)." Audit §3 names exactly why this is an overclaim as
written: "The `spirv-val` 'guarantee' claim at `SPIRV_VULKAN.md:46` must become a
build-time Lean SPIR-V validator + ∀-over-registered-shaders validity theorem (the Wasm
precedent), with spirv-val demoted to external cross-check." As written, the doc treats an
*external tool's* opinion as the guarantee; nothing in the repo's own Lean proves it. This
is the same shape of defect Law 8 forbids generally ("audited observable tracing" and
"universal specification theorems vs. concrete simulation instances") and the same shape
PLAN.md's own history already caught once: the Wasm-side fix (referenced by the audit as
"the Wasm precedent") replaced an external-tool-trust pattern with an in-repo build-time
Lean validator plus a ∀-registered-case validity theorem, after a fail-open oracle
(`INVALID:`/`TRAP:` laundering, PLAN.md's V8 finding — see G4's file) demonstrated why
trusting the external tool's pass/fail alone is unsound as *the* gate.

### The TC4 registry-gate precedent, applied to SPIR-V

TASKS.md's TC4 ("decoder + registry build-gate branch") is the x86-64 instruction-decoder
analog of what this task builds for SPIR-V: a closed population (the set of shader modules
this repo actually emits, or the set of opcodes the emitter is capable of producing) gets
an exhaustive, build-time-checked validity theorem rather than a sampled or externally
delegated check. This is precisely the D11 pattern named in `docs/VISION.md` §4: "A closed
population gets exhaustive language-level theorems (the instruction registry's roundtrip
gate is exactly this shape)." This task is the SPIR-V-domain instance of that same pattern:
a **registry-style ∀-over-registered-shaders validity theorem** — every shader module the
build actually registers/emits is proven valid against the Lean validator, at build time,
the same way TC4 proves every registered instruction decodes/encodes correctly.

### Grammar connection theorem (Law 12)

The task also requires a **grammar connection theorem vs `spirv.core.grammar.json`** —
this is `docs/REVIEW.md` Law 12 territory: "Two encodings of the same model-level fact... may
coexist ONLY when linked by a kernel-checked connection theorem proving their
equivalence." The Lean validator's notion of "valid SPIR-V" and the Khronos-published
machine-readable grammar are two encodings of the same fact (what instruction operand
shapes and enum values are legal); Law 12 requires either deriving one from the other or a
proven connection theorem between them. **Open gap, flagged honestly**: `references/spirv/`
currently contains only four prose chapters converted from the unified specification
(`ch_01_1_introduction.md` through `ch_04_4_appendix_a_changes.md`, per
`references/spirv/INDEX.md`) — grep-verified, no `spirv.core.grammar.json` or any other
machine-readable grammar file exists anywhere in this repository at the time this task was
written. The audit's and this task's references to "the ingested `spirv.core.grammar.json`"
describe a *planned* ingestion, not a present one. **This task's design doc must therefore
include, ahead of the connection theorem itself, a Law 4/Law 6 ingestion step**: vendoring
the actual Khronos `spirv.core.grammar.json` (and its `.unified1` sibling, if the emitter
targets a specific SPIR-V version) into `references/spirv/` via
`scripts/regenerate_references.py`, with a MANIFEST entry, before the connection theorem
can be stated against real ground truth rather than the prose spec alone. Treat this as a
prerequisite sub-deliverable, not an assumption.

## Deliverables & acceptance criteria

- A design document specifying: (1) the Lean SPIR-V validator's checks (structured
  control-flow well-formedness — merge-block/loop-merge correctness, already partially
  modeled by `SpirvTerminator` in `docs/TARGETS/SPIRV_VULKAN.md:31-44`; capability
  declarations matching used opcodes; type/operand-shape well-formedness per the grammar);
  (2) the registry-style ∀-theorem: for every shader module registered in the build (the
  closed population, TC4-style), the validator accepts it — stated and discharged the same
  way TC4's decoder roundtrip gate is, at build time; (3) `spirv-val` demoted explicitly to
  an *external cross-check* consumed by G4's differential harness (one oracle among
  several), never cited again as itself "the guarantee."
- A concrete plan (can be a design-doc section, not full execution) to ingest
  `spirv.core.grammar.json` into `references/spirv/` per Law 4/Law 6, since it is not
  currently vendored — name the target file location, the MANIFEST entry it needs, and how
  `scripts/regenerate_references.py --verify` will be extended to cover it. (This task's own
  Lean implementation must not be built before this ingestion lands, per Law 5.)
- The grammar connection theorem itself: a kernel-checked proof that the Lean validator's
  notion of syntactic validity agrees with the vendored grammar's constraints over the
  relevant finite domain (opcode enum, operand kind table) — Law 12's "connection theorem
  proving equality over the entire (finite) shared domain," discharged the same way other
  registry/grammar connection theorems in this repo are (see TC4 precedent).
- Fix the concrete `returnVoid` quantifier bug at `docs/TARGETS/SPIRV_VULKAN.md:43`
  *if it survives G1's housekeeping pass* — G1 is already scoped to fix this
  (`(h_clean : ∀ (s : ComposedState spirv S), s.obligations = [])` quantifies over all
  states of the typestate rather than the actual reached exit state, making the terminator
  unconstructible for any inhabited state type with a nonempty ledger). This task does not
  need to re-fix it; note it here only as the concrete illustration of why doc-then-review-
  then-code discipline matters for exactly this kind of quantifier error, and confirm at
  authoring time that G1's fix actually landed before building the validator against it.
- Per Law 13(4): state what differential evidence downstream implementation needs —
  specifically, that G4's harness must exercise both a valid-module positive case (accepted
  by both the Lean validator and lavapipe) and a malformed-module negative case (rejected by
  the Lean validator at build time, *and* separately confirmed rejected by lavapipe/
  `spirv-val` as the external cross-check) — closing the loop between this task's build-time
  gate and G4's runtime oracle rather than leaving them unconnected.
- Law-5/Law-13 discipline: design doc authored, then routed through fresh-agent design
  review before `design_review` is marked approved and before any Lean cites it.

## Pointers

- `docs/TARGETS/SPIRV_VULKAN.md:46` (the `spirv-val` "guarantee" overclaim to replace),
  `:31-44` (`SpirvTerminator`, structured merge typestate — the existing partial model this
  validator extends), `:43` (the `returnVoid` quantifier bug, G1's fix, noted here only as
  precedent).
- `GRAPHICS_PREBUILD_AUDIT.md` §3 (spirv-val paragraph), §9 ranked amendment #7 — read in
  full.
- `references/spirv/INDEX.md` and directory listing (grep/`ls`-verified: `INDEX.md`,
  `ch_01_1_introduction.md`, `ch_02_2_specification.md`, `ch_03_3_binary_form.md`,
  `ch_04_4_appendix_a_changes.md` — four prose chapters, **no machine-readable grammar file
  present**) — the Law 4 ingestion-status ground truth this task's design doc must be
  honest about.
- `docs/REVIEW.md` Law 4 (external reference ingestion), Law 6 (reference reproducibility —
  the grammar file must come in via `scripts/regenerate_references.py`, not hand-copied),
  Law 12 (connection theorem mandate — the grammar-vs-validator link).
- TASKS.md's TC4 entry ("decoder + registry build-gate branch") — the precedent this task's
  registry-style ∀-shader gate imitates; `docs/VISION.md` §4's citation of "the instruction
  registry's roundtrip gate" as the closed-population exemplar.
- G2's file (`docs/tasks/G2-synchronization-dsl.md`) and G3's file
  (`docs/tasks/G3-fp-kernel-dsl.md`) — this validator must reject modules violating either
  DSL's invariants; confirm both designs are approved before authoring this validator's
  acceptance criteria in detail.
- G4's file (`docs/tasks/G4-gpu-differential-harness.md`) — the model-faithfulness /
  artifact-validity boundary; this task owns artifact validity (is the SPIR-V well-formed),
  G4 owns model faithfulness (does it compute the right answer).
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing), so this design targets a future
  `Gasm/Targets/*` SPIR-V emitter/validator module, name TBD during authoring, resolving the
  `Gasm.Targets.Spirv` vs `Gasm/SPIRV/` naming drift G1's housekeeping pass addresses.

## Notes

- 2026-08-27: priority 7.3 — SPIR-V emitter + Lean validator + registry-style gate; the spirv.core.grammar.json ingestion gap TCB T8 flags as missing on disk is directly this task's dependency (see TC16's related link).

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_

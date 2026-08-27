---
id: G1
title: Graphics doc rework per GRAPHICS_PREBUILD_AUDIT top-10
status: done
blocked_on: ""
after: []
related: []
bar: ""
track: graphics
priority: 8.3
priority_set: 2026-08-27T18:25:47Z
design: "inline"
design_review: "approved 2026-08-27"
date: 2026-08-27
---

# G1: Graphics doc rework per GRAPHICS_PREBUILD_AUDIT top-10

## Context

Zero graphics Lean code exists in this repository, and no `REF:` citation anywhere in the tree
points at either graphics doc — `GRAPHICS_PREBUILD_AUDIT.md`'s framing is exact: "every fix below
is cheap now and expensive after code." An Opus researcher audited the two existing unbuilt
graphics plans (`docs/GRAPHICS_ARCHITECTURE.md`, `docs/TARGETS/SPIRV_VULKAN.md`) against every
ratified lens this project has (VISION, Laws 9–13, the observation standard in
`docs/EQUIVALENCE_PROOFS.md` §1.1, `docs/SYSTEM_EFFECTS.md` §6, PLAN.md's decisions) **before any
graphics code was written**, on the exact principle this conversion's own task-lifecycle
discipline now generalizes: design review is cheapest before code exists. Its verdict: **"NOT
ready for Spike 6."** This task is the doc-rework half of that audit's remediation — the
structural/scope fixes to the *existing* two docs. The harder, genuinely new design content (the
synchronization DSL, the FP kernel DSL, the differential harness, the SPIR-V validator, the Vulkan
host/capability model) is intentionally split out into G2–G6, each of which depends on this task
landing first so they're building on a corrected foundation rather than patching a moving one.

This task directly implements **ranked amendments #1, #2, #5, and #10** from
`GRAPHICS_PREBUILD_AUDIT.md` §9, plus its housekeeping list. Each is a concrete, already-diagnosed
defect in the current docs — this task's job is authoring the fix, not further investigation.

### 1. Redefine Spike 6 as parametric compute; delete the input-free gradient (audit #1)

`docs/GRAPHICS_ARCHITECTURE.md` §7 item 3 currently specifies Spike 6 as "Offscreen rendering of a
multi-color gradient / triangle to an RGBA8 buffer" with "100% constructive trace equivalence
across all 4 target pairings" (`:135-139`). The audit's §4 (read-binder / anti-pointwise mapping)
names this precisely: "Spike 6 as specified renders a fixed gradient with no input — its
equivalence theorem is pointwise by construction, satisfiable by a shader that stores a
precomputed table (the Tier-1 pattern)." This is `docs/VISION.md` §2's canned-output exhibit
rebuilt in a new domain, and Law 9 forbids it structurally. The audit's rasterization warning
compounds this: "the planned gradient-triangle spike is the worst possible first spike"
(rasterization tie-breaks are implementation-defined per the Vulkan invariance appendix — see
G3's file for the full FP-determinism argument). Fix: rewrite Spike 6's specification as
**parametric compute** — `∀ input buffer b (within declared bounds), readback = specFn(b)` — a
compute-only kernel, no rasterization, no fixed gradient.

### 2. Give `GpuEvent.readbackPixels` a payload; split contract vs. audit trace (audit #2)

`GpuEvent` (`docs/GRAPHICS_ARCHITECTURE.md:60-72`) mixes resource/command events
(`createDevice`, `createBuffer`, `createPipeline`, `transitionLayout` — audit-trace shaped, per
`docs/EQUIVALENCE_PROOFS.md` §1.1's "Vulkan/DX12/WebGPU entry points are the analog of
`VirtualAlloc`") with dispatch/readback events (contract-shaped) in one undifferentiated trace.
The audit's sharpest finding, verbatim: **"`readbackPixels (buffer) (pixelCount)` carries no pixel
data."** Line 71 confirms this exactly: `| readbackPixels (buffer : BufferHandle) (pixelCount :
Nat)` — the event records that a readback happened and how many pixels, never what came back. "The
trace records that a readback happened, not what came back — an implementation rendering garbage
satisfies trace equality." This is not a stylistic nit; it is the graphics-domain instance of the
exact canned-output vulnerability `docs/VISION.md` §2 exists to prevent everywhere else in the
project. Fix: `readbackPixels` must carry the actual returned payload (or a hash/reference to it
sufficient for equivalence checking); and the doc must state explicitly, per the observation
standard, that the **contract trace** for Spike 6 is exactly "PNG bytes on disk + exit code" (what
leaves the process), while device/resource events are **audit trace**, attached to the per-target
Vulkan typeclass instance under Law 8 — not equivalence observables. §7.3's claim of "100%
constructive trace equivalence across all 4 target pairings" is, per the audit, "incoherent under
§1.1" for a second, independent reason: a trace containing Vulkan resource events can never equal
a DX12 trace, because the two APIs' audit-trace shapes are not the same language. Rewrite that
claim entirely once the contract/audit split lands — it should not survive in its current form.

### 3. Shrink the six-target matrix to Win-Vulkan-compute (audit #5)

`docs/GRAPHICS_ARCHITECTURE.md` §2 (`:27-36`) declares six target slices: Win-Vulkan, Win-DX12,
Wasm-Vulkan, Wasm-WebGPU, Win-Compute, Wasm-Compute. The audit calls this "the bulk-import
pattern D7 forbids" outright — six speculative targets, zero built, is exactly the failure mode
`docs/VISION.md` §3.3 names as the predecessor project's cause of death (build ISA/targets before
the model is validated). Worse, **two of the six are fiction as written**: "browsers have no
Vulkan; WASI has no GPU; 'Host FFI trampolines' = inventing host imports, the same defect class as
Spike 4's fabricated `sock_*`" — Wasm-Vulkan (target 3) is impossible as stated, and Wasm-WebGPU
(target 6, or table row "Wasm-Compute") needs a real documented import surface that does not
currently exist. Fix: shrink the doc's declared target matrix to **one** — Windows x86-64 +
Vulkan, compute only — and demote the other five to an explicitly-labeled, **non-obligating**
"possible futures" appendix. This matters for a subtle but sharp reason the audit calls out under
Law 2: "any `REF:` citing the six-target section makes all six a 100%-implementation obligation."
As long as the six-target table is a normal, citable doc section, the moment any Lean code cites
it, Law 2 (implementation completeness) obligates building out all six — so this fix must happen
*before* any graphics `REF:` citation exists, which is exactly why this task has no upstream
dependency and is ready now.

### 4. Ingest missing references or explicitly defer those targets (audit #10, partial)

The audit's ingestion status check: SPIR-V unified spec and Vulkan 1.3 (including
`ch_07_synchronization`, `appendix_b__memory_model`, `appendix_i__invariance`, `ch_23_queries`) are
**fully vendored** — the Win-Vulkan-compute target this task shrinks the matrix to already has its
Law-4 ground truth in `references/`. DXIL/DXBC, D3D12, WGSL, and WebGPU are **not** vendored, and
per Law 5 their design docs (`docs/TARGETS/DXIL_D3D12.md`, `docs/TARGETS/WGSL_WEBGPU.md`) do not
exist. This task's job is not to author those docs (out of scope — they're exactly the kind of
speculative future-target work D7 defers) but to make the *current* docs honest about that
absence: the "possible futures" appendix from item 3 above should state plainly, per target, what
reference ingestion and design-doc work would be required before that target could be built, so a
future agent doesn't mistake the appendix for a ready backlog.

### Housekeeping (audit §8, "Contradictions & staleness")

Fold these into the same editing pass since they're all small and in the same two files (plus one
sibling doc):

- `docs/STDLIB_PNG.md:10` reads "Headless GPU Readback (**Spike 5**)" — stale; Spike 5 is gzip
  (confirmed: `Spikes/Spike5Gzip/` exists in the tree). Fix to Spike 6.
- Target-count inconsistency: `GRAPHICS_ARCHITECTURE.md` §2 lists six, its §1 mermaid diagram
  shows four lowering arrows, §7.3 claims "all 4 pairings" — all three must agree once the matrix
  is shrunk to one (item 3 above resolves this by construction: there is no longer a six-vs-four
  discrepancy to reconcile if there's exactly one target).
- Naming drift: the doc's own `Gasm.Targets.Spirv/Dxil/Wgsl` module names vs. `Gasm/SPIRV/` vs.
  `Gasm.SPIRV` are inconsistent with each other and with the repo's real tree convention
  (`Gasm/Targets/*`) — pick the real convention and use it consistently.
- `docs/SPIKES.md` / `PLAN.md` law-count references need updating to 13 (Law 13 — "Findings
  Become Gates" — was added after some of these references were written).
- Doc-level Law-12-spirited twin: `GRAPHICS_ARCHITECTURE.md:118-126` copies
  `png_idempotent_canonical_roundtrip` **verbatim** from `docs/STDLIB_PNG.md` — this should cite
  `STDLIB_PNG.md`'s copy rather than duplicate it (single source of truth, per Law 12's stated
  preference order even at the doc level).
- The `returnVoid` quantifier bug in `docs/TARGETS/SPIRV_VULKAN.md:43` — `(h_clean : ∀ (s :
  ComposedState spirv S), s.obligations = [])` quantifies over **all** states with that typestate,
  not the actual exit state reached at the point of return. As written this is unprovable for any
  inhabited state type with a nonempty ledger — the terminator is unconstructible. This is a small
  but real bug in existing (unbuilt) doc-level Lean signature and should be fixed to quantify over
  the specific reached state, not all states of the type.

### What this task explicitly does NOT cover

The synchronization model (RAW-inclusive happens-after edges replacing `SPIRV_VULKAN.md:65-67`'s
WAR/WAW-only layout-FSM claim), the floating-point determinism / Deterministic Shader Profile
question, the differential-validation harness design, the SPIR-V validator-vs-`spirv-val` gate
design, and the GPU memory/capability model are all **separate design docs**, deliberately
sequenced as G2–G6 `after: G1` so each gets focused treatment rather than being folded into one
enormous rewrite. This task should leave clearly-labeled placeholders/pointers in the reworked
docs noting where G2–G6's content will land, rather than attempting to sketch that content itself.

## Deliverables & acceptance criteria

- `docs/GRAPHICS_ARCHITECTURE.md` rewritten: Spike 6 redefined as parametric compute (no fixed
  gradient, no rasterization); `GpuEvent` split so `readbackPixels` carries a real payload and the
  doc states the contract/audit trace boundary explicitly per `docs/EQUIVALENCE_PROOFS.md` §1.1;
  §7.3's "100% constructive trace equivalence across all 4 target pairings" claim removed/rewritten
  to be coherent under the observation standard; six-target matrix shrunk to one (Win-Vulkan,
  compute-only) with the other five moved to a clearly non-obligating "possible futures" appendix
  stating what each would require before it's buildable.
- `docs/TARGETS/SPIRV_VULKAN.md`'s `returnVoid` quantifier fixed to bind the actual reached state.
- All housekeeping items above closed: `STDLIB_PNG.md:10`'s Spike5→6 fix, mermaid/matrix/§7.3
  target-count agreement, module-naming drift resolved to the real `Gasm/Targets/*` convention,
  law-count references updated to 13, the duplicated PNG roundtrip theorem replaced with a
  citation to `STDLIB_PNG.md`.
- No new design content invented for the synchronization/FP-determinism/harness/validator/capability
  questions — this task rewrites and scopes, it does not design those; clear pointers to G2–G6
  left in their place.
- Since the six-target-matrix shrink is what prevents an accidental Law-2 100%-implementation
  obligation on five fictional targets, this task should land (and be reviewed) **before** any
  graphics Lean file is written or cites either doc — it is intentionally sequenced with no
  upstream dependency so nothing blocks it.
- This is Law-5-class (it reshapes what Spike 6 and the target matrix commit the project to), so
  route the reworked docs through a design review before marking this task done — the same
  discipline the original pre-build audit modeled.

## Pointers

- `docs/GRAPHICS_ARCHITECTURE.md:27-36` (six-target matrix, §2), `:60-72` (`GpuEvent`, note
  `readbackPixels` at `:71` carrying no payload), `:118-126` (duplicated PNG theorem),
  `:135-139` (Spike 6 spec + "100% constructive trace equivalence" claim, §7 item 3).
- `docs/TARGETS/SPIRV_VULKAN.md:43` (`returnVoid` quantifier bug), `:46` (the `spirv-val` claim —
  leave as-is for G5 to address; do not attempt the validator-vs-gate rework here), `:65-67`
  (WAR/WAW-only barrier claim — leave for G2, do not attempt the sync-model rework here).
- `docs/STDLIB_PNG.md:10` (stale "Spike 5" reference).
- `GRAPHICS_PREBUILD_AUDIT.md` in full — this task implements §9 items 1, 2, 5, 10 and all of §8;
  read the whole document, not just the excerpts quoted above, since it is the primary source this
  task file summarizes.
- `MODEL_DEBT.md` §D (graphics-forward debt, brief cross-reference) — corroborates the
  ingestion-status claims above (Vulkan/SPIR-V vendored, DXIL/WGSL not).
- `docs/VISION.md` §2 (canned-output prohibition — the `readbackPixels` fix's rationale), §3.3
  (demand-driven growth / D7 — the six-target-matrix shrink's rationale).
- `docs/REVIEW.md` Law 2 (implementation completeness — the citation-obligation mechanism the
  matrix shrink must happen before triggering), Law 5 (stop-and-design), Law 9 (anti-pointwise —
  Spike 6's redefinition), Law 12 (connection theorem / single-source-of-truth spirit — the PNG
  theorem duplication).
- PLAN.md's "Graphics-plan pre-build validation" section — the research task that produced
  `GRAPHICS_PREBUILD_AUDIT.md`; already marked done there.

## Notes

- 2026-08-27: priority 8.3 — graphics doc rework is the direct fix for GRAPHICS_PREBUILD_AUDIT's top-10 findings and is the prerequisite for G2/G3/G4; owner is explicitly eager for graphics buildout.

_(none yet — first entries append here as work begins; Law-5-class, consolidate into the reworked
docs themselves — there is no separate design doc beyond the two files this task edits — and route
through design review before marking done.)_

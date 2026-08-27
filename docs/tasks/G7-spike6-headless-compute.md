---
id: G7
title: "Spike 6: headless parametric compute to PNG"
status: ready
blocked_on: ""
after: [G4, G5, G6, PA5]
related: []
bar: bar-4
track: graphics
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G7: Spike 6 — headless parametric compute to PNG

## Context

This is the first *implementation* task on the graphics track — a target-system
deliverable, not a design doc — and it is where G2 through G6's designs stop being paper
and become Lean code, assembly, and a running executable. It is sequenced
`after: [G4, G5, G6, PA5]`: G4 (differential harness) and G5 (SPIR-V validator) must exist
before any shader is emitted and checked; G6 (Vulkan host/capability model) must exist
before any GPU resource is allocated/bound/released under proof; PA5 (`canonicalizeTrace`:
causal-stamped normal form, input events as first-class trace events) must land because
this task's readback observation is exactly an *input event* in PA5's sense — the pixel
data returned from the device is data this program's contract must be parametric over, the
same way `read` is the universal binder for OS-level input (`docs/REVIEW.md` Law 9).
Notably, G3 (FP kernel DSL) is **not** a direct dependency edge for G7 in TASKS.md, but
G7's kernel must in practice be authored inside G3's Deterministic Shader Profile for its
determinism claim to be provable at all — treat G3's design as load-bearing context even
though the DAG routes the dependency through G5 (whose validator should itself depend on
G3, per G5's own file).

### The BAR-4 gate

TASKS.md states: "**BAR 4 — before G7 implementation: fresh-agent review of DSL designs +
harness.**" Per `docs/adr/0010-bar-triggered-deep-re-reviews.md` (read-only; owned by
another agent), **every BAR is a full-scope deep re-review of the entire codebase from
scratch, never a review scoped to the recent work that triggered it**: "The scope of a bar
review is always the entire codebase, never the recent work... Narrowing a bar to
're-review what just landed' is a process violation of this decision." Concretely for this
task: BAR 4's *trigger* is specifically that G2–G6's designs (and G4's harness design) have
landed and need fresh-eyes review before G7 implementation begins — but the review itself,
per ADR 0010, must cover drift between docs/laws and code reality anywhere in the tree,
whether the recently-merged graphics designs' claimed properties actually hold, new
findings ranked across the whole codebase, and an on/off-course verdict against PLAN.md —
not a narrowly-scoped audit of just the graphics DSL files. This task's `bar: bar-4` field
records that this full-scope review is a hard gate before any Lean/assembly for this task
is written; the review is not optional and not satisfied by a review of G2–G6's docs alone,
even though those docs are what makes the review timely now.

### The Law-9-compliant statement of what Spike 6 must prove

Audit §4 (read-binder / anti-pointwise mapping), quoted in full: "The GPU analog of `read`
is **input buffer/texture contents** plus device-reported limits. Spike 6 as specified
renders a fixed gradient with no input — its equivalence theorem is pointwise by
construction, satisfiable by a shader that stores a precomputed table (the Tier-1
pattern). Golden-image comparison is likewise pointwise and cannot count as verification.
Law 9-compliant statement: **for all input buffer contents b (within declared bounds), all
dispatch dimensions within advertised limits, all memory-model-permitted interleavings,
readback = specFn(b)** — with write-set race-freedom a discharged side condition and
`evalShader` differentially validated. Readback via staging copies is the input-chunking
dual and must be robust to arbitrary partial copies." This sentence is this task's actual
specification. Every clause is load-bearing:

- **"for all input buffer contents b (within declared bounds)"** — the kernel's contract
  is universally quantified over buffer contents, not instantiated at one fixed vector;
  this is what G1's redefinition of Spike 6 as parametric compute makes possible, and what
  the old fixed-gradient spec structurally could not satisfy.
- **"all dispatch dimensions within advertised limits"** — the device's reported
  `maxComputeWorkGroupCount`/`maxComputeWorkGroupSize` limits (and any other advertised
  limits relevant to this kernel) are themselves part of the domain quantified over, not a
  single hardcoded dispatch size.
- **"all memory-model-permitted interleavings"** — this is G2's synchronization DSL's
  domain: every interleaving G2's happens-before model permits must produce the same
  observable result, not merely the interleaving the implementation happens to schedule.
- **"readback = specFn(b)"** — the actual equivalence obligation: the bytes read back from
  the device must equal the pure Lean specification function applied to the input, closing
  exactly the gap the audit's top finding identifies (`GpuEvent.readbackPixels` carrying no
  payload) once G1's payload fix lands.
- **"write-set race-freedom a discharged side condition"** — race-freedom is not assumed;
  it is a proof obligation discharged via G2's DSL, feeding into this task's overall
  correctness argument as a named hypothesis, not folklore.
- **"`evalShader` differentially validated"** — this is G4's harness's job: the pure Lean
  `evalShader` function must itself be checked against lavapipe/SwiftShader before this
  task's equivalence theorem (which is a *statement about* `evalShader`, not about the
  physical GPU directly) can be trusted to say anything about reality.
- **"Readback via staging copies... robust to arbitrary partial copies"** — the audit
  names this "the input-chunking dual": Law 9 already requires OS-level reads to be proven
  correct under arbitrary chunking (`docs/REVIEW.md` Law 9's `read`-as-universal-binder
  clause); readback via a staging buffer is the same shape of problem on the output side,
  and this task must not assume the staging copy always completes in one shot.

### No performance contract — explicitly

Audit §5 states plainly: "**Recommendation: Spike 6 carries NO perf contract, explicitly,
until the timestamp/bandwidth harnesses are calibrated.**" This task must not claim, imply,
or gesture at a cost bound for the compute kernel, the upload, or the readback — that is
G8's job, and G8 is sequenced strictly after this task for exactly this reason (it also
needs F2's calibration-data governance to land first). If this task's design or
implementation discussion drifts toward "and this should be fast because..." language,
that is out of scope and should be flagged rather than written down as a contract.

### Contract trace vs. audit trace, concretely, for this task

Per `docs/EQUIVALENCE_PROOFS.md` §1.1 and G1's fix to `GpuEvent`: this task's **contract
trace** is exactly "PNG bytes on disk + exit code" (per G1's deliverables) — what leaves
the process. Device/resource events (`createDevice`, `createBuffer`, `createPipeline`,
`transitionLayout`, barrier events) are **audit trace**, attached to the Win-Vulkan target
typeclass instance per Law 8, and are not part of the cross-run equivalence obligation.
This task's equivalence proof ranges over the contract trace only; its Law-8 audited-
tracing obligation (that the real Vulkan/Win32 calls actually occur) is separate and is
proven against the audit trace.

## Deliverables & acceptance criteria

- A working, headless, Win-Vulkan-compute-only Spike 6 executable: dispatches a compute
  kernel authored inside G3's Deterministic Shader Profile, over an input buffer of
  arbitrary (bounds-declared) contents, reads the result back via staging copy, and writes
  a PNG (via `Stdlib/Png`, per `docs/GRAPHICS_ARCHITECTURE.md` §6/`docs/STDLIB_PNG.md`) to
  disk.
- A `VerifiedProgram`-shaped (or equivalent whole-program) contract stating exactly the
  Law-9-compliant claim quoted above: `∀ b (within declared bounds), ∀ dispatch dims
  (within advertised limits), ∀ memory-model-permitted interleavings ⇒ readback = specFn(b)`
  — with race-freedom and `evalShader` faithfulness as named, separately-discharged
  hypotheses (from G2 and G4 respectively), not folded silently into one monolithic proof.
- No pointwise fallback anywhere in the proof: confirm specifically that no code path
  instantiates the input buffer to a fixed vector to make the theorem provable (the "Tier-1
  pattern" the audit warns against by name), and that no golden-image byte-comparison
  stands in for the `readback = specFn(b)` obligation.
- The staging-copy readback proven robust to arbitrary partial copies — i.e., the
  contract must not assume the full buffer arrives in a single `vkCmdCopyBuffer`/host-map
  read; treat this the same way `docs/REVIEW.md` Law 9 treats `ReadFile`/`recv` chunking.
- Explicitly absent: any performance/cost claim about this kernel, its upload, or its
  readback. If a reviewer finds language suggesting a cost bound, that is a defect against
  this task's own scope, not a bonus.
- The contract-trace/audit-trace boundary respected exactly as G1 redefines it: the
  equivalence proof's observable set is PNG-bytes-plus-exit-code; device/resource events
  are audited (Law 8) but not equivalence-observable.
- **BAR 4 satisfied before implementation starts**: a fresh-agent, full-codebase deep
  re-review (per `docs/adr/0010`, not scoped narrowly to graphics) has run and reported its
  four required outputs (drift, claimed-outcomes check, ranked findings, on/off-course
  verdict) before this task's Lean/assembly is written. Record the review's completion
  (date, verdict) in this task's Notes once it happens — do not backfill or skip this gate.
- Per Law 13(4), since this task itself produces the differential evidence for downstream
  work: the G4 harness's five control vectors (positive, negative, device-loss,
  driver-absent, FP-divergence canary) must all be exercised against this task's actual
  emitted shader and dispatch, not merely against a hypothetical shape — this task is where
  G4's design gets its first real subject.

## Pointers

- `GRAPHICS_PREBUILD_AUDIT.md` §4 (read-binder/anti-pointwise mapping, quoted in full
  above), §5 (no perf contract until calibrated), §9 amendment #1 — read in full.
- `docs/tasks/G1-graphics-doc-rework.md` — the redefinition of Spike 6 as parametric
  compute and the `GpuEvent.readbackPixels` payload fix this task's implementation depends
  on having landed; also the contract/audit trace split.
- `docs/tasks/G2-synchronization-dsl.md`, `G3-fp-kernel-dsl.md`,
  `G4-gpu-differential-harness.md`, `G5-spirv-emitter-validator.md`,
  `G6-vulkan-host-model.md` — the five designs this task implements against; all five
  (G2–G6, i.e. every design task on this track except G8/G9) should be `design-review:
  approved` before this task's implementation work begins, per the BAR-4 gate above.
- `docs/adr/0010-bar-triggered-deep-re-reviews.md` (read-only) — the full-scope-review
  mandate governing what BAR 4 actually requires.
- `docs/EQUIVALENCE_PROOFS.md` §1.1 — the observation standard this task's contract/audit
  trace split must satisfy exactly.
- `docs/REVIEW.md` Law 8 (audited tracing for the device/resource audit trace), Law 9
  (universal quantification — the `read`-as-binder pattern this task's readback mirrors on
  the output side).
- `docs/STDLIB_PNG.md`, `docs/GRAPHICS_ARCHITECTURE.md` §6 — the existing verified PNG
  codec this task's output stage uses; note `STDLIB_PNG.md:10`'s stale "Spike 5" reference
  is fixed by G1, not this task.
- TASKS.md's PA5 entry ("canonicalizeTrace: causal-stamped normal form, input events as
  first-class trace events, coalescing per SYSTEM_EFFECTS §6 — after: PA2; needs OS1 for
  the input-event model") — this task's readback-as-input-event framing depends on PA5's
  normal form; consult PA5's own task file under `docs/tasks/` if it exists by the time
  this task is authored.
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing); this is the first task
  that actually populates `Gasm/Targets/*` for the graphics path, following whatever module
  naming G1's housekeeping pass and G2/G3/G5's designs settle on.

## Notes

- 2026-08-27: priority 7.5 — Spike 6 (headless parametric compute to PNG) triggers BAR 4 and is the first real graphics-track end-to-end exercise; owner-prioritized track.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.
Additionally: BAR 4's full-codebase re-review completion must be recorded here, with date
and verdict, before implementation work proceeds — see Deliverables above.)_

---
id: G4
title: GPU differential-validation harness design
status: ready
blocked_on: ""
after: [G1]
related: []
bar: ""
track: graphics
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G4: GPU differential-validation harness design

## Context

`GRAPHICS_PREBUILD_AUDIT.md` §3 states plainly: differential validation is **"absent from
the docs"** entirely. `docs/VISION.md` §3.2 already commits the project to differential
validation of every machine/OS model against reality ("Graphics API and shader models
(future): the same differential discipline against real drivers and reference
rasterizers/executors") — this task is where that commitment becomes a concrete design for
the graphics path, before Spike 6 has anything to validate against. It is sequenced
`after: [G1]` only, in parallel with G2/G3, since the harness design does not itself depend
on the sync or FP-determinism DSLs being finished (though the FP-canary control below
depends on G3's profile existing to define what "float-controls honored" means precisely —
this task should design the canary's shape and defer its exact vector to G3's profile
definition landing).

### The two axes and the oracle stack

Audit §3: "Two axes: model faithfulness and artifact validity." Model faithfulness asks
whether `evalShader` (the pure Lean spec) agrees with what real hardware/drivers produce;
artifact validity asks whether the emitted SPIR-V module itself is well-formed per the
Khronos grammar (this second axis is G5's job — see below for the boundary). Oracles, per
audit §3: **"SwiftShader/lavapipe (deterministic CPU reference) primary; real GPUs as
cross-vendor divergence detectors; SPIRV-Tools... WARP for DX12; naga/Tint/wgpu for
WGSL."**

### Scope cut: this task designs for Win-Vulkan-compute only

G1 shrinks the six-target matrix to Win-Vulkan-compute (audit §9 amendment #5, §8 D7
violation finding). This task must design the harness **for that one target only** — WARP
(DX12), naga/Tint/wgpu (WGSL) are named by the audit as part of the oracle landscape for
targets G1 has explicitly deferred to a non-obligating "possible futures" appendix.
Designing this harness against DX12/WGSL oracles now would silently re-widen the scope G1
just cut, recreating the exact D7 bulk-import failure mode the audit flagged. State this
cut explicitly in the design doc: **lavapipe (or SwiftShader) is the in-scope oracle for
this task; WARP and naga/Tint/wgpu are out of scope until their respective target docs
(`DXIL_D3D12.md`, `WGSL_WEBGPU.md`) exist and are ingested per Law 4/Law 5**, matching
MODEL_DEBT.md §D's explicit statement that DXIL/DXBC and WGSL references are not vendored.

### Mandatory controls (Law 13)

Audit §3, quoted in full: "Law 13 controls: positive (known dispatch), negative (malformed
modules MUST be reported as rejection, not laundered — the V8 INVALID/TRAP lesson),
device-loss control, **driver-absent aborts the run**, and an **FP-divergence canary** (a
vector that differs when float-controls are not honored). Except-typed outcomes
throughout." Each of these is mandatory, per `docs/REVIEW.md` Law 13(4): "for harnesses
that interact with the world (hardware, engines, OS) and therefore cannot be theorems:
mandatory positive and negative control vectors at the start of every session... An oracle
that cannot run must fail the run; it must never no-op, skip, or synthesize results."

### The V8 INVALID/TRAP lesson — why this must not be re-learned here

The "V8 INVALID/TRAP lesson" refers to this project's own prior finding (documented in
PLAN.md's Wasm-fuzzer history): a Wasm differential fuzzer that, when it encountered
invalid or trapping module inputs, silently treated the case as a pass rather than as a
rejection that must be validated as a rejection — a fail-open bug in the harness itself,
not in the thing being validated. The audit's citation of this lesson for the GPU harness
is a direct warning that the same shape of bug — treating "the driver rejected this
malformed module" as equivalent to "no divergence found" instead of as a distinct outcome
that must itself be checked for correctness — must not recur here. This task's negative
control (malformed SPIR-V module dispatched to lavapipe) exists specifically to catch this:
the harness must assert the *rejection itself* happened and was reported as such, not
merely that the run didn't crash.

### Except-typed outcomes

Every harness invocation returns one of a small closed set of outcomes — success with
readback data, validated rejection (negative case), device-loss, driver-absent-abort — as
an `Except`-shaped Lean type, per audit §3's "Except-typed outcomes throughout." Per Law
13(4)'s preference-order item 4: "oracle outcomes as an `Except` that no code path can
synthesize" is the ∀-shaped mechanization the audit is asking for here — the harness's
result type itself should make "silently passed" unrepresentable, not merely
discourage it by convention.

## Deliverables & acceptance criteria

- A design document specifying the harness's oracle stack (lavapipe/SwiftShader primary,
  real GPUs as divergence detectors, explicitly scoped to Win-Vulkan-compute per the cut
  above), its invocation protocol (how a candidate dispatch + input buffer + expected
  `specFn` result get run against the oracle and compared), and its `Except`-typed result
  type covering at minimum: `.ok readbackBytes`, `.rejected reason` (for negative controls),
  `.deviceLoss`, and `.driverAbsent` (which must abort the run per Law 13, not be silently
  swallowed).
- All five Law-13 controls designed concretely, not just named: (1) positive control — a
  known-good dispatch with a hand-checkable expected result; (2) negative control — a
  malformed SPIR-V module (e.g. missing required capability declaration, or a structurally
  invalid merge block) that lavapipe must reject, with the harness asserting the rejection
  occurred and was correctly classified, not merely that no crash occurred (the V8
  INVALID/TRAP lesson, applied); (3) device-loss control — a scenario forcing
  `VK_ERROR_DEVICE_LOST` and asserting the harness surfaces it rather than hanging or
  reporting false success; (4) driver-absent control — asserting the harness aborts the
  entire run (not a single test) when no Vulkan-capable driver/lavapipe is found; (5)
  FP-divergence canary — a kernel and input vector chosen so that its result differs
  observably between float-controls-honored and float-controls-ignored execution, so the
  canary proves G3's profile preconditions are actually load-bearing on this oracle.
- A stated boundary with G5: this task validates model faithfulness (does the shader
  compute the right answer); G5 validates artifact validity (is the emitted SPIR-V
  well-formed per the grammar) via a build-time Lean validator, with `spirv-val` demoted to
  an external cross-check consumed by *this* harness as one of several oracles, not as the
  primary gate (that primary role moves to G5's Lean validator per audit §9 amendment #7).
  State this boundary explicitly so a future author does not duplicate validator logic
  across G4 and G5.
- Per Law 13(4)'s general mandate, restated here as this task's own acceptance bar: the
  harness's design must make "the oracle didn't run, but the test reported pass" and "the
  oracle rejected the input, but the harness reported no divergence" both unrepresentable
  in the result type, not merely tested against by convention.
- Law-5/Law-13 discipline: design doc authored, then routed through fresh-agent design
  review before `design_review` is marked approved and before any Lean cites it.

## Pointers

- `GRAPHICS_PREBUILD_AUDIT.md` §3 in full (differential validation), §9 ranked amendment #6
  — read in full; this task's Context section quotes but does not exhaust it.
- `docs/VISION.md` §3.2 (differential validation as a first-class, permanent obligation for
  every model, explicitly including future graphics/shader models) and §3.3
  (demand-driven growth — the reason WARP/naga/Tint/wgpu are named as future oracles but
  out of scope for this task specifically).
- `docs/REVIEW.md` Law 13 in full, especially the preference-order list and "An oracle that
  cannot run must fail the run; it must never no-op, skip, or synthesize results."
- MODEL_DEBT.md §D — corroborates the DXIL/WGSL reference-ingestion gap that scopes this
  task to lavapipe/Vulkan only.
- PLAN.md — search for the Wasm differential-fuzzer / V8 INVALID-TRAP finding history that
  motivates the negative-control design above (the exact section title may have shifted
  since this task file was authored; confirm the current location when writing the design
  doc rather than citing a line number that may drift).
- G3's file (`docs/tasks/G3-fp-kernel-dsl.md`) — the FP-divergence canary's exact vector
  depends on G3's Deterministic Shader Profile grammar; this task should design the
  canary's *shape* (a differing-result vector under a controlled float-controls flag) and
  leave the concrete vector's derivation to whichever task lands second between G3 and G4's
  implementation.
- G5's file (`docs/tasks/G5-spirv-emitter-validator.md`) — the model-faithfulness /
  artifact-validity boundary this task must respect.
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing), so this design targets a future harness
  module under `Gasm/Targets/*` or a sibling test-harness location, name TBD during
  authoring, following whatever convention the CPU-side hardware fuzz harness
  (`HardwareHarness.lean`, referenced in MODEL_DEBT.md §A7) already establishes for
  differential harnesses in this repo.

## Notes

- 2026-08-27: priority 7.0 — GPU differential-validation harness design is required before G7 (Spike 6) can have any oracle at all.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_

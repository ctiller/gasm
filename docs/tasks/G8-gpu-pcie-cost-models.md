---
id: G8
title: GPU/PCIe cost models + calibration
status: ready
blocked_on: ""
after: [G7, F2]
related: [F5]
bar: ""
track: graphics
priority: 6.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G8: GPU/PCIe cost models + calibration

## Context

This task closes the gap G7 explicitly leaves open: audit §5's recommendation
("**Spike 6 carries NO perf contract, explicitly, until the timestamp/bandwidth harnesses
are calibrated**") means G7 ships a correctness-only Spike 6, and this task is where a
performance contract becomes possible for the first time on the graphics path. It is
sequenced `after: [G7, F2]`: `after: G7` because a cost model needs a real, working
compute-to-readback pipeline to measure against — modeling the cost of a pipeline that does
not yet exist and has not been differentially validated for correctness would repeat the
exact mistake `docs/VISION.md` §3.3 warns against (building on an unvalidated increment);
`after: F2` because F2 (calibration-data governance, MODEL_DEBT §E5) is the policy this
task's own measured numbers must be governed by, and MODEL_DEBT §E5 states plainly that
skipping this governance is how the predecessor project's `wsc` died: "wsc died of exactly
this — RDTSC medians hand-transcribed as `Nat` literals and left to rot." F2 had not yet
been written as a standalone `docs/tasks/` file at the time this task was authored; consult
it directly if it exists by the time this task is picked up, and otherwise treat
MODEL_DEBT.md §E5 (quoted below) as F2's substantive content.

### The two forcing documents, quoted directly

**MODEL_DEBT.md §E1** (PCIe / interconnect transfer model), quoted in full: "`Gasm/Targets/`
contains four targets (X86_64, Wasm, WASI, Windows). There is no device, no bus, no
transfer. Nothing models: per-direction bandwidth, per-transfer fixed latency,
**host→device vs device→host asymmetry** (the readback penalty that decides most offload
questions), pinned vs pageable staging cost, submission/doorbell overhead, or batching
amortization (N small transfers vs one coalesced). Without these, 'CPU vs GPU including
readback' is not expressible even in principle — a GPU kernel cost alone always wins.
**Forcing function**: Spike 6 pixel readback is literally a device→host transfer; the debt
lands the moment Spike 6 has a cost contract. **Validation**: a transfer-size sweep (64 B →
256 MB, both directions, pinned and pageable) as a differential oracle; fit latency +
inverse-bandwidth coefficients; oracle must fail closed when no device is present (Law 13
control-vector rules — a missing GPU must abort the run, never silently pass)." This task
*is* the moment G7's Spike 6 gets a cost contract — the forcing function has now arrived.

**MODEL_DEBT.md §E2** (no composable cost views between CPU and GPU), quoted in full:
"`PerfCycleBounds` (`Uop.lean:132-136`) is `Nat` cycles under an implicitly single, unnamed
clock. Cycles are not comparable across devices: a GPU 'cycle' is a different clock at a
different width, and both are unstable under turbo/DVFS. **Ratified design (Craig
2026-08-27, VISION §5): layered views that COMPOSE, not one flattened unit.** Each system
keeps its native precision view as first-class (cycle counts for x86 — valuable, keep them;
device ticks for GPU; latency+bandwidth terms for transports); a **system-architect view in
µs/ms** is derived through explicit conversions owned by named device profiles (profile
carries clock/frequency provenance). Placement decisions compare `t_cpu(N)` vs `t_h2d(bytes)
+ t_gpu(N) + t_d2h(bytes)` at the architect level; within-domain optimization keeps native
units. The composition (validated conversions) is the contract." `docs/VISION.md` §5's own
language for this is the layered-views-that-compose design: "**Native precision views per
system**... **The system-architect view**... **Composition is the contract.**" This task's
central deliverable is exactly that composition layer for CPU↔GPU, plus the PCIe transfer
terms E1 asks for.

### Cost shape to build toward

Audit §5: "Cost shape making placement computable: `cost_gpu(N) = upload(N) + dispatch(N) +
readback(N)` in nanoseconds under a named device profile, comparable to `cost_cpu(N)` via
the CPU profile's clock." This is the concrete target function this task's design doc must
define precisely — each of `upload`, `dispatch`, `readback` as its own closed-form term
(per `docs/VISION.md` §5's "parametric cost functions, not asymptotics" mandate, applied
here to the GPU/transport domain the way F4 applies it to the CPU domain), with the whole
sum comparable to a CPU-side cost under the paired-profile composition E2 describes.

### Calibration governance (F2 / MODEL_DEBT §E5)

MODEL_DEBT.md §E5, quoted in full: "Law 4 governs *vendored authoritative text*. Every
Section E entry, and TOP-10 item 5, produces something Law 4 has no category for:
**measured numbers from this machine**. wsc died of exactly this... Proposed position:
calibration is a *third* reference class — checked in, machine-readable, `references/`-
style, with (a) named device/profile identity and provenance (host, frequency policy, OS
build, date), (b) the regenerating harness committed alongside so the data is reproducible
rather than transcribed, (c) staleness surfaced mechanically (a gate failing when data
predates its harness or names a profile the build doesn't define), (d) a hard prohibition
on hand-editing a calibration value. Model coefficients then *cite* calibration files the
way semantics cite the SDM. Without this, every Section E model becomes a second wsc." This
task's GPU/PCIe calibration data (bandwidth-sweep fits, timestamp-query coefficients, named
device profiles) must be produced and governed exactly this way — this is the concrete
reason `after: F2` is a real dependency, not a formality: authoring GPU calibration data
before F2's governance policy exists risks producing exactly the second-wsc outcome §E5
warns against.

### Occupancy caveat

Audit §5 also notes: "Occupancy/coalescing/divergence make GPU body-cost far less
predictable than a uop model — first version deliberately coarse, validated for monotone
faithfulness only." This task's `dispatch(N)` term should not attempt cycle-exact GPU
kernel cost modeling in its first version; per `docs/VISION.md` §5's monotone-faithfulness
standard ("when the model ranks variant A faster than variant B, real hardware must
overwhelmingly agree"), a coarse model validated for rank-order agreement is the acceptable
first target, matching how the CPU-side perf model is held to the same monotone-faithfulness
bar rather than cycle-exactness.

## Deliverables & acceptance criteria

- A design document defining `cost_gpu(N) = upload(N) + dispatch(N) + readback(N)` with
  each term as an explicit closed-form function under a named device profile: `upload`/
  `readback` as PCIe transfer terms (latency + inverse-bandwidth, separately fit for
  host→device and device→host given the audit/MODEL_DEBT's explicit asymmetry point), and
  `dispatch` as a deliberately coarse, monotone-faithfulness-validated GPU kernel cost term
  (not claiming cycle-exactness, per the occupancy caveat above).
- The layered-views composition per MODEL_DEBT §E2/`docs/VISION.md` §5: native-precision
  views preserved (x86 cycles unchanged; GPU device ticks or equivalent native unit kept
  first-class; transport terms in latency+bandwidth), with an explicit, validated
  conversion into a shared system-architect µs/ms view, so that `cost_cpu(N)` and
  `cost_gpu(N)` (inclusive of upload/readback) become comparable at the architect level
  without discarding native precision anywhere.
- A calibration-data plan conforming to F2/MODEL_DEBT §E5's four governance properties:
  named device/profile identity with provenance (host, frequency policy, OS build, date);
  the regenerating harness (transfer-size sweep, 64 B–256 MB, both directions, pinned and
  pageable, per audit §5/MODEL_DEBT §E1) committed alongside the data it produces; a
  mechanical staleness check (data predating its harness, or naming an undefined profile,
  fails the build); and a hard prohibition on hand-editing calibration values enforced
  however F2 specifies (a linter, a checked file format, or equivalent).
- The missing-device control vector from MODEL_DEBT §E1, restated as this task's own
  acceptance criterion: the calibration harness "must fail closed when no device is
  present (Law 13 control-vector rules — a missing GPU must abort the run, never silently
  pass)" — verify this is actually the case in the harness design, not merely asserted.
- Explicit acknowledgment that this task's `dispatch(N)` term is a first, coarse version,
  validated only for rank-order/monotone faithfulness (per `docs/VISION.md` §5), not
  cycle-exactness — state this in the design doc so a future reviewer does not mistake the
  first version for a precision claim it does not make.
- Per Law 13(4): state the differential evidence this design's own claims need — the
  transfer-size sweep itself (per MODEL_DEBT §E1) is the primary oracle; in addition, a
  monotone-faithfulness check comparing the model's ranking of at least two GPU kernel
  variants (e.g. differing dispatch dimensions) against real measured timestamps, matching
  the CPU-side perf model's own monotone-faithfulness validation standard.
- Law-5/Law-13 discipline: design doc authored, then routed through fresh-agent design
  review before `design_review` is marked approved and before any Lean/calibration data
  cites it.

## Pointers

- `GRAPHICS_PREBUILD_AUDIT.md` §5 in full (performance model + placement queries), §9
  ranked amendment #9 — read in full.
- MODEL_DEBT.md §E1 (PCIe/interconnect transfer model, quoted in full above), §E2 (no
  composable cost views, quoted in full above), §E5 (calibration-data governance, quoted in
  full above) — this task's three core sources; also §D (graphics-forward debt, brief
  cross-reference) and the TOP-10 PRIORITY TABLE's item 5 (uncited coefficients — the same
  Law-4-gap argument E5 makes for calibration data specifically).
- `docs/VISION.md` §5 in full (Performance Modeling: Agents as the Optimizing Compiler,
  including the "layered views that compose" design language quoted above and the
  monotone-faithfulness standard) — this task instantiates §5's device/transport extension
  directly.
- `Gasm/Targets/X86_64/Uop.lean:132-136` (`PerfCycleBounds` — grep this path to confirm the
  current line range before citing exactly, since MODEL_DEBT's line numbers are dated to
  its audit day) — the existing single-clock CPU-only cost representation this task's
  composition layer must extend without discarding.
- TASKS.md's F2 entry ("calibration-data governance (MODEL_DEBT E5...) — after: — (ready
  now; policy/design)") and F1/F3/F5 entries (RDTSC harness, staged calibration, composable
  cost views) — this task is the GPU-domain sibling of F5 (composable cost views) and
  should stay consistent with whatever F5 lands with on the CPU side rather than diverging.
  Consult F2's own `docs/tasks/` file if it exists by the time this task is authored;
  otherwise MODEL_DEBT §E5 (quoted above) is treated as F2's substantive content.
- `docs/tasks/G7-spike6-headless-compute.md` — the Spike 6 pipeline this task's cost model
  measures; G7 explicitly ships with no performance contract, which is what makes this task
  necessary and not redundant.
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing); this design targets a future
  cost-model extension under `Gasm/Targets/*` (GPU/transport profile) plus whatever shared
  cost-composition module F5 establishes on the CPU side.

## Notes

- 2026-08-27: priority 6.5 — GPU/PCIe cost models + calibration is graphics-track cost work, gated on G7 landing and F2's calibration governance.
- 2026-08-27: related: [F5] — G8's GPU/PCIe cost models are the graphics-track instance of exactly the CPU/GPU composable-cost-view abstraction F5 is building generally (MODEL_DEBT E2, 'prerequisite for all placement questions'); G8 should consume F5's layered-views design rather than inventing its own unit system.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_

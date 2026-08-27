---
id: F5
title: Composable cost views (native precision + µs/ms architect view + validated conversions)
status: ready
blocked_on: ""
after: [F3]
related: []
bar: ""
track: perf
priority: 7.3
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# F5: Composable cost views (native precision + µs/ms architect view + validated conversions)

## Context

This task is the second half of `docs/VISION.md` §5's thesis — where F4 makes concrete *what a cost
function looks like* (a parametric polynomial on a routine contract), this task makes concrete *how
costs expressed in different native units get compared to each other* across CPU, GPU, and transport
domains. It directly implements MODEL_DEBT §E2, which is the entry MODEL_DEBT itself flags as having
the widest blast radius in the entire ledger ("E2 and E5 have the widest blast radius: E2 is
prerequisite for every placement question").

### VISION §5's layered-views passage, quoted in full

> **From optimizing compiler to optimizing system architect.** The end-state cost model spans
> devices and transports — CPU compute, GPU compute, **PCIe transfer cost including readback**, disk
> I/O, network — organized as **layered views that compose, not one flattened unit system**:
>
> - **Native precision views per system**: each domain keeps its own most-precise natural unit as a
>   first-class model — cycle counts for x86 (valuable and measurable there), device ticks for GPU
>   timestamps, bytes-and-latency terms for transports. Precision lives at the leaves and is never
>   thrown away by premature conversion.
> - **The system-architect view**: microseconds/milliseconds per operation, obtained from the native
>   views through *explicit conversions* carried by named device profiles (a profile owns its
>   clock/frequency provenance). Placement questions — "CPU or GPU, counting upload and readback?",
>   "recompute or spill to disk?", "local or remote?" — are asked and answered at this level, by
>   comparing closed-form parametric cost functions whose terms were converted from the native views.
> - **Composition is the contract.** The requirement is not that all costs share a unit; it is that
>   every native view composes into the architect view through a validated conversion, so
>   cross-domain comparisons are always well-defined while within-domain reasoning keeps full native
>   precision.
>
> Each device/transport model is differentially validated like the CPU model (timestamp queries,
> bandwidth benchmarks, under the same control-vector rules); measured calibration data is governed
> like `references/` — checked in, regenerable, never hand-edited.

### MODEL_DEBT §E2, quoted in full — the same design, from the debt-ledger side

> **E2. No composable cost views between CPU and GPU — the central missing abstraction.**
> `PerfCycleBounds` (`Uop.lean:132-136`) is `Nat` cycles under an implicitly single, unnamed clock.
> Cycles are not comparable across devices: a GPU "cycle" is a different clock at a different width,
> and both are unstable under turbo/DVFS. **Ratified design (Craig 2026-08-27, VISION §5): layered
> views that COMPOSE, not one flattened unit.** Each system keeps its native precision view as
> first-class (cycle counts for x86 — valuable, keep them; device ticks for GPU; latency+bandwidth
> terms for transports); a **system-architect view in µs/ms** is derived through explicit conversions
> owned by named device profiles (profile carries clock/frequency provenance). Placement decisions
> compare `t_cpu(N)` vs `t_h2d(bytes) + t_gpu(N) + t_d2h(bytes)` at the architect level; within-domain
> optimization keeps native units. The composition (validated conversions) is the contract. This
> still forces the frequency/turbo gap (A5) closed — the cycles→time conversion is exactly what A5
> blocks — but does NOT demote cycles to a derived unit. Cost: conversion layer is small; the
> honesty burden (which profile, which frequency, measured how — see E5) is the real work.

Two design pressures are worth naming explicitly because they are easy to get backwards:

1. **This is not "pick one universal unit and convert everything into it."** VISION and MODEL_DEBT
   both explicitly reject unifying on a single flattened unit (µs everywhere, say) — `PerfCycleBounds`
   staying in cycles is a *feature*, not debt to eliminate, because within-domain reasoning (comparing
   two x86 variants) is more precise and more directly measurable in native cycles than after a lossy
   round-trip through wall-clock time. The deliverable is a *conversion layer* that sits alongside the
   native views, not a replacement for them.
2. **The conversion itself needs to be a validated, honest thing**, not a hardcoded multiply-by-clock-
   frequency constant. MODEL_DEBT's own note ("the honesty burden — which profile, which frequency,
   measured how — see E5 — is the real work") flags that the small amount of actual conversion-formula
   code is not where this task's difficulty lives; the difficulty is in making the conversion's inputs
   (a named device profile's clock/frequency provenance) themselves calibration data governed by F2,
   so that "convert 1200 cycles to microseconds" is answerable honestly rather than by an assumed
   constant frequency that silently goes stale under turbo/DVFS — which is exactly what MODEL_DEBT
   §A5 already flags as unmodeled ("Turbo/frequency and TLB are absent"). This task is explicitly
   named as the thing that "forces the frequency/turbo gap (A5) closed" — i.e. F5 cannot honestly
   build the cycles→time conversion without also confronting A5's absent frequency model, even though
   A5 itself is not separately staged in F3's four-stage list. State in the design doc how much of A5
   this task actually needs to resolve (likely: enough to state a named profile's assumed/measured
   operating frequency with honest provenance, not necessarily a full turbo-state model).

### Why this depends only on F3, not F1/F2 directly

TASKS.md lists F5's dependency as `after: [F3]` only. This makes sense: F5 needs the *calibrated* CPU
native-precision view (cycles, from F3) to exist so the conversion layer has something real to
convert from, but F5 does not itself need F1's harness directly (it is not measuring new hardware
behavior, it is building the honest bridge between an already-measured native view and an
architect-level view) — though in practice F5's conversion-formula validation (see Deliverables
below) will likely reuse F1's harness machinery to timestamp wall-clock durations for cross-checking,
and its calibration-data outputs (named device profiles' frequency provenance) must go through F2's
governance mechanism regardless of the formal dependency edge. Treat F1/F2 as practically necessary
even though TASKS.md's DAG does not draw a hard edge from them.

## Deliverables & acceptance criteria

- A design doc (Law 5; Law-5-class performance-model work) specifying: the native-precision view
  representation for each domain currently in scope (x86 cycles — already `PerfCycleBounds`,
  `Uop.lean:132-136`; GPU device ticks and transport bytes/latency terms are aspirational pending
  G-track/E-track work and should be scoped as "the conversion layer's shape must accommodate these
  later" rather than fully built now, since G8/E1-E4 are not this task's scope); the system-architect
  view (µs/ms); and the explicit conversion function(s) between them, each owned by a named device
  profile carrying its own clock/frequency provenance.
- The conversion's frequency/clock inputs must be calibration data governed by F2 (named
  device/profile identity, provenance, regenerating harness, staleness detection, no hand-editing) —
  not a bare literal constant multiplied into a cycle count. This is the direct application of F2's
  mechanism to a second consumer beyond F3, and is good evidence F2's design generalizes rather than
  being special-cased to F3's needs.
- A "validated conversion" demonstration: show that converting a calibrated native-cycle cost (from
  F3's corrected model) through this task's conversion layer into µs/ms, and comparing against a
  directly-measured wall-clock duration for the same kernel (via F1's harness or an equivalent
  wall-clock timing path), agrees within a stated, justified tolerance — this is this task's version
  of F1/F3's containment criterion, applied to the conversion layer rather than the underlying cycle
  model.
- At least one worked placement-question example using the architect view as VISION/§E2 describe —
  even a deliberately simple one (e.g. compare two CPU-only variants' architect-view costs, since
  GPU/transport native views are out of scope for this task) demonstrating that "composition is the
  contract": the architect-level comparison is well-defined and traces back through explicit,
  validated conversions to each side's native view, not to a shared unit chosen for convenience.
- Explicitly do NOT demote `PerfCycleBounds`/cycle-count reasoning to a derived unit anywhere in
  within-domain (CPU-only) optimization code paths — native precision must remain first-class and
  directly usable, per VISION's explicit instruction ("does NOT demote cycles to a derived unit").
- State clearly in the design doc's scope section what this task does NOT build (a GPU device-tick
  native view, a PCIe transfer model, a disk/network native view — these are MODEL_DEBT §E1/E3/E4 and
  G-track work, explicitly gated separately in TASKS.md, e.g. `G8 ... after: G7, F2`) so a fresh
  reader does not mistake this task for the full cross-device cost model.

## Pointers

- `docs/VISION.md` §5, "From optimizing compiler to optimizing system architect" (quoted in full
  above) — this task's direct thesis statement.
- `MODEL_DEBT.md` §E2 (quoted in full above), §A5 (frequency/turbo absence this task's conversion
  layer forces a confrontation with — quoted in F3's task file), §E5 (calibration governance the
  conversion's frequency inputs must go through), TOP-10 table and target-class tag table's E2 row
  ("**prerequisite for all placement questions**").
- `Gasm/Targets/X86_64/Uop.lean:132-136` (`PerfCycleBounds` — the existing native-precision cycle view
  this task's conversion layer wraps, not replaces).
- `Gasm/Targets/X86_64/Performance.lean:76-96` (`computeCycleBounds` — produces the native-cycle
  values this task converts).
- `docs/tasks/F3-staged-model-calibration.md` (this task's direct dependency — the calibrated model
  supplying real native-cycle values to convert).
- `docs/tasks/F2-calibration-data-governance.md` (governs this task's device-profile frequency
  provenance data, even though not a formal TASKS.md dependency edge).
- `docs/tasks/F1-rdtsc-harness.md` (likely reused for wall-clock cross-checking during this task's
  conversion validation, even though not a formal dependency edge).
- `docs/adr/0006-performance-model-as-strategic-asset.md` (D5).

## Notes

- 2026-08-27: priority 7.3 — MODEL_DEBT E2: composable cost views are the 'prerequisite for all placement questions' (CPU vs GPU including readback) — second-widest blast radius in the supplement after E5/F2.

_(none yet — first entries append here as work begins; this is Law-5-class performance-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_

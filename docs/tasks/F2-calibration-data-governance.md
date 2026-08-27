---
id: F2
title: Calibration-data governance (MODEL_DEBT E5 — the third reference class)
status: designing
blocked_on: ""
after: []
related: []
bar: ""
track: perf
priority: 8.3
priority_set: 2026-08-27T18:25:47Z
design: "docs/CALIBRATION_GOVERNANCE.md"
design_review: "redesign 2026-08-27"
date: 2026-08-27
---

# F2: Calibration-data governance (MODEL_DEBT E5 — the third reference class)

## Context

This task establishes a policy/governance mechanism, not a model or a proof. It is ready now
(`after: []` in TASKS.md) precisely because it has no code dependency — but it gates a large amount
of downstream work: F3's staged calibration, F4/F5's cost functions, and MODEL_DEBT §G8 (GPU/PCIe
cost models) all either consume calibration data directly or are explicitly listed in TASKS.md as
gated on F2 (`G8 ... after: G7, F2`). Getting this wrong, or late, means every one of those tasks
either invents its own ad-hoc storage convention or repeats the exact mistake this task exists to
prevent.

### The MODEL_DEBT §E5 finding, in full

MODEL_DEBT.md's supplement section E is titled "SYSTEM-LEVEL TRANSPORT & PLACEMENT COST MODELS" and
its final entry, E5, is short, precise, and is this task's entire substance. Quoted verbatim:

> **E5. Governance of measured calibration data under Law 4 — an open policy gap; resolve first.**
> Law 4 governs *vendored authoritative text*. Every Section E entry, and TOP-10 item 5, produces
> something Law 4 has no category for: **measured numbers from this machine**. wsc died of exactly
> this — RDTSC medians hand-transcribed as `Nat` literals and left to rot. Proposed position:
> calibration is a *third* reference class — checked in, machine-readable, `references/`-style,
> with (a) named device/profile identity and provenance (host, frequency policy, OS build, date),
> (b) the regenerating harness committed alongside so the data is reproducible rather than
> transcribed, (c) staleness surfaced mechanically (a gate failing when data predates its harness or
> names a profile the build doesn't define), (d) a hard prohibition on hand-editing a calibration
> value. Model coefficients then *cite* calibration files the way semantics cite the SDM. Without
> this, every Section E model becomes a second wsc.

Read this literally as four separate deliverables — (a) through (d) are each a distinct mechanism,
not four descriptions of one thing, and each needs its own concrete design:

- **(a) Identity and provenance.** A calibration file must name which physical machine, CPU
  microarchitecture, frequency-governor/turbo policy, OS build, and date produced it. This is what
  lets a future reader (or an automated staleness check) distinguish "this number describes the
  i9-13900H this repo has been measured on" from "this number describes something else entirely" —
  directly answering the gaps-register concern (quoted in F3's task file, and below) that all
  hardware truth currently comes from exactly one machine.
- **(b) The regenerating harness committed alongside the data.** This is the single most important
  clause and the direct fix for wsc's failure: wsc's numbers were hand-transcribed *from* a harness
  that was never checked in next to them, so nobody could re-run it to check the numbers still held.
  Every calibration file this task's mechanism produces must ship with (or point unambiguously to) the
  exact harness invocation that regenerates it — F1's `PerfHardwareFuzzer`/`--hardware` CLI mode is
  the first concrete instance of such a harness, but this governance mechanism must be general enough
  to also cover F3's staged calibration outputs and, eventually, MODEL_DEBT §E1-E4's PCIe/storage/
  network calibration sweeps.
- **(c) Mechanical staleness detection.** A gate — not a convention, not a comment, not a README note
  — that fails when a calibration file predates the harness that produced it (harness changed since
  the data was last regenerated) or names a microarchitecture profile the current build doesn't even
  define (e.g. a calibration file for a `zen4Profile` that got renamed or removed from `Uop.lean`).
  This is exactly the kind of mechanical prevention Law 13 demands: a reviewer noticing stale
  calibration data by inspection is evidence of a missing gate, not a working process.
- **(d) Hard prohibition on hand-editing.** Structurally prevent a human or agent from opening a
  calibration file and typing in a new number by hand — the file's format and its consuming tooling
  should make a hand-edited value either mechanically detectable (e.g. a checksum or signature over
  the regeneration inputs) or simply not something an editor can produce a plausible-looking value
  for without actually running the harness.

### Why this is a *third* reference class, not an extension of Law 4

`docs/REVIEW.md` Law 4 states:

> **Official reference documentation (e.g. Intel/AMD ISA manuals, Microsoft PE/COFF specification,
> Windows Win32 API contracts) must be brought into the repository directly as authoritative
> sources.** We do NOT author or synthesize ad-hoc approximations of hardware manuals or external OS
> specifications; that is a massive cheat. Authentic, authoritative reference texts must be
> imported/vendored directly into the repository so that formal models cite genuine ground truth.

Law 4 as written is about *vendoring third-party authoritative text* — Intel manuals, Win32
contracts, RFCs. Calibration data is neither authored by this project (that would be "invention," the
thing Law 4 exists to forbid) nor a vendored external document (nobody publishes "the RDTSC median for
this exact instruction sequence on this exact CPU") — it is **measured by this project, from this
project's own harnesses, against real hardware this project owns.** MODEL_DEBT explicitly proposes
treating it as "a *third* reference class" alongside (1) vendored external references and (2)
first-party model/spec text — sharing Law 4's spirit (checked-in, machine-readable, cited by the
things that depend on it) while needing its own rules for provenance and regeneration that vendored
static text does not need (a vendored SDM PDF doesn't go stale in the way a measurement taken on a
specific CPU under a specific turbo policy does). This task's job is to write that rule down as a
concrete, checkable mechanism — most naturally as a `docs/` design doc plus whatever
`scripts/`-level tooling enforces (c) and (d), landing in a `references/`-adjacent or dedicated
`calibration/`-style location so it inherits the same "checked-in, not ad-hoc" discipline Law 6
(Reference Reproducibility Mandate) already establishes for `references/` proper.

### Licensing check — a small but explicit sub-deliverable

TASKS.md's F2 line and PLAN.md's gaps register both call out a distinct, smaller concern:
"licensing check for external tables." PLAN.md's gaps register states it as its own line item:

> Small: calibration-source licensing check before vendoring (Agner Fog/uops.info redistribution
> vs Law 4; prune/advance stale `master`/`owner` branches...

If F3's later calibration work wants to *cite* published latency/throughput tables (Agner Fog's
instruction tables, uops.info) as corroborating evidence for measured coefficients — MODEL_DEBT §A8
explicitly names both sources as the kind of reference the project currently lacks — this task should
resolve, in advance, whether and how those specific external tables may be redistributed/vendored
under Law 4's "bring it in directly" model, since their licenses are not obviously as permissive as an
official vendor ISA manual's. This is a small, bounded sub-task (a licensing determination, not a data
pipeline) but it belongs here because it is squarely a governance question and F3 will need the answer
before it can cite those sources.

## Deliverables & acceptance criteria

- A design doc (Law 5; see the Notes convention below — this is governance/policy work, Law-5-class
  in spirit per the task-lifecycle convention, since it establishes a new reference-class category
  under Law 4) specifying the calibration reference-class format: file location convention, required
  provenance metadata fields (device/profile identity, frequency policy, OS build, date — MODEL_DEBT
  §E5(a)), and the citation convention model coefficients use to reference a calibration file (mirror
  the existing `/- REF: ... -/` syntax's spirit — a coefficient cites its calibration file "the way
  semantics cite the SDM," per §E5's own words).
- A concrete mechanism for §E5(b): every calibration file is either generated by, or points
  unambiguously and checkably to, a specific committed harness (its file path, and ideally a content
  hash or version marker of that harness at generation time) — this is what makes the data
  *regenerable* rather than *transcribed*.
- **A demonstrated staleness-detection control** (§E5(c)): the acceptance evidence for this
  deliverable specifically is a working negative control — construct a calibration file that (i)
  predates a change to its named harness, or (ii) names a microarchitecture profile absent from the
  current build (e.g. references a profile name `Uop.lean` doesn't define), and show the gate rejects
  it; then show a genuinely fresh, correctly-provenanced calibration file passes. Per this project's
  general evidence convention for control-vector-style gates (Law 13), a mechanism that has never been
  demonstrated to actually reject a bad instance does not count as delivered.
- **A demonstrated hand-edit-rejection control** (§E5(d)): construct a calibration file identical to a
  valid one except for one hand-modified numeric value (simulating exactly the wsc failure — someone
  typing a "corrected" number directly into the file) and show the mechanism flags or rejects it.
  Like the staleness control, this must be exercised, not merely designed.
- The licensing determination for Agner Fog / uops.info (and any other external latency/throughput
  table source F3 is likely to want) — a clear written answer (vendor directly under Law 4, cite by
  reference without vendoring the full table, or exclude entirely), so F3 does not have to make this
  call mid-calibration.
- This governance mechanism must land in a state F3, F4, F5, and (eventually) MODEL_DEBT §G8 can
  actually build on — i.e. by the time F3 starts, there must be a real place to put a calibration file
  and a real gate that checks it, not just a design doc nobody wired up (the same "a gate nothing
  invokes binds nothing" lesson PLAN.md's Phase-1 reviewers repeatedly flagged for other gates).

## Pointers

- `MODEL_DEBT.md` §E5 (quoted in full above — the entire substance of this task) and the TOP-10
  priority table row 5 ("Calibrate latency/throughput/uop-count tables against a real source (A8) ...
  needs Law 4 ingestion first") and the target-class tag table's E5 row ("universal; **do first —
  wsc's actual failure mode**").
- `MODEL_DEBT.md` §A8 (uncited coefficients — SHL-by-CL and DIV spot-checks — the concrete
  coefficients F3 will calibrate once this governance mechanism exists to hold the data).
- `docs/REVIEW.md` Law 4 (External Reference Ingestion Law, quoted above), Law 6 (Reference
  Reproducibility Mandate — `references/` regeneration discipline this task's mechanism should mirror
  for calibration data specifically), Law 13 (Findings Become Gates — the control-vector convention
  this task's staleness/hand-edit demonstrations follow).
- `docs/VISION.md` §5, closing paragraph: "Each device/transport model is differentially validated
  like the CPU model (timestamp queries, bandwidth benchmarks, under the same control-vector rules);
  measured calibration data is governed like `references/` — checked in, regenerable, never
  hand-edited." This is F2's mandate stated at the vision level; F2 is the concrete mechanism that
  sentence promises exists.
- PLAN.md gaps register: "Small: calibration-source licensing check before vendoring (Agner
  Fog/uops.info redistribution vs Law 4...)" — the licensing sub-deliverable.
- `docs/adr/0006-performance-model-as-strategic-asset.md` (D5 — performance modeling is strategic;
  the end-state parametric-cost-function vision this governance mechanism ultimately serves).
- Downstream consumers to keep in mind while designing (do not implement these; just don't foreclose
  them): `docs/tasks/F3-staged-model-calibration.md` (`after: [F1, F2]`), `docs/tasks/F1-rdtsc-harness.md`
  (F1's calibration-pass constant is explicitly flagged there as needing this mechanism), and
  MODEL_DEBT §G8 (GPU/PCIe cost models, `after: G7, F2` per TASKS.md).

## Notes

- 2026-08-27: priority 8.3 — MODEL_DEBT E5: calibration-data governance is flagged 'do first' with the widest blast radius of the supplement section — every Section E model and TOP-10 item 5 depend on this policy existing before they produce numbers.

_(none yet — first entries append here as work begins; this is Law-5-class performance-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
